module SSA (toSSA, SSA (..)) where

import AbsLatte (Ident (Ident))
import CFG
import CFGDefs
import Control.Monad (foldM, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader
  ( MonadReader (local),
    ReaderT,
    asks,
    runReaderT,
  )
import Control.Monad.State
  ( MonadState (get, put),
    StateT,
    gets,
    modify,
    runStateT,
  )
import Data.List (sort)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import FIR
import GHC.IO.Handle.FD (stderr)
import System.IO (hPutStrLn)

type PhiOperand = (Label, Expr)

data Expr
  = ELoc Loc
  | EPhi Loc [PhiOperand]
  deriving (Show)

data Env = Env
  { currLabel :: Label,
    currCfg :: CFG' Code
  }
  deriving (Show)

type VarID = (Ident, Int)

printVi :: VarID -> String
printVi (Ident s, src) = "%" ++ s ++ "_" ++ show src

data Store = Store
  { currDef :: Map VarID (Map Label Expr),
    lastDefNumInBlock :: Map VarID (Map Label Int),
    lastDefNum :: Map VarID Int,
    cfgs :: CFGsNoDefs' Code,
    beenIn :: Map Label Code,
    phis :: Map Label (Map VarID (Loc, Map Label Expr))
  }
  deriving (Show)

type SSAM a = StateT Store (ReaderT Env IO) a

initPhi :: VType -> VarID -> Int -> SSAM ()
initPhi tp vi@(idt, src) num = do
  st <- get
  currLab <- asks currLabel
  let mp = M.findWithDefault M.empty currLab (phis st)
  let mp' = M.insert vi (LAddr tp (Var idt src (Just num)), M.empty) mp
  let phis' = M.insert currLab mp' (phis st)
  put (st {phis = phis'})

-- TODO clean this up some day
writeToPhis :: VarID -> Label -> Expr -> SSAM ()
writeToPhis vi predLab e = do
  st <- get
  currLab <- asks currLabel
  let mp = M.findWithDefault M.empty currLab (phis st)
  case M.lookup vi mp of
    Nothing -> error "phi not inited"
    Just (num, mp') -> do
      let mp'' = M.insert predLab e mp'
      let phis' = M.insert currLab (M.insert vi (num, mp'') mp) (phis st)
      put (st {phis = phis'})

addrToVarID :: Addr -> VarID
addrToVarID (Var idt src _) = (idt, src)
addrToVarID (ArgVar idt) = (idt, 0)
-- TODO make addr a different type than temp?
addrToVarID _ = error "expected var or argvar"

locToVarID :: Loc -> VarID
locToVarID (LAddr _ addr) = addrToVarID addr
locToVarID loc = error $ "tried getting VarUId not from var: " ++ show loc

debugPrint :: String -> SSAM ()
debugPrint s = do
  currLab <- asks currLabel
  when True $ liftIO $ hPutStrLn stderr $ "SSA: " ++ "(" ++ show currLab ++ ") " ++ s

getLastNum :: VarID -> SSAM (Maybe Int)
getLastNum vu = gets (M.lookup vu . lastDefNum)

setLastNumInBlock :: VarID -> Int -> SSAM ()
setLastNumInBlock vi num = do
  debugPrint $ "setLastNumInBlock: " ++ printVi vi ++ " <- " ++ show num
  st <- get
  currLab <- asks currLabel
  let mp = M.insert currLab num $ M.findWithDefault M.empty vi (lastDefNumInBlock st)
  put (st {lastDefNumInBlock = M.insert vi mp (lastDefNumInBlock st)})

setLastNum :: VarID -> Int -> SSAM ()
setLastNum vu num = modify (\st -> st {lastDefNum = M.insert vu num (lastDefNum st)})

freshVarNum :: VarID -> SSAM Int
freshVarNum vi = do
  mln <- getLastNum vi
  let n = maybe 0 (+ 1) mln
  setLastNumInBlock vi n
  setLastNum vi n
  debugPrint $ "freshVarNum: " ++ printVi vi ++ " -> " ++ show n
  return n

freshVar :: Addr -> SSAM Addr
freshVar addr = do
  let vi@(idt, src) = addrToVarID addr
  mln <- getLastNum vi
  let n' = maybe 0 (+ 1) mln
  setLastNumInBlock vi n'
  setLastNum vi n'
  return (Var idt src (Just n'))

freshNum :: Loc -> SSAM Loc
freshNum (LAddr tp var) = do
  var' <- freshVar var
  debugPrint $ "freshNum: " ++ show var ++ " -> " ++ show var'
  return (LAddr tp var')
freshNum _ = error "expected addr"

assign :: VarID -> Expr -> SSAM ()
assign vi expr = do
  debugPrint $ "assign: " ++ printVi vi ++ " <- " ++ show expr
  currLab <- asks currLabel
  st <- get
  let mp =
        M.insert currLab expr $
          M.findWithDefault M.empty vi (currDef st)
  let currDef' = M.insert vi mp (currDef st)
  put (st {currDef = currDef'})

getPreds :: Label -> SSAM [Label]
getPreds lab = do
  cfg <- asks currCfg
  case M.lookup lab cfg of
    Just bb -> return $ justBlocks $ preds bb
    Nothing -> error $ "no bb with this label " ++ show lab
  where
    justBlocks :: [Node] -> [Label]
    justBlocks (FnBlock lab1 : t) = lab1 : justBlocks t
    justBlocks (_ : t) = justBlocks t
    justBlocks [] = []

withLabel :: Label -> Env -> Env
withLabel lab env = env {currLabel = lab}

lookupCurrDef :: VarID -> Label -> SSAM (Maybe Expr)
lookupCurrDef vi lab = do
  st <- get
  case M.lookup vi (currDef st) of
    Nothing -> do
      debugPrint $ "looked for " ++ printVi vi ++ "got nothing"
      return Nothing
    Just mp -> do
      debugPrint $ "looked for " ++ printVi vi ++ " got:\n\t" ++ show mp
      return $ M.lookup lab mp

isVar :: Loc -> Bool
isVar (LAddr _ (Var {})) = True
isVar _ = False

readVariable :: VType -> VarID -> SSAM Expr
readVariable tp vi = do
  debugPrint $ "readVariable: " ++ printVi vi
  currLab <- asks currLabel
  cd <- lookupCurrDef vi currLab
  case cd of
    Just e -> do
      debugPrint $ "looked up " ++ show e
      return e
    Nothing -> do
      debugPrint "looked up nothing"
      readVariableRec tp vi

addPhiOperands :: VType -> VarID -> [Label] -> Expr -> SSAM Expr
addPhiOperands tp vi preds (EPhi num _) = do
  pop <- mapM addPhiOperand (sort preds)
  return (EPhi num pop)
  where
    addPhiOperand :: Label -> SSAM PhiOperand
    addPhiOperand predLab = do
      expr <-
        local
          (withLabel predLab)
          ( do
              cfg <- asks currCfg
              let bb = fromMaybe (error "aa") $ M.lookup predLab cfg
              _ <- ssaBB bb
              readVariable tp vi
          )
      writeToPhis vi predLab expr
      debugPrint $ "addPhiOperand: " ++ printVi vi ++ " <- (L" ++ show predLab ++ ", " ++ show expr ++ ")"
      return (predLab, expr)
addPhiOperands _ _ _ (ELoc _) = error "expected EPhi"

readVariableRec :: VType -> VarID -> SSAM Expr
readVariableRec tp vi@(idt, src) = do
  currLab <- asks currLabel
  debugPrint $ "readVariableRec: " ++ printVi vi
  labPreds <- getPreds currLab
  case labPreds of
    [] -> error "wait, what?"
    [lab] -> do
      cfg <- asks currCfg
      let bb = fromMaybe (error "aa") $ M.lookup lab cfg
      _ <- ssaBB bb
      local (withLabel lab) $ readVariable tp vi
    preds -> do
      debugPrint $ "readVariableRec: put empty phi in " ++ printVi vi
      num <- freshVarNum vi
      let loc = LAddr tp (Var idt src (Just num))
      let phi = EPhi loc []
      initPhi tp vi num
      assign vi phi
      phi' <- addPhiOperands tp vi preds phi
      assign vi phi'
      return phi'

ephiToPhi :: PhiOperand -> (Label, Loc)
ephiToPhi (lab, ELoc loc) = (lab, loc)
ephiToPhi (lab, EPhi loc _) = (lab, loc)

maybeGenPhi :: Loc -> SSAM Loc
maybeGenPhi loc@(LAddr tp addr) =
  case addr of
    (ArgVar _) -> do
      currLab <- asks currLabel
      cd <- lookupCurrDef (addrToVarID addr) currLab
      case cd of
        Nothing -> do
          loc' <- freshNum loc
          assign (locToVarID loc') (ELoc loc')
          return loc'
        Just e -> exprToRet e
    (Var {}) -> do
      do
        e <- readVariable tp (locToVarID loc)
        exprToRet e
    _else -> return loc
  where
    exprToRet :: Expr -> SSAM Loc
    exprToRet e = case e of
      ELoc loc' -> return loc'
      EPhi loc' pops -> do
        assign (locToVarID loc) (ELoc loc')
        debugPrint $ "genPhi: " ++ show loc' ++ " " ++ show pops
        return loc'
maybeGenPhi loc = return loc

ssaCode :: Code -> SSAM Code
ssaCode (Unar Asgn loc1@(LAddr _ _) loc2 : t) = do
  loc1' <- freshNum loc1
  debugPrint $ "ssaInstr: " ++ show loc1' ++ " <- " ++ show loc2
  if not $ isVar loc2
    then do
      assign (locToVarID loc1') (ELoc loc2)
      ssaCode t
    else do
      e <- readVariable (typeOfLoc loc2) (locToVarID loc2)
      case e of
        (ELoc loc) -> do
          assign (locToVarID loc1') (ELoc loc)
          ssaCode t
        _ephi -> ssaCode t
ssaCode (Bin op loc1 loc2 loc3 : t) = do
  debugPrint $ "ssaInstr: " ++ show loc1 ++ " <- " ++ show loc2 ++ " " ++ show op ++ " " ++ show loc3
  loc1' <- maybeGenPhi loc1
  loc2' <- maybeGenPhi loc2
  loc3' <- maybeGenPhi loc3
  t' <- ssaCode t
  return $ Bin op loc1' loc2' loc3' : t'
ssaCode (Call loc1 idt locs : t) = do
  locs' <- mapM maybeGenPhi locs
  t' <- ssaCode t
  return $ Call loc1 idt locs' : t'
ssaCode (IRet loc : t) = do
  debugPrint $ "IRet: " ++ show loc
  loc' <- maybeGenPhi loc
  t' <- ssaCode t
  return $ IRet loc' : t'
ssaCode (instr : t) = do
  t' <- ssaCode t
  return (instr : t')
ssaCode [] = return []

ssaBB :: BB' Code -> SSAM (BB' Code)
ssaBB bb = do
  bi <- gets beenIn
  case M.lookup (label bb) bi of
    Just stmts -> do
      debugPrint "== ssaBB : just ret =="
      p <- gets phis
      debugPrint $ "done L" ++ show (label bb) ++ " phis:\n\t" ++ show p
      return bb {stmts = reverse stmts}
    Nothing -> do
      stmts' <-
        local
          (withLabel (label bb))
          ( do
              debugPrint "== ssaBB : ssaInstr =="
              ssaCode (reverse $ stmts bb)
          )
      debugPrint $ "beenIn" ++ show (label bb)
      modify (\st -> st {beenIn = M.insert (label bb) stmts' (beenIn st)})
      return bb {stmts = reverse stmts'}

-- TODO remove trivial phis like Phi %a_1_4 [(L8, %a_1_3), (L10, %a_1_3)]
-- propagate assignment in case of one pop? maybe leave it to copy propagation?
nonTrivialPhiOrNop :: Loc -> [(Label, Loc)] -> [Instr]
nonTrivialPhiOrNop phiLoc pops =
  case filter isNotSame pops of
    [] -> []
    pops' -> [Phi phiLoc pops']
  where
    isNotSame (_,_) = True
    -- isNotSame :: (Label, Loc) -> Bool
    -- isNotSame (_, loc) = loc /= phiLoc

emitPhi :: BB' Code -> SSAM (BB' Code)
emitPhi bb = do
  debugPrint $ "emitPhi " ++ show bb
  st <- get
  let mp = fromMaybe (error "impossible") $ M.lookup (label bb) (phis st)
  foldM
    ( \acc vi -> do
        let (loc, popMap) = fromMaybe (error "impossible") $ M.lookup vi mp
        let op = nonTrivialPhiOrNop loc $ map ephiToPhi (M.toList popMap)
        -- TODO awful, but optimal reversing is a todo
        return $ acc {stmts = stmts acc ++ op}
    )
    bb
    (M.keys mp)

emitPhis :: CFG' Code -> SSAM (CFG' Code)
emitPhis cfg = do
  st <- get
  debugPrint $ "emitPhis: " ++ show cfg
  let bbs =
        map
          ( \lab ->
              fromMaybe (error $ "no bb for lab?: " ++ show lab) $ M.lookup lab cfg
          )
          $ M.keys (phis st)
  foldM
    ( \acc bb -> do
        bb' <- emitPhi bb
        return $ M.insert (label bb) bb' acc
    )
    cfg
    bbs

ssaCFG :: CFG' Code -> SSAM (CFG' Code)
ssaCFG cfg = do
  local
    (\env -> env {currCfg = cfg})
    ( do
        res <- mapM ssaBB cfg >>= emitPhis
        modify (\st -> st {phis = M.empty})
        return res
    )

ssaCFGs :: CFGsNoDefs' Code -> SSAM (CFGsNoDefs' Code)
ssaCFGs = mapM ssaCFG

newtype SSA = SSA (CFGs' Code)

toSSA :: CFGs' Code -> IO SSA
toSSA (cfgs, info) = do
  (cfgs', _) <- runReaderT (runStateT m initStore) initEnv
  return $ SSA (cfgs', info)
  where
    m = ssaCFGs cfgs
    initStore =
      Store
        { currDef = M.empty,
          lastDefNumInBlock = M.empty,
          lastDefNum = M.empty,
          beenIn = M.empty,
          phis = M.empty,
          cfgs
        }
    initEnv =
      Env
        { currLabel = BlockLabel 0,
          currCfg = M.empty
        }
