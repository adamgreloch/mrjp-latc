module SSA (toSSA) where

import AbsLatte (Ident (Ident))
import CFG
import CFGDefs
import Control.Monad (foldM, foldM_, unless, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader
  ( MonadReader (ask, local),
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
import TransformAbsToFIR

type PhiOperand = (Label, Expr)

data Expr
  = ELoc Loc
  | EPhi Int [PhiOperand]
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

type GenM a = StateT Store (ReaderT Env IO) a

initPhi :: VType -> VarID -> Int -> GenM ()
initPhi tp vi@(idt, src) num = do
  st <- get
  currLab <- asks currLabel
  let map = M.findWithDefault M.empty currLab (phis st)
  let map' = M.insert vi (LAddr tp (Var idt src (Just num)), M.empty) map
  let phis' = M.insert currLab map' (phis st)
  put (st {phis = phis'})

-- TODO clean this up some day
writeToPhis :: VarID -> Label -> Expr -> GenM ()
writeToPhis vi predLab e = do
  st <- get
  currLab <- asks currLabel
  let map = M.findWithDefault M.empty currLab (phis st)
  case M.lookup vi map of
    Nothing -> error "phi not inited"
    Just (num, map') -> do
      let map'' = M.insert predLab e map'
      let phis' = M.insert currLab (M.insert vi (num, map'') map) (phis st)
      put (st {phis = phis'})

readPhis :: Label -> VarID -> GenM (Maybe Expr)
readPhis predLab vi = do
  st <- get
  currLab <- asks currLabel
  case M.lookup currLab (phis st) of
    Nothing -> return Nothing
    Just map -> case M.lookup vi map of
      Nothing -> return Nothing
      Just (_, map') -> return $ M.lookup predLab map'

addrToVarID :: Addr -> VarID
addrToVarID (Var idt src _) = (idt, src)
addrToVarID (ArgVar idt) = (idt, 0)

locToVarID :: Loc -> VarID
locToVarID (LAddr _ addr) = addrToVarID addr
locToVarID loc = error $ "tried getting VarUId not from var: " ++ show loc

debugPrint :: String -> GenM ()
debugPrint s = do
  currLab <- asks currLabel
  when True $ liftIO $ hPutStrLn stderr $ "SSA: " ++ "(L" ++ show currLab ++ ") " ++ s

getLastNumInBlock :: VarID -> GenM (Maybe Int)
getLastNumInBlock vu = do
  st <- get
  currLab <- asks currLabel
  case M.lookup vu (lastDefNumInBlock st) of
    Nothing -> return Nothing
    Just map -> return $ M.lookup currLab map

getLastNum :: VarID -> GenM (Maybe Int)
getLastNum vu = do
  st <- get
  currLab <- asks currLabel
  return $ M.lookup vu (lastDefNum st)

setLastNumInBlock :: VarID -> Int -> GenM ()
setLastNumInBlock vi num = do
  debugPrint $ "setLastNumInBlock: " ++ printVi vi ++ " <- " ++ show num
  st <- get
  currLab <- asks currLabel
  let map = M.insert currLab num $ M.findWithDefault M.empty vi (lastDefNumInBlock st)
  put (st {lastDefNumInBlock = M.insert vi map (lastDefNumInBlock st)})

setLastNum :: VarID -> Int -> GenM ()
setLastNum vu num = modify (\st -> st {lastDefNum = M.insert vu num (lastDefNum st)})

freshVarNum :: VarID -> GenM Int
freshVarNum vi = do
  st <- get
  mln <- getLastNum vi
  let n = maybe 0 (+ 1) mln
  setLastNumInBlock vi n
  setLastNum vi n
  debugPrint $ "freshVarNum: " ++ printVi vi ++ " -> " ++ show n
  return n

freshVar :: Addr -> GenM Addr
freshVar addr = do
  st <- get
  let vi@(idt, src) = addrToVarID addr
  mln <- getLastNum vi
  let n' = maybe 0 (+ 1) mln
  setLastNumInBlock vi n'
  setLastNum vi n'
  return (Var idt src (Just n'))

freshNum :: Loc -> GenM Loc
freshNum (LAddr tp var) = do
  var' <- freshVar var
  debugPrint $ "freshNum: " ++ show var ++ " -> " ++ show var'
  return (LAddr tp var')

freshNumIfUnnumbered :: Loc -> GenM Loc
freshNumIfUnnumbered loc@(LAddr _ (Var _ _ Nothing)) = freshNum loc
freshNumIfUnnumbered loc@(LAddr _ (Var _ _ (Just _))) = return loc

assign :: VarID -> Expr -> GenM ()
assign vi expr = do
  debugPrint $ "assign: " ++ printVi vi ++ " <- " ++ show expr
  currLab <- asks currLabel
  st <- get
  let map =
        M.insert currLab expr $
          M.findWithDefault M.empty vi (currDef st)
  let currDef' = M.insert vi map (currDef st)
  put (st {currDef = currDef'})

getPreds :: Label -> GenM [Label]
getPreds lab = do
  cfg <- asks currCfg
  st <- get
  case M.lookup lab cfg of
    Just bb -> return $ justBlocks $ preds bb
    Nothing -> error $ "no bb with this label " ++ show lab
  where
    justBlocks :: [Node] -> [Label]
    justBlocks (FnBlock lab : t) = lab : justBlocks t
    justBlocks (_ : t) = justBlocks t
    justBlocks [] = []

withLabel :: Label -> Env -> Env
withLabel lab env = env {currLabel = lab}

lookupCurrDef :: VarID -> Label -> GenM (Maybe Expr)
lookupCurrDef vi@(idt, src) lab = do
  st <- get
  case M.lookup vi (currDef st) of
    Nothing -> do
      debugPrint $ "looked for " ++ printVi vi ++ "got nothing"
      return Nothing
    Just map -> do
      debugPrint $ "looked for " ++ printVi vi ++ " got:\n\t" ++ show map
      return $ M.lookup lab map

isVar :: Loc -> Bool
isVar (LAddr _ (Var {})) = True
isVar _ = False

isUnnumbered :: Loc -> Bool
isUnnumbered (LAddr _ (Var _ _ Nothing)) = True
isUnnumbered _ = False

renumber :: Loc -> Int -> Loc
renumber (LAddr tp (Var idt src _)) num = LAddr tp (Var idt src (Just num))

readVariable :: VType -> VarID -> GenM Expr
readVariable tp vi@(_, src) = do
  debugPrint $ "readVariable: " ++ printVi vi
  currLab <- asks currLabel
  st <- get
  cd <- lookupCurrDef vi currLab
  case cd of
    Just e -> do
      debugPrint $ "looked up " ++ show e
      return e
    Nothing -> do
      debugPrint "looked up nothing"
      readVariableRec tp vi

addPhiOperands :: VType -> VarID -> [Label] -> Expr -> GenM Expr
addPhiOperands tp vi preds (EPhi num _) = do
  pop <- mapM addPhiOperand (sort preds)
  return (EPhi num pop)
  where
    addPhiOperand :: Label -> GenM PhiOperand
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

readVariableRec :: VType -> VarID -> GenM Expr
readVariableRec tp vi = do
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
      let phi = EPhi num []
      initPhi tp vi num
      assign vi phi
      phi' <- addPhiOperands tp vi preds phi
      assign vi phi'
      return phi'

ephiToPhi :: PhiOperand -> (Label, Loc)
ephiToPhi (lab, ELoc loc) = (lab, loc)
ephiToPhi (lab, _) = error "not eloc"

isArgOrArgVar :: Addr -> Bool
isArgOrArgVar (ArgVar {}) = True
isArgOrArgVar (Var {}) = True
isArgOrArgVar _ = False

maybeGenPhi :: Loc -> GenM (Loc, [Instr])
maybeGenPhi loc@(LAddr tp addr) =
  case addr of
    (ArgVar idt) -> do
      currLab <- asks currLabel
      cd <- lookupCurrDef (addrToVarID addr) currLab
      case cd of
        Nothing -> do
          loc' <- freshNum loc
          assign (locToVarID loc') (ELoc loc')
          return (loc', [])
        Just e -> exprToRet e
    (Var {}) -> do
      do
        e <- readVariable tp (locToVarID loc)
        exprToRet e
    _else -> return (loc, [])
  where
    vi@(idt, src) = addrToVarID addr

    exprToRet :: Expr -> GenM (Loc, [Instr])
    exprToRet e = case e of
      ELoc loc' -> return (loc', [])
      EPhi num pops -> do
        let loc' = LAddr tp (Var idt src (Just num))
        assign (locToVarID loc) (ELoc loc')
        debugPrint $ "genPhi: " ++ show loc' ++ " " ++ show pops
        return (loc', [Phi loc' (map ephiToPhi pops)])
maybeGenPhi loc = return (loc, [])

addr :: Loc -> Addr
addr (LAddr _ addr) = addr
addr _ = error "not LAddr"

ssaInstr :: Code -> GenM Code
ssaInstr (Unar Asgn loc1@(LAddr _ _) loc2 : t) = do
  loc1' <- freshNum loc1
  debugPrint $ "ssaInstr: " ++ show loc1' ++ " <- " ++ show loc2
  if not $ isVar loc2
    then do
      assign (locToVarID loc1') (ELoc loc2)
      ssaInstr t
    else do
      e <- readVariable (typeOfLoc loc2) (locToVarID loc2)
      case e of
        el@(ELoc loc) -> do
          assign (locToVarID loc1') (ELoc loc)
          ssaInstr t
        _ephi -> ssaInstr t
ssaInstr (Bin op loc1 loc2 loc3 : t) = do
  debugPrint $ "ssaInstr: " ++ show loc1 ++ " <- " ++ show loc2 ++ " " ++ show op ++ " " ++ show loc3
  (loc2', ops2) <- maybeGenPhi loc2
  (loc3', ops3) <- maybeGenPhi loc3
  t' <- ssaInstr t
  return $ Bin op loc1 loc2' loc3' : t'
ssaInstr (IRet loc : t) = do
  debugPrint $ "IRet: " ++ show loc
  (loc', ops) <- maybeGenPhi loc
  t' <- ssaInstr t
  return $ IRet loc' : t'
ssaInstr (instr : t) = do
  t' <- ssaInstr t
  return (instr : t')
ssaInstr [] = return []

ssaBB :: BB' Code -> GenM (BB' Code)
ssaBB bb = do
  bi <- gets beenIn
  case M.lookup (label bb) bi of
    Just  stmts -> do
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
              ssaInstr (reverse $ stmts bb)
          )
      debugPrint $ "beenIn" ++ show (label bb)
      modify (\st -> st {beenIn = M.insert (label bb) stmts' (beenIn st)})
      return bb {stmts = reverse stmts'}

emitPhi :: BB' Code -> GenM (BB' Code)
emitPhi bb = do
  debugPrint $ "emitPhi " ++ show bb
  st <- get
  let mp = fromMaybe (error "impossible") $ M.lookup (label bb) (phis st)
  foldM
    ( \acc vi@(idt, src) -> do
        let (loc, popMap) = fromMaybe (error "impossible") $ M.lookup vi mp
        let pops = map ephiToPhi (M.toList popMap)
        -- TODO awful, but optimal reversing is a todo
        return $ acc {stmts = stmts acc ++ [Phi loc pops]}
    )
    bb
    (M.keys mp)

emitPhis :: CFG' Code -> GenM (CFG' Code)
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

ssaCFG :: CFG' Code -> GenM (CFG' Code)
ssaCFG cfg = do
  local
    (\env -> env {currCfg = cfg})
    ( do
        res <- mapM ssaBB cfg >>= emitPhis
        modify (\st -> st {phis = M.empty})
        return res
    )

ssaCFGs :: CFGsNoDefs' Code -> GenM (CFGsNoDefs' Code)
ssaCFGs = mapM ssaCFG

toSSA :: CFGs' Code -> IO (CFGs' Code)
toSSA (cfgs, info) = do
  (cfgs', _) <- runReaderT (runStateT m initStore) initEnv
  return (cfgs', info)
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
        { currLabel = 0,
          currCfg = M.empty
        }
