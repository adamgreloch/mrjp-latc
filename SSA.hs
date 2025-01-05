module SSA (toSSA) where

import AbsLatte (Ident (Ident))
import CFG
import CFGDefs
import Control.Monad (when)
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
    beenIn :: Map Label (Int, Code)
  }
  deriving (Show)

type GenM a = StateT Store (ReaderT Env IO) a

varID :: Loc -> VarID
varID (LAddr _ (Var idt src _)) = (idt, src)
varID loc = error $ "tried getting VarUId not from var: " ++ show loc

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
freshVar (Var idt src _) = do
  st <- get
  let vu = (idt, src)
  mln <- getLastNum vu
  let n' = maybe 0 (+ 1) mln
  setLastNumInBlock vu n'
  setLastNum vu n'
  return (Var idt src (Just n'))

freshNum :: Loc -> GenM Loc
freshNum (LAddr tp var) = do
  var' <- freshVar var
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

readVariable :: VarID -> GenM Expr
readVariable vi = do
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
      readVariableRec vi

addPhiOperands :: VarID -> [Label] -> Expr -> GenM Expr
addPhiOperands vi preds (EPhi num _) = do
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
              readVariable vi
          )
      debugPrint $ "addPhiOperand: " ++ printVi vi ++ " <- (L" ++ show predLab ++ ", " ++ show expr ++ ")"
      return (predLab, expr)

readVariableRec :: VarID -> GenM Expr
readVariableRec vi = do
  currLab <- asks currLabel
  debugPrint $ "readVariableRec: " ++ printVi vi
  labPreds <- getPreds currLab
  case labPreds of
    [] -> error "wait, what?"
    [lab] -> local (withLabel lab) $ readVariable vi
    preds -> do
      debugPrint $ "readVariableRec: put empty phi in " ++ printVi vi
      num <- freshVarNum vi
      let phi =  EPhi num []
      assign vi phi
      phi' <- addPhiOperands vi preds phi
      assign vi phi'
      return phi'

ephiToPhi :: PhiOperand -> (Label, Loc)
ephiToPhi (lab, ELoc loc) = (lab, loc)
ephiToPhi (lab, _) = (lab, LImmInt 0)

maybeGenPhi :: Loc -> GenM (Loc, [Instr])
maybeGenPhi loc@(LAddr _ _) = do
  e <- readVariable (varID loc)
  case e of
    ELoc loc' -> return (loc', [])
    EPhi num pops -> do
      case loc of
        (LAddr tp (Var idt src _)) ->
          do
            let loc' = LAddr tp (Var idt src (Just num))
            assign (varID loc) (ELoc loc')
            debugPrint $ "genPhi: " ++ show loc' ++ " " ++ show pops
            return (loc', [Phi loc' (map ephiToPhi pops)])
        _else -> error "can it happen?"
maybeGenPhi loc = return (loc, [])

addr :: Loc -> Addr
addr (LAddr _ addr) = addr
addr _ = error "not LAddr"

ssaInstr :: Code -> GenM Code
ssaInstr (Unar Asgn loc1@(LAddr _ (Var {})) loc2 : t) = do
  loc1' <- freshNum loc1
  debugPrint $ "ssaInstr: " ++ show loc1' ++ " <- " ++ show loc2
  if not $ isVar loc2
    then do
      assign (varID loc1') (ELoc loc2)
      ssaInstr t
      -- t' <- ssaInstr t
      -- return $ Unar Asgn loc1' loc2 : t'
    else do
      e <- readVariable (varID loc2)
      case e of
        el@(ELoc loc) -> do
          assign (varID loc1') (ELoc loc)
          ssaInstr t
          -- t' <- ssaInstr t
          -- return $ Unar Asgn loc1' loc : t'
        EPhi num pops -> do
          t' <- ssaInstr t
          return $ Phi (renumber loc1' num) (map ephiToPhi pops) : t'
ssaInstr (Bin op loc1 loc2 loc3 : t) = do
  debugPrint $ "ssaInstr: " ++ show loc1 ++ " <- " ++ show loc2 ++ " " ++ show op ++ " " ++ show loc3
  (loc2', ops2) <- maybeGenPhi loc2
  (loc3', ops3) <- maybeGenPhi loc3
  t' <- ssaInstr t
  return $ ops2 ++ ops3 ++ Bin op loc1 loc2' loc3' : t'
ssaInstr (IRet loc : t) = do
  (loc', ops) <- maybeGenPhi loc
  t' <- ssaInstr t
  return $ ops ++ IRet loc' : t'
ssaInstr (instr : t) = do
  t' <- ssaInstr t
  return (instr : t')
ssaInstr [] = return []


-- remove trivial phi
updatePhi (instr@(Phi loc []) : t) = updatePhi t
updatePhi (instr@(Phi loc pops) : t) = do
  currLab <- asks currLabel
  labPreds <- getPreds currLab
  debugPrint $ "updatePhi: " ++ show instr ++ " preds: " ++ show labPreds
  case labPreds of
    [] -> error "wait, what?"
    [lab] -> updatePhi t
    preds -> do
      t' <- updatePhi t
      return (Phi loc pops : t')
updatePhi (instr : t) = do
  t' <- updatePhi t
  return (instr : t')
updatePhi [] = return []

ssaBB :: BB' Code -> GenM (BB' Code)
ssaBB bb = do
  bi <- gets beenIn
  case M.lookup (label bb) bi of
    Just (0, stmts) -> do
      stmts' <-
        local
          (withLabel (label bb))
          ( do
              debugPrint "== ssaBB : updatePhi =="
              updatePhi stmts
          )
      modify (\st -> st {beenIn = M.insert (label bb) (1, stmts') (beenIn st)})
      return bb {stmts = reverse stmts'}
    Just (1, stmts) -> do
      debugPrint $ "done" ++ show (label bb)
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
      modify (\st -> st {beenIn = M.insert (label bb) (0, stmts') (beenIn st)})
      return bb {stmts = reverse stmts'}

ssaCFG :: CFG' Code -> GenM (CFG' Code)
ssaCFG cfg = local (\env -> env {currCfg = cfg}) $ mapM ssaBB cfg

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
          cfgs
        }
    initEnv =
      Env
        { currLabel = 0,
          currCfg = M.empty
        }
