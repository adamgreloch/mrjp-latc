module CSE (doGCSE) where

import CFG
import CFGDefs
import Control.Monad (when, (>=>))
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State
  ( MonadState (get),
    StateT,
    gets,
    modify,
    runStateT,
  )
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import FIR
import GHC.IO.Handle.FD (stderr)
import SSA (SSA (..))
import System.IO (hPutStrLn)

type SubExpr = (Loc, Op2, Loc)

data Store = Store
  { exprs :: Map SubExpr Loc,
    rename :: Map Loc Loc
  }

type CSEM a = StateT Store IO a

relOp :: (Ord a) => Op2 -> (a -> a -> Bool)
relOp op = case op of
  LTh -> (<)
  LEq -> (<=)
  GTh -> (>)
  GEq -> (>=)
  Eq -> (==)
  NEq -> (/=)
  _else -> error "not a rel op2"

foldIfConstant :: Instr -> Maybe Loc
foldIfConstant (Bin op _ (LImmInt a) (LImmInt b)) | isRel op = Just (LImmBool (relOp op a b))
foldIfConstant (Bin op _ (LImmInt a) (LImmInt b)) = Just (LImmInt (intOp a b))
  where
    intOp = case op of
      Add -> (+)
      Sub -> (-)
      Mul -> (*)
      Div -> div
      Mod -> rem
      _else -> error "not an int op2"
foldIfConstant (Bin Add _ (LString a) (LString b)) = Just (LString (a ++ b))
foldIfConstant (Bin op _ (LString a) (LString b)) | isRel op = Just (LImmBool (relOp op a b))
foldIfConstant _ = Nothing

debugPrint :: String -> CSEM ()
debugPrint s = when False $ liftIO $ hPutStrLn stderr $ "CSE: " ++ s

addRename :: Loc -> Loc -> CSEM ()
addRename from to = modify (\st -> st {rename = M.insert from to (rename st)})

addBinInstr :: Instr -> CSEM ()
addBinInstr (Bin op loc1 loc2 loc3) = do
  modify (\st -> st {exprs = M.insert (loc2, op, loc3) loc1 (exprs st)})
  when (isCommutative op) $ modify (\st -> st {exprs = M.insert (loc3, op, loc2) loc1 (exprs st)})
  where
    isCommutative Add = True
    isCommutative Mul = True
    isCommutative _ = False
addBinInstr _ = error "should only be used for binary instructions"

refresh :: Loc -> CSEM Loc
refresh loc = gets (fromMaybe loc . M.lookup loc . rename)

refreshInstr :: Instr -> CSEM Instr
refreshInstr (IRet loc) = do loc' <- refresh loc; return (IRet loc')
refreshInstr (Call loc idt locs) = do
  loc' <- refresh loc
  locs' <- mapM refresh locs
  return (Call loc' idt locs')
refreshInstr (Phi loc pops) = do
  pops' <- mapM ( \(lab, lc) -> do lc' <- refresh lc; return (lab, lc')) pops
  debugPrint $ show pops ++ " refreshed to " ++ show pops'
  return (Phi loc pops')
refreshInstr i = return i

reduceCode :: Code -> CSEM Code
reduceCode (i@(Bin CondBr loc1 loc2 loc3) : t) = do
  [loc1', loc2', loc3'] <- mapM refresh [loc1, loc2, loc3]
  let i' = Bin CondBr loc1' loc2' loc3'
  debugPrint $ show i ++ " refreshed to " ++ show i'
  t' <- reduceCode t
  return (i' : t')
reduceCode (i@(Bin op loc1 loc2 loc3) : t) = do
  st <- get
  [loc1', loc2', loc3'] <- mapM refresh [loc1, loc2, loc3]
  let i' = Bin op loc1' loc2' loc3'
  debugPrint $ show i ++ " refreshed to " ++ show i'
  case foldIfConstant i' of
    Just foldedLoc -> do
      debugPrint $ show i' ++ " folded to " ++ show foldedLoc
      addRename loc1' foldedLoc
      reduceCode t
    Nothing -> do
      case M.lookup (loc2', op, loc3') (exprs st) of
        Just loc' -> do
          debugPrint $ show i' ++ " same as " ++ show loc'
          addRename loc1' loc'
          reduceCode t
        Nothing -> do
          debugPrint $ show i' ++ " nothing like it"
          addBinInstr i'
          t' <- reduceCode t
          return (i' : t')
reduceCode (i : t) = do
  i' <- refreshInstr i
  t' <- reduceCode t
  return (i' : t')
reduceCode [] = return []

doBB :: BB' Code -> CSEM (BB' Code)
doBB bb = do
  stmts' <- reduceCode (stmts bb)
  return bb {stmts = stmts'}

refreshBB :: BB' Code -> CSEM (BB' Code)
refreshBB bb = do
  stmts' <- mapM refreshInstr (stmts bb)
  return bb {stmts = stmts'}

doCFG :: CFG' Code -> IO (CFG' Code)
doCFG cfg = do
  (cfg', _) <- runStateT m initStore
  return cfg'
  where
    m = (mapM doBB >=> mapM refreshBB) cfg
    initStore =
      Store
        { exprs = M.empty,
          rename = M.empty
        }

doCFGs :: CFGsNoDefs' Code -> IO (CFGsNoDefs' Code)
doCFGs = mapM doCFG

doGCSE :: SSA -> IO SSA
doGCSE s@(SSA (cfgs, info)) =
  if elem CSE $ opts info
    then do
      cfgs' <- doCFGs cfgs
      return $ SSA (cfgs', info)
    else return s
