{-# LANGUAGE ImportQualifiedPost #-}

module CSE (doGCSE) where

import CFG
import CFGDefs
import Control.Monad (foldM, when, (>=>))
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
    modify,
    runStateT,
  )
import Data.List (sort)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Set (Set)
import Data.Set qualified as S
import FIR
import GHC.IO.Handle.FD (stderr)
import SSA (SSA (..))
import System.IO (hPutStrLn)

type SubExpr = (Loc, Op2, Loc)

data Store = Store
  { localExprs :: Map SubExpr Loc,
    rename :: Map Loc Loc,
    exprs :: Map Label (Map SubExpr Loc),
    visited :: Set Label,
    toDelete :: Map Loc Label,
    refreshes :: Int
  }

newtype Env = Env
  { currLabel :: Label
  }

type CSEM a = StateT Store (ReaderT Env IO) a

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
debugPrint s = when True $ liftIO $ hPutStrLn stderr $ "CSE: " ++ s

addRename :: Loc -> Loc -> CSEM ()
addRename from to = do
  debugPrint $ show from ++ " -> " ++ show to
  modify (\st -> st {rename = M.insert from to (rename st)})

addBinInstr :: Instr -> CSEM ()
addBinInstr (Bin op loc1 loc2 loc3) = modify (\st -> st {localExprs = M.insert (loc2, op, loc3) loc1 (localExprs st)})
addBinInstr _ = error "should only be used for binary instructions"

refresh :: Loc -> CSEM Loc
refresh loc = do
  st <- get
  case M.lookup loc (rename st) of
    Nothing -> return loc
    Just loc' -> do
      put (st {refreshes = refreshes st + 1})
      return loc'

refreshInstr :: Instr -> CSEM Instr
refreshInstr (Bin op loc1 loc2 loc3) = do
  [loc1', loc2', loc3'] <- mapM refresh [loc1, loc2, loc3]
  return $ Bin op loc1' loc2' loc3'
refreshInstr (IRet loc) = do loc' <- refresh loc; return (IRet loc')
refreshInstr (Call loc idt locs) = do
  loc' <- refresh loc
  locs' <- mapM refresh locs
  return (Call loc' idt locs')
refreshInstr (Phi loc pops) = do
  st <- get
  pops' <- mapM (\(lab, lc) -> do lc' <- refresh lc; return (lab, lc')) pops
  debugPrint $ show pops ++ " refreshed to " ++ show pops' ++ "\n" ++ show (rename st)
  return (Phi loc pops')
refreshInstr i = return i

uniqueLocs :: [(Label, Loc)] -> [(Label, Loc)]
uniqueLocs l = f Nothing (sort l)
  where
    f :: Maybe Loc -> [(Label, Loc)] -> [(Label, Loc)]
    f _ [] = []
    f e ((_, loc) : t) | e == Just loc = f e t
    f _ ((lab, loc) : t) = (lab, loc) : f (Just loc) t

isToDelete :: Loc -> CSEM Bool
isToDelete loc = do
  currLab <- asks currLabel
  st <- get
  case M.lookup loc (toDelete st) of
    Just lab -> return $ lab /= currLab
    Nothing -> return False

refreshCode :: Code -> CSEM Code
refreshCode (i@(Bin op loc1 _ _) : t) | op /= CondBr = do
  currLab <- asks currLabel
  debugPrint $ show currLab ++ " : should remove " ++ show i ++ "? "
  loc1' <- refresh loc1
  td <- isToDelete loc1'
  if td
    then do
      debugPrint "yes"
      refreshCode t
    else do
      debugPrint "no"
      i' <- refreshInstr i
      t' <- refreshCode t
      return (i' : t')
refreshCode (i@(Phi loc pops) : t) = do
  pops' <- mapM (\(lab, lc) -> do lc' <- refresh lc; return (lab, lc')) pops

  let pops'' = uniqueLocs $ filter (\(_, lc) -> lc /= loc) pops'
  case pops'' of
    [(_, loc1)] -> do
      addRename loc loc1
      debugPrint $ "renamed trivial " ++ show i ++ " to " ++ show loc1
      refreshCode t
    _else -> do
      st <- get
      debugPrint $ show i ++ " refreshed to " ++ show (Phi loc pops') ++ "\n" ++ show (rename st)
      t' <- refreshCode t
      return (Phi loc pops' : t')
refreshCode (i : t) = do
  i' <- refreshInstr i
  t' <- refreshCode t
  return (i' : t')
refreshCode [] = return []

lookupSubExpr :: SubExpr -> Map SubExpr Loc -> Maybe Loc
lookupSubExpr (loc1, op, loc2) le =
  case M.lookup (loc1, op, loc2) le of
    Nothing -> M.lookup (loc2, op, loc1) le
    Just l -> Just l

reduceCode :: Code -> CSEM Code
reduceCode (i@(Bin op loc1 loc2 loc3) : t) | op /= CondBr = do
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
      case lookupSubExpr (loc2', op, loc3') (localExprs st) of
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

refreshBB :: BB' Code -> CSEM (BB' Code)
refreshBB bb = do
  stmts' <- local (withLabel (label bb)) $ refreshCode (stmts bb)
  return bb {stmts = stmts'}

withLabel :: Label -> Env -> Env
withLabel lab env = env {currLabel = lab}

walkDown :: (BB' Code -> CSEM (BB' Code)) -> CFG' Code -> CSEM (CFG' Code)
walkDown m cfg = do
  modify (\st -> st {visited = S.empty})
  f (startBB cfg) cfg
  where
    f :: BB' Code -> CFG' Code -> CSEM (CFG' Code)
    f bb cfg_ = do
      debugPrint $ "WALK " ++ show (label bb)
      bb' <- m bb
      let cfg' = insertBB bb' cfg_
      let succBB = getSuccsAsBB bb' cfg'

      pst <- get

      foldM
        ( \acc v -> do
            st <- get
            if S.member (label v) (visited st)
              then return acc
              else do
                put
                  ( st
                      { localExprs = localExprs pst,
                        visited = S.insert (label v) (visited st)
                      }
                  )
                debugPrint $ "WALK " ++ show (label v)
                f v acc
        )
        cfg'
        succBB

walkCFG :: BB' Code -> CFG' Code -> CSEM (CFG' Code)
walkCFG bb cfg = do
  local
    (withLabel (label bb))
    ( do
        debugPrint $ show (label bb) ++ " reduce"
        stmts' <- reduceCode (stmts bb)
        modify (\st -> st {exprs = M.insert (label bb) (localExprs st) (exprs st)})
        pst <- get
        debugPrint $ show (label bb) ++ " local exprs : " ++ show (localExprs pst)
        cfg' <-
          foldM
            ( \acc v -> do
                st <- get
                if S.member (label v) (visited st)
                  then return acc
                  else do
                    put
                      ( st
                          { localExprs = localExprs pst,
                            visited = S.insert (label v) (visited st)
                          }
                      )
                    walkCFG v acc
            )
            cfg
            (map (`lookupBB` cfg) succLabs)
        pst' <- get
        let getLabExprs lab = fromJust $ M.lookup lab (exprs pst')

        mapM_ (\l -> debugPrint $ show l ++ " succ : " ++ show (getLabExprs l)) succLabs
        s <- case succLabs of
          [_] -> return []
          h : t -> do
            let inter = foldr (M.intersection . getLabExprs) (getLabExprs h) t
            let commonInSuccs = M.difference inter (getLabExprs (label bb))
            foldM f [] (M.toList commonInSuccs)
          _else -> return []

        debugPrint $ show s

        return $ insertBB (bb {stmts = init stmts' ++ s ++ [last stmts']}) cfg'
    )
  where
    succLabs = getSuccs bb

    markAsToDelete :: (Loc, Label) -> CSEM ()
    markAsToDelete (loc, ll) = modify (\st -> st {toDelete = M.insert loc ll (toDelete st)})

    f :: Code -> (SubExpr, Loc) -> CSEM Code
    f acc ((loc2, op, loc3), loc1) = do
      pst' <- get
      let getLabExprs lab = fromJust $ M.lookup lab (exprs pst')
      let commonLocs = map (fromJust . M.lookup (loc2, op, loc3) . getLabExprs) succLabs
      let locsToLoc1 = filter (/= loc1) commonLocs

      currLab <- asks currLabel

      markAsToDelete (loc1, currLab)

      mapM_ (`addRename` loc1) locsToLoc1
      debugPrint $ show locsToLoc1
      return (Bin op loc1 loc2 loc3 : acc)

refreshCFGUntilStable :: CFG' Code -> CSEM (CFG' Code)
refreshCFGUntilStable cfg = do
  st0 <- get
  let s0 = M.size (rename st0)
  cfg' <- walkDown refreshBB cfg
  st1 <- get
  let s1 = M.size (rename st1)
  if s1 > s0
    then do
      refreshCFGUntilStable cfg'
    else return cfg'

doCFG :: CFG' Code -> IO (CFG' Code)
doCFG cfg = do
  (cfg', st) <- runReaderT (runStateT m initStore) initEnv
  if refreshes st == 0
    then return cfg'
    else do
      doCFG cfg'
  where
    m = (walkCFG (startBB cfg) >=> refreshCFGUntilStable) cfg
    initStore =
      Store
        { localExprs = M.empty,
          rename = M.empty,
          exprs = M.empty,
          visited = S.empty,
          toDelete = M.empty,
          refreshes = 0
        }
    initEnv =
      Env {currLabel = Entry}

doCFGs :: CFGsNoDefs' Code -> IO (CFGsNoDefs' Code)
doCFGs = mapM doCFG

doGCSE :: SSA -> IO SSA
doGCSE s@(SSA (cfgs, info)) =
  if elem CSE $ opts info
    then do
      cfgs' <- doCFGs cfgs
      return $ SSA (cfgs', info)
    else return s
