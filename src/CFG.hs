{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE StrictData #-}

module CFG
  ( genCFGs,
    Label,
    CFG,
    CFGs,
    CFGs',
    BB' (BB', label, stmts, preds, succs),
  )
where

import AbsLatte
import CFGDefs
import Common
import Control.Exception (assert)
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
import Data.List (find)
import Data.Map qualified as M
import GHC.IO.Handle.FD (stderr)
import System.IO (hPutStrLn)
import TypeCheckLatte (TypeCheckInfo (..))

type BB = BB' [Stmt]

type CFG = CFG' [Stmt]

type CFGsNoDefs = CFGsNoDefs' [Stmt]

type CFGs = CFGs' [Stmt]

data Store = Store
  { cfgs :: CFGsNoDefs,
    currStmts :: [Stmt],
    lastLabel :: Label,
    cfgDefs :: Defs,
    counter :: Int
  }
  deriving (Show)

data Env = Env
  { currLabel :: Label,
    currFn :: Ident,
    currBindings :: Bindings
  }

type CFGM a = StateT Store (ReaderT Env IO) a

debugPrint :: String -> CFGM ()
debugPrint s = when False $ liftIO $ hPutStrLn stderr $ "CFG: " ++ s

freshLabel :: CFGM Label
freshLabel = do
  st <- get
  case CFG.lastLabel st of
    BlockLabel n -> do
      let fresh = BlockLabel (n + 1)
      put (st {lastLabel = fresh})
      return fresh
    _else -> error "why"

freshIdent :: CFGM Ident
freshIdent = do
  st <- get
  let fresh = counter st + 1
  put (st {counter = fresh})
  -- this ident must be illegal in the language but
  -- legal in LLVM to guarantee it is not used in the
  -- source code (and that it will still compile :p)
  return (Ident ("_" ++ show fresh))

addBBToCFG :: BB -> CFGM ()
addBBToCFG bb = mapLabelToBB (label bb) bb

withLabel :: Label -> Env -> Env
withLabel lab env = env {currLabel = lab}

addEmptyBB :: Label -> CFGM BB
addEmptyBB lab = do
  let bb = emptyBB lab
  addBBToCFG bb
  return bb

getCurrFnCFG :: CFGM CFG
getCurrFnCFG = do
  idt <- asks currFn
  gets (M.findWithDefault M.empty idt . cfgs)

getBB :: Label -> CFGM BB
getBB lab = do
  cfg <- getCurrFnCFG
  case M.lookup lab cfg of
    Just bb -> return bb
    Nothing -> addEmptyBB lab

putStmtsToBB :: Label -> [Stmt] -> CFGM ()
putStmtsToBB lab ss = do
  bb <- getBB lab
  let bb' = bb {stmts = ss}
  mapLabelToBB lab bb'

putBindingsToBB :: Label -> Bindings -> CFGM ()
putBindingsToBB lab bdg = do
  bb <- getBB lab
  let bb' = bb {bindings = bdg}
  mapLabelToBB lab bb'

addEdgesFromTo :: [Label] -> Label -> When -> CFGM ()
addEdgesFromTo labs bb w = mapM_ (\l -> addEdgeFromTo l bb w) labs

applyToCurrCFG :: (CFG -> CFG) -> CFGM ()
applyToCurrCFG f = do
  idt <- asks currFn
  modify
    ( \st ->
        st
          { cfgs =
              M.update
                (Just . f)
                idt
                (cfgs st)
          }
    )

replaceCurrRefToLabel :: Label -> Label -> Node -> CFGM ()
replaceCurrRefToLabel labFrom labTo node = applyToCurrCFG (replaceRefToLabel labFrom labTo node)

mapLabelToBB :: Label -> BB -> CFGM ()
mapLabelToBB lab bb = applyToCurrCFG (M.insert lab bb)

deleteLabel :: Label -> CFGM ()
deleteLabel lab = applyToCurrCFG (M.delete lab)

addEdgeFromTo :: Label -> Label -> When -> CFGM ()
addEdgeFromTo lab0 lab1 w = do
  debugPrint $ "add adge " ++ show lab0 ++ " -> " ++ show lab1 ++ " when " ++ show w
  bb0 <- getBB lab0
  bb1 <- getBB lab1
  if null (stmts bb0) && null (succs bb0)
    then do
      mapM_ (replaceCurrRefToLabel lab0 lab1) (preds bb0)
      mapLabelToBB lab1 $ bb1 {preds = preds bb0 ++ preds bb1}
      deleteLabel lab0
    else do
      mapLabelToBB lab0 $ bb0 {succs = (FnBlock lab1, w) : succs bb0}
      mapLabelToBB lab1 $ bb1 {preds = FnBlock lab0 : preds bb1}

addEntryEdgeTo :: Label -> Ident -> CFGM ()
addEntryEdgeTo lab fnname = do
  bb <- getBB lab
  let bb' = bb {preds = FnEntry fnname : preds bb}
  mapLabelToBB lab bb'

addRetEdgeFrom :: Label -> When -> CFGM ()
addRetEdgeFrom lab w = do
  bb <- getBB lab
  idt <- asks currFn
  let bb' = bb {succs = (FnRet idt, w) : succs bb}
  mapLabelToBB lab bb'

takeCurrStmts :: CFGM [Stmt]
takeCurrStmts = do
  st <- get
  let s = currStmts st
  put (st {currStmts = []})
  return s

addStmtToCurrBlock :: Stmt -> CFGM ()
addStmtToCurrBlock s = do
  st <- get
  put (st {currStmts = s : currStmts st})

endCurrBlock :: CFGM Label
endCurrBlock = do
  currLab <- asks currLabel

  ss <- takeCurrStmts
  putStmtsToBB currLab ss

  debugPrint $
    "endCurrBlock currLab="
      ++ show currLab
      ++ " currStmts:\n"
      ++ printCode (reverse ss)

  currBdgs <- asks currBindings
  putBindingsToBB currLab currBdgs

  return currLab

scHelper :: Bool -> (BNFC'Position, Expr, Expr) -> (Label, Label) -> (Expr -> CFGM (Env, Expr)) -> CFGM (Env, Expr)
scHelper shortOnTrue (p, e1, e2) (labOnTrue, labOnFalse) m = do
  idt <- freshIdent
  env <- bindVar idt (Bool p)
  nonSCLab <- freshLabel
  let lit = if shortOnTrue then ELitTrue p else ELitFalse p
  let (innerTrue, innerFalse) = if shortOnTrue then (labOnTrue, nonSCLab) else (nonSCLab, labOnFalse)
  addStmtToCurrBlock (Decl p (Bool p) [Init p idt lit])
  local
    (const env)
    ( do
        (env', e1') <- m e1
        (env'', e2') <- local (const env') $ m e2
        local
          (const env'')
          ( do
              let inner = Ass p idt e2'
              addStmtToCurrBlock (Cond p e1' inner)
              currLab <- endCurrBlock

              local (withLabel nonSCLab) $ addStmtToCurrBlock inner

              let e = EVar p idt

              addEdgeFromTo currLab innerTrue WhenTrue
              addEdgeFromTo currLab innerFalse WhenFalse

              return (withLabel nonSCLab env'', e)
          )
    )

tryShortCircuitCondExpr :: (Label, Label) -> Expr -> CFGM (Env, Expr)
tryShortCircuitCondExpr labs (EAnd p e1 e2) = scHelper False (p, e1, e2) labs (tryShortCircuitCondExpr labs)
tryShortCircuitCondExpr labs (EOr p e1 e2) = scHelper True (p, e1, e2) labs (tryShortCircuitCondExpr labs)
tryShortCircuitCondExpr labs (Not p e) = do
  (env, e') <- tryShortCircuitCondExpr labs e
  return (env, Not p e')
tryShortCircuitCondExpr _ e = do
  env <- ask
  return (env, e)

tryShortCircuitAndOr :: Bool -> (BNFC'Position, Expr, Expr) -> CFGM (Env, Expr)
tryShortCircuitAndOr shortOnTrue andOr = do
  doneLab <- freshLabel

  (env, e) <- scHelper shortOnTrue andOr (doneLab, doneLab) tryShortCircuitExpr

  local
    (const env)
    ( do
        nonSCLab <- endCurrBlock
        addEdgeFromTo nonSCLab doneLab WhenDone
        resEnv <- ask
        return (withLabel doneLab resEnv, e)
    )

tryShortCircuitExpr :: Expr -> CFGM (Env, Expr)
tryShortCircuitExpr (EApp p idt es) = do
  (resEnv, es') <- f es
  return (resEnv, EApp p idt es')
  where
    f (h : t) = do
      (env', h') <- tryShortCircuitExpr h
      (env'', t') <- local (const env') $ f t
      return (env'', h' : t')
    f [] = do
      env <- ask
      return (env, [])
tryShortCircuitExpr (EAnd p e1 e2) = tryShortCircuitAndOr False (p, e1, e2)
tryShortCircuitExpr (EOr p e1 e2) = tryShortCircuitAndOr True (p, e1, e2)
tryShortCircuitExpr (Not p e) = do
  (env, e') <- tryShortCircuitExpr e
  return (env, Not p e')
tryShortCircuitExpr e = do
  env <- ask
  return (env, e)

procStmts :: [Stmt] -> CFGM [Label]
procStmts [] = do
  currLab <- endCurrBlock
  return [currLab]
procStmts (stmt : t) = do
  currLab_ <- asks currLabel
  debugPrint $ "procStmts currLab=" ++ show currLab_ ++ " stmts:\n" ++ printCode [stmt]
  case stmt of
    (BStmt _ (Block _ ss)) -> do
      -- BStmt can be either inlined into adjacent blocks or is
      -- handled by cond flow already

      -- We create a new block only for the sake of easier handling
      -- of variable shadowing in the new block. The block is temporary
      -- and is merged later with currLab
      currLab <- endCurrBlock
      lab1 <- freshLabel
      addEdgeFromTo currLab lab1 WhenDone

      retLabs <- local (withLabel lab1) $ procStmts ss

      if null retLabs
        then return []
        else do
          lab2 <- freshLabel

          addEdgesFromTo (assert (length retLabs <= 1) retLabs) lab2 WhenDone

          local (withLabel lab2) $ procStmts t
    (Ret p e) -> do
      (env', e') <- tryShortCircuitExpr e
      local (const env') $ handleRets (Ret p e')
    (VRet _) -> handleRets stmt
    (Cond _ _ (Empty _)) -> procStmts t
    (Cond _ (ELitFalse _) _) -> procStmts t
    (Cond _ (ELitTrue _) innerTrue) -> procStmts (innerTrue : t)
    (Cond p e inner) -> do
      onTrueLab <- freshLabel
      onFalseLab <- freshLabel

      (env', e') <- tryShortCircuitCondExpr (onTrueLab, onFalseLab) e

      local
        (const env')
        ( do
            addStmtToCurrBlock (Cond p e' inner)
            nonSCLab <- endCurrBlock

            addEdgeFromTo nonSCLab onTrueLab WhenTrue

            retLabs <- local (withLabel onTrueLab) $ procStmts [inner]

            addEdgeFromTo nonSCLab onFalseLab WhenFalse
            addEdgesFromTo retLabs onFalseLab WhenDone

            local (withLabel onFalseLab) $ procStmts t
        )
    (CondElse _ (ELitTrue _) innerTrue _) -> procStmts (innerTrue : t)
    (CondElse _ (ELitFalse _) _ innerFalse) -> procStmts (innerFalse : t)
    (CondElse _ _ (Empty _) (Empty _)) -> procStmts t
    (CondElse p e innerTrue (Empty _)) -> procStmts (Cond p e innerTrue : t)
    (CondElse p e (Empty _) innerFalse) -> procStmts (Cond p (Neg p e) innerFalse : t)
    (CondElse p e innerTrue innerFalse) -> do
      onTrueLab <- freshLabel
      onFalseLab <- freshLabel

      (env', e') <- tryShortCircuitCondExpr (onTrueLab, onFalseLab) e
      local
        (const env')
        ( do
            addStmtToCurrBlock (CondElse p e' innerTrue innerFalse)
            nonSCLab <- endCurrBlock

            addEdgeFromTo nonSCLab onTrueLab WhenTrue
            retLabsTrue <- local (withLabel onTrueLab) $ procStmts [innerTrue]

            addEdgeFromTo nonSCLab onFalseLab WhenFalse
            retLabsFalse <- local (withLabel onFalseLab) $ procStmts [innerFalse]

            let retLabs = retLabsTrue ++ retLabsFalse
            debugPrint $ "CondElse retLabs=" ++ show retLabs
            if null retLabs
              then return []
              else do
                lab3 <- freshLabel
                addEdgesFromTo (retLabsTrue ++ retLabsFalse) lab3 WhenDone
                local (withLabel lab3) $ procStmts t
        )
    (While p e loopBody) -> do
      currLab <- endCurrBlock
      guardLab <- freshLabel
      bodyLab <- freshLabel
      endLab <- freshLabel

      addEdgeFromTo currLab guardLab WhenDone
      (env', e') <- local (withLabel guardLab) $ tryShortCircuitCondExpr (bodyLab, endLab) e
      local
        (const env')
        ( do
            addStmtToCurrBlock (While p e' loopBody)
            whileLab <- endCurrBlock

            addEdgeFromTo whileLab bodyLab WhenTrue

            retLabsDone <- local (withLabel bodyLab) $ procStmts [loopBody]

            addEdgesFromTo retLabsDone guardLab WhenDone
            addEdgeFromTo whileLab endLab WhenFalse

            local (withLabel endLab) $ procStmts t
        )
    (Decl _ tp items) -> do
      env' <- readerSeq declareItem items
      addStmtToCurrBlock stmt
      local (const env') $ procStmts t
      where
        declareItem :: Item -> CFGM Env
        declareItem (NoInit _ idt) = bindVar idt tp
        declareItem (Init _ idt _) = bindVar idt tp
    (SExp _ (ELitTrue _)) -> procStmts t
    (SExp _ (ELitFalse _)) -> procStmts t
    (SExp p (EOr _ (ELitFalse _) e)) -> procStmts (SExp p e : t)
    (SExp p (EAnd _ (ELitTrue _) e)) -> procStmts (SExp p e : t)
    (SExp _ (EOr _ (ELitTrue _) _)) -> procStmts t
    (SExp _ (EAnd _ (ELitFalse _) _)) -> procStmts t
    (SExp p e) -> do
      (env', e') <- tryShortCircuitExpr e
      local
        (const env')
        ( do
            addStmtToCurrBlock (SExp p e')
            procStmts t
        )
    _else -> do
      addStmtToCurrBlock stmt
      procStmts t
  where
    handleRets :: Stmt -> CFGM [Label]
    handleRets s = do
      addStmtToCurrBlock s
      currLab <- endCurrBlock
      addRetEdgeFrom currLab WhenDone
      return []

addBinding :: Def -> Ident -> CFGM Env
addBinding def idt = do
  sloc <- newSLoc
  modify
    ( \st ->
        st
          { cfgDefs = M.insert sloc def (cfgDefs st)
          }
    )
  env <- ask
  return env {currBindings = M.alter (f sloc) idt (currBindings env)}
  where
    f sloc Nothing = Just [sloc]
    f sloc (Just l) = Just (sloc : l)

bindVar :: Ident -> Type -> CFGM Env
bindVar idt tp = do
  currLab <- asks currLabel
  addBinding (DVar tp currLab) idt

bindArg :: Ident -> Type -> CFGM Env
bindArg idt tp = do
  currLab <- asks currLabel
  addBinding (DArg tp currLab) idt

newSLoc :: CFGM SLoc
newSLoc = gets (M.size . cfgDefs)

procBlock :: Block -> CFGM [Label]
procBlock (Block _ ss) = procStmts ss

procTopDef :: TopDef -> CFGM ()
procTopDef (FnDef _ rettp fnname args block) = do
  modify (\st -> st {cfgs = M.insert fnname M.empty (cfgs st)})
  lab <- freshLabel
  let env =
        Env
          { currLabel = lab,
            currFn = fnname,
            currBindings = M.empty
          }
  env' <- local (const env) $ readerSeq bindArgs args
  local
    (const env')
    ( do
        addEntryEdgeTo lab fnname
        retLabs <- procBlock block

        -- void functions can lack return stmt, add it for them
        when (isVoid rettp) $ mapM_ addVRetIfImplicit retLabs
        -- removeDeadNodes
    )
  where
    bindArgs :: Arg -> CFGM Env
    bindArgs (Arg _ tp idt) = bindArg idt tp

    isVRet :: Stmt -> Bool
    isVRet (VRet _) = True
    isVRet _ = False

    isVoid :: Type -> Bool
    isVoid (Void _) = True
    isVoid _ = False

    addVRetIfImplicit :: Label -> CFGM ()
    addVRetIfImplicit lab = do
      bb <- getBB lab
      case find isVRet $ stmts bb of
        Nothing -> do
          putStmtsToBB lab (VRet BNFC'NoPosition : stmts bb)
          addRetEdgeFrom lab WhenDone
        _else -> return ()

procProgram :: Program -> CFGM ()
procProgram (Program _ topdefs) = mapM_ procTopDef topdefs

runCFGM :: TypeCheckInfo -> CFGM a -> IO (a, Store)
runCFGM tcinfo m = runReaderT (runStateT m initStore) initEnv
  where
    initStore =
      Store
        { cfgs = M.empty,
          counter = 0,
          currStmts = [],
          CFG.lastLabel = BlockLabel 0,
          cfgDefs = globalDefs tcinfo
        }
    initEnv =
      Env
        { currFn = Ident "??",
          currLabel = BlockLabel 0,
          currBindings = globalBindings tcinfo
        }

genCFGs :: TypeCheckInfo -> Program -> IO CFGs
genCFGs tcinfo p = do
  (_, st) <- runCFGM tcinfo (procProgram p)
  return
    ( cfgs st,
      CFGInfo
        { cfgInfoDefs = cfgDefs st,
          cfgInfoBindings = globalBindings tcinfo,
          opts = []
        }
    )
