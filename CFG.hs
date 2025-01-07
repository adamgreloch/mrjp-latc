{-# LANGUAGE StrictData #-}

module CFG
  ( genCFGs,
    toDot,
    Label,
    CFG,
    CFGs,
    CFGs',
    BB' (BB', label, stmts, preds, succs),
    mapTo,
  )
where

import AbsLatte
import CFGDefs
import Common
import Control.Exception (assert)
import Control.Monad (foldM, unless, when)
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
import Data.Bifunctor qualified
import Data.List (find)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Text (pack, replace, unpack)
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
    currBindings :: Bindings,
    currSCLabel :: Maybe (When, Label)
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

emptyBB :: Label -> BB
emptyBB label = BB' {label, stmts = [], preds = [], succs = [], bindings = M.empty}

withLabel :: Label -> Env -> Env
withLabel lab env = env {currLabel = lab}

withSCLabel :: (When, Label) -> Env -> Env
withSCLabel we env = env {currSCLabel = Just we}

addEmptyBB :: Label -> CFGM BB
addEmptyBB label = do
  let bb = emptyBB label
  addBBToCFG bb
  return bb

getCurrFnCFG :: CFGM CFG
getCurrFnCFG = do
  idt <- asks currFn
  gets (M.findWithDefault M.empty idt . cfgs)

getBB :: Label -> CFGM BB
getBB label = do
  cfg <- getCurrFnCFG
  case M.lookup label cfg of
    Just bb -> return bb
    Nothing -> addEmptyBB label

putStmtsToBB :: Label -> [Stmt] -> CFGM ()
putStmtsToBB lab stmts = do
  bb <- getBB lab
  let bb' = bb {stmts = stmts}
  mapLabelToBB lab bb'

putBindingsToBB :: Label -> Bindings -> CFGM ()
putBindingsToBB lab bdg = do
  bb <- getBB lab
  let bb' = bb {bindings = bdg}
  mapLabelToBB lab bb'

addEdgesFromTo :: [Label] -> Label -> When -> CFGM ()
addEdgesFromTo labs bb w = mapM_ (\l -> addEdgeFromTo l bb w) labs

replaceRefToLabel :: Label -> Label -> Node -> CFGM ()
replaceRefToLabel labFrom labTo (FnBlock lab) = do
  bb <- getBB lab
  let bb' = bb {preds = map repl (preds bb), succs = map (Data.Bifunctor.first repl) (succs bb)}
  mapLabelToBB lab bb'
  where
    repl :: Node -> Node
    repl n@(FnBlock l) = if l == labFrom then FnBlock labTo else n
    repl n = n
replaceRefToLabel _ _ _ = return ()

removeRefToLabel :: Label -> Node -> CFGM ()
removeRefToLabel labToDelete (FnBlock lab) = do
  bb <- getBB lab
  let bb' = bb {preds = filter keep (preds bb), succs = filter (\(w, n) -> keep w) (succs bb)}
  mapLabelToBB lab bb'
  where
    keep :: Node -> Bool
    keep n@(FnBlock l) = l /= labToDelete
    keep n = True
removeRefToLabel _ _ = return ()

mapLabelToBB :: Label -> BB -> CFGM ()
mapLabelToBB lab bb = do
  idt <- asks currFn
  modify
    ( \st ->
        st
          { cfgs =
              M.update
                (Just . M.insert lab bb)
                idt
                (cfgs st)
          }
    )

removeLabel :: Label -> CFGM ()
removeLabel lab = do
  idt <- asks currFn
  st <- get
  debugPrint $ show (cfgs st)
  modify
    ( \st ->
        st
          { cfgs =
              M.update
                (Just . M.delete lab)
                idt
                (cfgs st)
          }
    )
  st <- get
  debugPrint $ show (cfgs st)

removeBBIfDead :: BB -> CFGM ()
removeBBIfDead bb = do
  let lab = label bb
  idt <- asks currFn
  when
    (null (succs bb))
    ( do
        debugPrint $ "removing " ++ show lab
        mapM_ (removeRefToLabel lab) (preds bb)
        removeLabel lab
    )

addEdgeFromTo :: Label -> Label -> When -> CFGM ()
addEdgeFromTo lab0 lab1 w = do
  debugPrint $ "add adge " ++ show lab0 ++ " -> " ++ show lab1 ++ " when " ++ show w
  bb0 <- getBB lab0
  bb1 <- getBB lab1
  if null (stmts bb0) && null (succs bb0)
    then do
      mapM_ (replaceRefToLabel lab0 lab1) (preds bb0)
      mapLabelToBB lab1 $ bb1 {preds = preds bb0 ++ preds bb1}
      removeLabel lab0
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

  currStmts <- takeCurrStmts
  putStmtsToBB currLab currStmts

  debugPrint $
    "endCurrBlock currLab="
      ++ show currLab
      ++ " currStmts:\n"
      ++ printCode (reverse currStmts)

  currBdgs <- asks currBindings
  putBindingsToBB currLab currBdgs

  return currLab

type CB = Expr -> CFGM (Label, Label, Env)

type CS = Expr -> CFGM [Label]

type CM = CFGM [Label]

type CallBacks = (CB, CM, CS)

justLabels :: Label -> Label -> Env -> CallBacks
justLabels lab1 lab2 env = (\_ -> return (lab1, lab2, env), return [], \_ -> return [])

shortCircuit :: Bool -> BNFC'Position -> Expr -> Expr -> CallBacks -> CFGM (Env, Expr, Bool)
shortCircuit shortOnTrue p e1 e2 cbs@(csc, cyes, cno) = do
  idt <- freshIdent
  env <- bindVar idt (Bool p)
  lab1 <- freshLabel
  let lit = if shortOnTrue then ELitTrue p else ELitFalse p
  addStmtToCurrBlock (Decl p (Bool p) [Init p idt lit])
  local
    (const env)
    ( do
        (env', e1', _) <- shortcircuitIfBExpr e1 cbs
        (env'', e2', _) <- local (const env') $ shortcircuitIfBExpr e2 cbs
        local
          (const env'')
          ( do
              let inner = Ass p idt e2'
              addStmtToCurrBlock (Cond p e1' inner)
              currLab <- endCurrBlock

              local (withLabel lab1) $ addStmtToCurrBlock inner

              let e = EVar p idt

              (labOnTrue, labOnFalse, newEnv) <- local (withLabel lab1) $ csc e

              let (innerTrue, innerFalse) = if shortOnTrue then (labOnTrue, lab1) else (lab1, labOnFalse)
              addEdgeFromTo currLab innerTrue WhenTrue
              addEdgeFromTo currLab innerFalse WhenFalse

              return (withLabel lab1 env'', e, True)
          )
    )

handleExpr :: Expr -> CallBacks -> CFGM [Label]
handleExpr e cbs@(csc, cyes, cno) = do
  (env', e1', b) <- shortcircuitIfBExpr e cbs
  if b then local (const env') cyes else cno e

shortcircuitIfBExpr :: Expr -> CallBacks -> CFGM (Env, Expr, Bool)
shortcircuitIfBExpr (EAnd p e1 e2) cbs = shortCircuit False p e1 e2 cbs
shortcircuitIfBExpr (EOr p e1 e2) cbs = shortCircuit True p e1 e2 cbs
shortcircuitIfBExpr (Not p e) cbs = do
  (env, e', b) <- shortcircuitIfBExpr e cbs
  return (env, Not p e', b)
shortcircuitIfBExpr e cbs@(csc, cyes, cno) = do
  env <- ask
  return (env, e, False)

qshortCircuit :: Bool -> BNFC'Position -> Expr -> Expr -> CFGM (Env, Expr, Bool)
qshortCircuit shortOnTrue p e1 e2 = do
  idt <- freshIdent
  env <- bindVar idt (Bool p)
  lab1 <- freshLabel
  let lit = if shortOnTrue then ELitTrue p else ELitFalse p
  addStmtToCurrBlock (Decl p (Bool p) [Init p idt lit])
  local
    (const env)
    ( do
        (env', e1', msc) <- qshortcircuitIfBExpr e1
        (env'', e2', msc') <- local (const env') $ qshortcircuitIfBExpr e2
        local
          (const env'')
          ( do
              let inner = Ass p idt e2'
              addStmtToCurrBlock (Cond p e1' inner)
              currLab <- endCurrBlock

              local (withLabel lab1) $ addStmtToCurrBlock inner

              let e = EVar p idt

              sc <- freshLabel

              let whenSC = if shortOnTrue then WhenTrue else WhenFalse

              if shortOnTrue
                then do
                  -- addEdgeFromTo currLab sc WhenTrue
                  addEdgeFromTo currLab lab1 WhenFalse
                else do
                  addEdgeFromTo currLab lab1 WhenTrue
              -- addEdgeFromTo currLab sc WhenFalse

              debugPrint $ "can short-circuit from " ++ show currLab ++ " when " ++ show whenSC

              resEnv <-
                local
                  (withLabel lab1 . withSCLabel (whenSC, currLab))
                  ( do
                      env <- ask
                      nonSC <- endCurrBlock
                      doneLab <- freshLabel
                      addEdgeFromTo nonSC doneLab WhenDone
                      mscLab <- asks currSCLabel
                      case mscLab of
                        Nothing -> error "no sc lab when expected"
                        Just (whenSC, scLab) -> do
                          addEdgeFromTo scLab doneLab whenSC
                          return $ withLabel doneLab env
                  )

              return (resEnv, e, True)
          )
    )

qshortcircuitIfBExpr :: Expr -> CFGM (Env, Expr, Bool)
qshortcircuitIfBExpr (EApp p idt es) = do
  (resEnv, es', b) <- f es
  return (resEnv, EApp p idt es', b)
  where
    f (h : t) = do
      (env', h', b1) <- qshortcircuitIfBExpr h
      (env'', t', b2) <- local (const env') $ f t
      return (env'', h' : t', b1 || b2)
    f [] = do
      env <- ask
      return (env, [], False)
qshortcircuitIfBExpr (EAnd p e1 e2) = qshortCircuit False p e1 e2
qshortcircuitIfBExpr (EOr p e1 e2) = qshortCircuit True p e1 e2
qshortcircuitIfBExpr (Not p e) = do
  (env, e', b) <- qshortcircuitIfBExpr e
  return (env, Not p e', b)
qshortcircuitIfBExpr e = do
  env <- ask
  return (env, e, False)

procStmts :: [Stmt] -> CFGM [Label]
procStmts [] = do
  currLab <- endCurrBlock
  return [currLab]
procStmts (stmt : t) = do
  currLab_ <- asks currLabel
  debugPrint $ "procStmts currLab=" ++ show currLab_ ++ " stmts:\n" ++ printCode [stmt]
  env <- ask
  case stmt of
    (BStmt _ (Block _ stmts)) -> do
      -- BStmt can be either inlined into adjacent blocks or is
      -- handled by cond flow already

      -- We create a new block only for the sake of easier handling
      -- of variable shadowing in the new block. The block is temporary
      -- and is merged later with currLab
      currLab <- endCurrBlock
      lab1 <- freshLabel
      addEdgeFromTo currLab lab1 WhenDone

      retLabs <- local (withLabel lab1) $ procStmts stmts

      if null retLabs
        then return []
        else do
          lab2 <- freshLabel

          addEdgesFromTo (assert (length retLabs <= 1) retLabs) lab2 WhenDone

          -- TODO defer this optimalization post FIR:
          -- mergeLabels currLab lab1

          local (withLabel lab2) $ procStmts t
    (Ret p e) -> do
      let cb e' =
            ( do
                let p = hasPosition e'
                onTrueLab <- freshLabel
                onFalseLab <- freshLabel

                addStmtToCurrBlock (CondElse p e' (Empty p) (Empty p))
                currLab <- endCurrBlock

                addEdgeFromTo currLab onTrueLab WhenTrue
                local
                  (withLabel onTrueLab)
                  ( do
                      addStmtToCurrBlock (Ret p (ELitTrue p))
                      endCurrBlock
                  )
                addRetEdgeFrom onTrueLab WhenDone

                addEdgeFromTo currLab onFalseLab WhenFalse
                local
                  (withLabel onFalseLab)
                  ( do
                      addStmtToCurrBlock (Ret p (ELitFalse p))
                      endCurrBlock
                  )
                addRetEdgeFrom onFalseLab WhenDone

                env <- ask

                return (onTrueLab, onFalseLab, env)
            )
      handleExpr e (cb, return [], \_ -> handleRets stmt)
    (VRet _) -> handleRets stmt
    -- (Cond _ _ (Empty _)) -> procStmts t
    (Cond _ (ELitFalse _) _) -> procStmts t
    (Cond _ (ELitTrue _) innerTrue) -> procStmts (innerTrue : t)
    (Cond p e inner) -> do
      onTrueLab <- freshLabel
      onFalseLab <- freshLabel

      (env', e', _) <- shortcircuitIfBExpr e (justLabels onTrueLab onFalseLab env)

      local
        (const env')
        ( do
            addStmtToCurrBlock (Cond p e' inner)
            currLab <- endCurrBlock

            addEdgeFromTo currLab onTrueLab WhenTrue

            retLabs <- local (withLabel onTrueLab) $ procStmts [inner]

            addEdgeFromTo currLab onFalseLab WhenFalse
            addEdgesFromTo retLabs onFalseLab WhenDone
            local (withLabel onFalseLab) $ procStmts t
        )
    (CondElse _ (ELitTrue _) innerTrue _) -> procStmts (innerTrue : t)
    (CondElse _ (ELitFalse _) _ innerFalse) -> procStmts (innerFalse : t)
    (CondElse p e (Empty _) (Empty _)) -> procStmts t
    (CondElse p e innerTrue (Empty _)) -> procStmts (Cond p e innerTrue : t)
    (CondElse p e (Empty _) innerFalse) -> procStmts (Cond p (Neg p e) innerFalse : t)
    (CondElse p e innerTrue innerFalse) -> do
      onTrueLab <- freshLabel
      onFalseLab <- freshLabel

      (env', e', _) <- shortcircuitIfBExpr e (justLabels onTrueLab onFalseLab env)
      local
        (const env')
        ( do
            addStmtToCurrBlock (CondElse p e' innerTrue innerFalse)
            currLab <- endCurrBlock

            addEdgeFromTo currLab onTrueLab WhenTrue
            retLabsTrue <- local (withLabel onTrueLab) $ procStmts [innerTrue]

            addEdgeFromTo currLab onFalseLab WhenFalse
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
      (env', e', _) <- local (withLabel guardLab) $ shortcircuitIfBExpr e (justLabels bodyLab endLab env)
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
    (SExp p (ELitTrue _)) -> procStmts t
    (SExp p (ELitFalse _)) -> procStmts t
    (SExp p (EOr p1 (ELitFalse p2) e)) -> procStmts (SExp p e : t)
    (SExp p (EAnd p1 (ELitTrue p2) e)) -> procStmts (SExp p e : t)
    (SExp _ (EOr _ (ELitTrue _) _)) -> procStmts t
    (SExp _ (EAnd _ (ELitFalse _) _)) -> procStmts t
    (SExp p e) -> do
      (env', e', b) <- qshortcircuitIfBExpr e
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

addBinding :: Def -> Ident -> Type -> CFGM Env
addBinding def idt tp = do
  sloc <- newSLoc
  currLab <- asks currLabel
  modify
    ( \st ->
        st
          { cfgDefs = M.insert sloc def (cfgDefs st)
          }
    )
  st <- get
  -- debugPrint $ "addBinding " ++ show idt ++ "(sloc " ++ show sloc ++ ") " ++ "(" ++ show tp ++ ", " ++ show currLab ++ ")\n" ++ show (cfgDefs st)
  env <- ask
  return env {currBindings = M.alter (f sloc) idt (currBindings env)}
  where
    -- TODO could be done better
    f sloc Nothing = Just [sloc]
    f sloc (Just l) = Just (sloc : l)

bindVar :: Ident -> Type -> CFGM Env
bindVar idt tp = do
  currLab <- asks currLabel
  addBinding (DVar tp currLab) idt tp

bindArg :: Ident -> Type -> CFGM Env
bindArg idt tp = do
  currLab <- asks currLabel
  addBinding (DArg tp currLab) idt tp

newSLoc :: CFGM SLoc
newSLoc = gets (M.size . cfgDefs)

procBlock :: Block -> CFGM [Label]
procBlock (Block _ stmts) = procStmts stmts

procTopDef :: TopDef -> CFGM ()
procTopDef (FnDef _ rettp fnname args block) = do
  modify (\st -> st {cfgs = M.insert fnname M.empty (cfgs st)})
  lab <- freshLabel
  let env =
        Env
          { currLabel = lab,
            currFn = fnname,
            currBindings = M.empty,
            currSCLabel = Nothing
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

    removeDeadNodes :: CFGM ()
    removeDeadNodes = do
      st <- get
      mapM_
        ( mapM_
            ( \bb -> do
                debugPrint $ show bb
                removeBBIfDead bb
            )
        )
        (cfgs st)

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
          currBindings = globalBindings tcinfo,
          currSCLabel = Nothing
        }

genCFGs :: TypeCheckInfo -> Program -> IO CFGs
genCFGs tcinfo p = do
  (_, st) <- runCFGM tcinfo (procProgram p)
  return
    ( cfgs st,
      CFGInfo
        { cfgInfoDefs = cfgDefs st,
          cfgInfoBindings = globalBindings tcinfo
        }
    )

printableToDot :: (Printable [a]) => [a] -> String
printableToDot s =
  unpack $
    foldr
      ( \(from, to) acc ->
          replace (pack from) (pack to) acc
      )
      (pack (printCode s))
      replacePatterns
  where
    -- NOTE: pattern ordering is important here, e.g. "}\n" -> "}" assumes
    -- "}" -> "\\}" has been applied
    replacePatterns =
      [ (" ", "\\ "),
        ("\"", "\\\""),
        (".", "\\."),
        ("%", "\\%"),
        (">", "\\>"),
        ("<", "\\<"),
        ("{", "\\{"),
        ("}", "\\}"),
        ("\n", "\\l\n|"),
        ("}\n", "}")
      ]

bbToDot :: (Printable [a]) => BB' [a] -> String
bbToDot bb =
  bbLabStr
    ++ " [shape=record,style=filled,fillcolor=lightgrey,label=\"{"
    ++ bbLabStr
    ++ "\n|"
    ++ (printableToDot . reverse) (stmts bb)
    ++ "\\l\n}\"];\n\n"
    ++ foldr (\(s, w) acc -> bbLabStr ++ " -> " ++ show s ++ "[label=" ++ show w ++ "];\n" ++ acc) [] (succs bb)
    ++ foldr (\p acc -> show p ++ " -> " ++ bbLabStr ++ ";\n" ++ acc) [] (filter isFnEntry $ preds bb)
  where
    bbLabStr = show (label bb)
    isFnEntry :: Node -> Bool
    isFnEntry (FnEntry _) = True
    isFnEntry _ = False

toDotCFG :: (Printable [a]) => Ident -> CFG' [a] -> String
toDotCFG (Ident fnname) cfg =
  "subgraph \"cluster_"
    ++ fnname
    ++ "\" {\n style=\"dashed\";\n color=\"black\";\n label=\""
    ++ fnname
    ++ "()\";\n"
    ++ foldr (\(_, bb) acc -> bbToDot bb ++ "\n" ++ acc) [] (M.toList cfg)
    ++ "}"

toDot :: (Printable [a]) => CFGs' [a] -> String
toDot (cfgs, _) =
  "digraph \"cfgs\" {\noverlap=false;\n"
    ++ foldr (\(idt, cfg) acc -> toDotCFG idt cfg ++ "\n" ++ acc) [] (M.toList cfgs)
    ++ "}"

mapTo :: (CFGInfo -> BB' a -> BB' b) -> CFGs' a -> CFGs' b
mapTo f (cfgs, info) = (M.map (M.map (f info)) cfgs, info)
