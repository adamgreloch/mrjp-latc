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
import Data.Bifunctor qualified
import Data.List (find)
import Data.Map qualified as M
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
    cfgDefs :: Defs
  }
  deriving (Show)

data Env = Env
  { currLabel :: Label,
    currFn :: Ident,
    currBindings :: Bindings
  }

type CFGM a = StateT Store (ReaderT Env IO) a

debugPrint :: String -> CFGM ()
debugPrint s = when True $ liftIO $ hPutStrLn stderr $ "CFG: " ++ s

freshLabel :: CFGM Label
freshLabel = do
  st <- get
  let fresh = CFG.lastLabel st + 1
  put (st {CFG.lastLabel = fresh})
  return fresh

addBBToCFG :: BB -> CFGM ()
addBBToCFG bb = mapLabelToBB (label bb) bb

emptyBB :: Label -> BB
emptyBB label = BB' {label, stmts = [], preds = [], succs = [], bindings = M.empty}

withLabel :: Label -> Env -> Env
withLabel lab env = env {currLabel = lab}

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

addEdgeFromTo :: Label -> Label -> When -> CFGM ()
addEdgeFromTo lab0 lab1 w = do
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

mergeLabels :: Label -> Label -> CFGM ()
mergeLabels lab0 lab1 = do
  bb0 <- getBB lab0
  bb1 <- getBB lab1
  mapM_ (replaceRefToLabel lab0 lab1) (preds bb0)
  mapM_ (\(l, _) -> replaceRefToLabel lab0 lab1 l) (succs bb0)
  mapLabelToBB lab1 $ bb1 {stmts = stmts bb1 ++ stmts bb0, preds = preds bb0}
  removeLabel lab0

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
      ++ printCode currStmts

  currBdgs <- asks currBindings
  putBindingsToBB currLab currBdgs

  return currLab

procStmts :: [Stmt] -> CFGM [Label]
procStmts [] = do
  currLab <- endCurrBlock
  return [currLab]
procStmts (stmt : t) = do
  currLab_ <- asks currLabel
  debugPrint $ "procStmts currLab=" ++ show currLab_ ++ " stmts:\n" ++ printCode [stmt]
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
    (Ret _ _) -> handleRets stmt
    (VRet _) -> handleRets stmt
    (Cond _ _ inner) -> do
      addStmtToCurrBlock stmt
      currLab <- endCurrBlock

      lab1 <- freshLabel
      addEdgeFromTo currLab lab1 WhenTrue
      retLabs <- local (withLabel lab1) $ procStmts [inner]

      lab2 <- freshLabel
      addEdgeFromTo currLab lab2 WhenFalse
      addEdgesFromTo retLabs lab2 WhenDone
      local (withLabel lab2) $ procStmts t
    (CondElse _ _ innerTrue innerFalse) -> do
      addStmtToCurrBlock stmt
      currLab <- endCurrBlock

      lab1 <- freshLabel
      addEdgeFromTo currLab lab1 WhenTrue
      retLabsTrue <- local (withLabel lab1) $ procStmts [innerTrue]

      lab2 <- freshLabel
      addEdgeFromTo currLab lab2 WhenFalse
      retLabsFalse <- local (withLabel lab2) $ procStmts [innerFalse]

      let retLabs = retLabsTrue ++ retLabsFalse
      debugPrint $ "CondElse retLabs=" ++ show retLabs
      if null retLabs
        then return []
        else do
          lab3 <- freshLabel
          addEdgesFromTo (retLabsTrue ++ retLabsFalse) lab3 WhenDone
          local (withLabel lab3) $ procStmts t
    (While _ _ loopBody) -> do
      currLab <- endCurrBlock

      lab1 <- freshLabel
      local
        (withLabel lab1)
        ( do
            addStmtToCurrBlock stmt
            _ <- endCurrBlock
            return ()
        )

      addEdgeFromTo currLab lab1 WhenDone

      lab2 <- freshLabel
      addEdgeFromTo lab1 lab2 WhenTrue
      retLabsDone <- local (withLabel lab2) $ procStmts [loopBody]

      addEdgesFromTo retLabsDone lab1 WhenDone

      lab3 <- freshLabel
      addEdgeFromTo lab1 lab3 WhenFalse
      local (withLabel lab3) $ procStmts t
    (Decl _ tp items) -> do
      env' <- readerSeq declareItem items
      addStmtToCurrBlock stmt
      local (const env') $ procStmts t
      where
        declareItem :: Item -> CFGM Env
        declareItem (NoInit _ idt) = bindVar idt tp
        declareItem (Init _ idt _) = bindVar idt tp
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
  debugPrint $ "addBinding " ++ show idt ++ "(" ++ show tp ++ ", " ++ show currLab ++ ")"
  modify
    ( \st ->
        st
          { cfgDefs = M.insert sloc def (cfgDefs st)
          }
    )
  env <- ask
  return env {currBindings = M.insert idt sloc (currBindings env)}

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
procProgram (Program _ topdefs) =
  mapM_ procTopDef topdefs

runCFGM :: TypeCheckInfo -> CFGM a -> IO (a, Store)
runCFGM tcinfo m = runReaderT (runStateT m initStore) initEnv
  where
    initStore =
      Store
        { cfgs = M.empty,
          currStmts = [],
          CFG.lastLabel = 0,
          cfgDefs = globalDefs tcinfo
        }
    initEnv =
      Env
        { currFn = Ident "??",
          currLabel = 0,
          currBindings = globalBindings tcinfo
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
    bbLabStr = "L" ++ show (label bb)
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
