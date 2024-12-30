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
import Control.Monad.Reader
  ( MonadReader (ask, local),
    Reader,
    asks,
    runReader,
  )
import Control.Monad.State
  ( MonadState (get, put),
    StateT,
    gets,
    modify,
    runStateT,
  )
import Data.Bifunctor qualified
import Data.Map qualified as M
import Data.Text (pack, replace, unpack)

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

type CFGM a = StateT Store (Reader Env) a

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

  currBdgs <- asks currBindings
  putBindingsToBB currLab currBdgs

  return currLab

procStmts :: [Stmt] -> CFGM [Label]
procStmts [] = do
  currLab <- endCurrBlock
  return [currLab]
procStmts (stmt : t) =
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

      lab2 <- freshLabel

      addEdgesFromTo (assert (length retLabs <= 1) retLabs) lab2 WhenDone
      mergeLabels currLab lab1
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
        declareItem (NoInit _ idt) = addBinding idt tp
        declareItem (Init _ idt _) = addBinding idt tp
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

addBinding :: Ident -> Type -> CFGM Env
addBinding idt tp = do
  sloc <- newSLoc
  currLab <- asks currLabel
  modify
    ( \st ->
        st
          { cfgDefs = M.insert sloc (tp, currLab) (cfgDefs st)
          }
    )
  env <- ask
  return env {currBindings = M.insert idt sloc (currBindings env)}

newSLoc :: CFGM SLoc
newSLoc = gets (M.size . cfgDefs)

procBlock :: Block -> CFGM ()
procBlock (Block _ stmts) = do
  _ <- procStmts stmts
  return ()

procTopDef :: TopDef -> CFGM ()
procTopDef (FnDef _ _ fnname args block) = do
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
        procBlock block
    )
  where
    bindArgs :: Arg -> CFGM Env
    bindArgs (Arg _ tp idt) = addBinding idt tp

procProgram :: Program -> CFGM ()
procProgram (Program _ topdefs) =
  mapM_ procTopDef topdefs

runCFGM :: CFGM a -> (a, Store)
runCFGM m = runReader (runStateT m initStore) initLabel
  where
    initStore =
      Store
        { cfgs = M.empty,
          currStmts = [],
          CFG.lastLabel = 0,
          cfgDefs = M.empty
        }
    initLabel =
      Env
        { currFn = Ident "??",
          currLabel = 0,
          currBindings = M.empty
        }

genCFGs :: Program -> CFGs
genCFGs p =
  let (_, st) = runCFGM (procProgram p)
   in (cfgs st, cfgDefs st)

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

mapTo :: (Defs -> BB' a -> BB' b) -> CFGs' a -> CFGs' b
mapTo f (cfgs, defs) = (M.map (M.map (f defs)) cfgs, defs)
