module CFG (genCFG, toDot) where

import AbsLatte
import Control.Monad.Reader
  ( MonadReader (ask, local),
    Reader,
    asks,
    runReader,
  )
import Control.Monad.State
  ( MonadState (get, put),
    State,
    gets,
    modify,
    runState,
  )
import Data.List
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Text (pack, replace, unpack)
import PrintLatte (printTree)

type Label = Int

data Node = FnEntry Ident | FnBlock Label | FnRet deriving (Eq)

instance Show Node where
  show (FnEntry (Ident s)) = "FnEntry_" ++ s
  show (FnBlock l) = "L" ++ show l
  show FnRet = "FnRet"

data BB = BB
  { label :: Label,
    stmts :: [Stmt],
    preds :: [Node],
    succs :: [Node]
  }
  deriving (Show)

type CFG = M.Map Label BB

data Store = Store
  { cfg :: CFG,
    currStmts :: [Stmt],
    currLabel :: Label,
    lastLabel :: Label,
    defs :: M.Map Ident (M.Map Label Expr)
  }
  deriving (Show)

type CFGM a = State Store a

setCurrLabel :: Label -> CFGM ()
setCurrLabel lab = do
  st <- get
  put (st {currLabel = lab})

freshLabel :: CFGM Label
freshLabel = do
  st <- get
  let fresh = lastLabel st + 1
  put (st {lastLabel = fresh})
  return fresh

addBBToCFG :: BB -> CFGM ()
addBBToCFG bb = do
  st <- get
  put (st {cfg = M.insert (label bb) bb (cfg st)})

emptyBB :: Label -> BB
emptyBB label = BB {label, stmts = [], preds = [], succs = []}

addEmptyBB :: Label -> CFGM BB
addEmptyBB label = do
  let bb = emptyBB label
  addBBToCFG bb
  return bb

getBB :: Label -> CFGM BB
getBB label = do
  st <- get
  case M.lookup label (cfg st) of
    Just bb -> return bb
    Nothing -> addEmptyBB label

putStmtsToBB :: Label -> [Stmt] -> CFGM ()
putStmtsToBB label stmts = do
  bb <- getBB label
  let bb' = bb {stmts = stmts}
  modify (\st -> st {cfg = M.insert label bb' (cfg st)})

-- TODO rewrite to fold
addEdgesFromTo :: [Label] -> Label -> CFGM ()
addEdgesFromTo [] _ = return ()
addEdgesFromTo (h : t) bb = do
  addEdgeFromTo h bb
  addEdgesFromTo t bb

-- assumes bb0->bb1
mergeBBs :: BB -> BB -> CFGM BB
mergeBBs bb0 bb1 = do
  return $ bb1 {stmts = stmts bb1 ++ stmts bb0, preds = preds bb0 ++ delete (FnBlock (label bb0)) (preds bb1)}

replaceRefToLabel :: Label -> Label -> Node -> CFGM ()
replaceRefToLabel labFrom labTo (FnBlock lab) = do
  bb <- getBB lab
  let bb' = bb {preds = map repl (preds bb), succs = map repl (succs bb)}
  st <- get
  let cfg' = M.insert lab bb' $ cfg st
  put (st {cfg = cfg'})
  where
    repl :: Node -> Node
    repl n@(FnBlock l) = if l == labFrom then FnBlock labTo else n
    repl n = n
replaceRefToLabel _ _ _ = return ()

addEdgeFromTo :: Label -> Label -> CFGM ()
addEdgeFromTo lab0 lab1 = do
  bb0 <- getBB lab0
  bb1 <- getBB lab1
  if null (stmts bb0) && null (succs bb0)
    then do
      let bb01 = bb1 {stmts = stmts bb1 ++ stmts bb0, preds = preds bb0 ++ preds bb1}
      mapM_ (replaceRefToLabel lab0 lab1) (preds bb0)
      mapM_ (replaceRefToLabel lab0 lab1) (succs bb0)
      st <- get
      let cfg' = M.insert lab1 bb01 $ M.delete lab0 $ cfg st
      put (st {cfg = cfg'})
    else do
      -- TODO add some debug assert? like:
      -- case M.lookup (label bb0) (cfg st) of
      --   Nothing -> error "no such bb0 in cfg"
      let bb0' = bb0 {succs = FnBlock lab1 : succs bb0}
      let bb1' = bb1 {preds = FnBlock lab0 : preds bb1}
      st <- get
      let cfg' =
            M.insert lab0 bb0' $
              M.insert lab1 bb1' $
                cfg st
      put (st {cfg = cfg'})

addEntryEdgeTo :: Label -> Ident -> CFGM ()
addEntryEdgeTo lab fnname = do
  bb <- getBB lab
  let bb' = bb {preds = FnEntry fnname : preds bb}
  st <- get
  let cfg' = M.insert lab bb' $ cfg st
  put (st {cfg = cfg'})

addRetEdgeFrom :: Label -> CFGM ()
addRetEdgeFrom lab = do
  bb <- getBB lab
  let bb' = bb {succs = FnRet : succs bb}
  st <- get
  let cfg' = M.insert lab bb' $ cfg st
  put (st {cfg = cfg'})

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

procStmts :: Label -> [Stmt] -> CFGM [Label]
procStmts currLab [] = do
  currStmts <- takeCurrStmts
  putStmtsToBB currLab currStmts
  return [currLab]
procStmts currLab (stmt : t) =
  case stmt of
    (BStmt _ (Block _ stmts)) -> do
      -- BStmt can be either inlined into adjacent blocks or is
      -- handled by cond flow already
      procStmts currLab (stmts ++ t)
    s@(Ret _ _) -> handleRets s
    s@(VRet _) -> handleRets s
    s@(Cond _ _ condstmt) -> do
      addStmtToCurrBlock s
      currStmts <- takeCurrStmts
      putStmtsToBB currLab currStmts
      lab1 <- freshLabel
      addEdgeFromTo currLab lab1
      retLabs <- procStmts lab1 [condstmt]
      if null retLabs
        then -- there's no returning paths from the block, meaning
        -- we will never reach `t`
          return []
        else do
          lab <- freshLabel
          addEdgesFromTo (currLab : retLabs) lab
          procStmts lab t
    _else -> do
      addStmtToCurrBlock stmt
      procStmts currLab t
  where
    handleRets :: Stmt -> CFGM [Label]
    handleRets s = do
      addStmtToCurrBlock s
      currStmts <- takeCurrStmts
      putStmtsToBB currLab currStmts
      addRetEdgeFrom currLab
      return []

procBlock :: Block -> CFGM ()
procBlock (Block _ stmts) = do
  lab <- gets currLabel
  _ <- procStmts lab stmts
  return ()

-- TODO add entry node-label
procTopDef :: TopDef -> CFGM ()
procTopDef (FnDef _ _ fnname args block) = do
  lab <- gets currLabel
  addEntryEdgeTo lab fnname
  procBlock block

procProgram :: Program -> CFGM ()
procProgram (Program _ topdefs) = mapM_ procTopDef topdefs

runCFGM :: CFGM a -> (a, Store)
runCFGM m = runState m initStore
  where
    initStore =
      Store
        { cfg = M.empty,
          currStmts = [],
          currLabel = 0,
          lastLabel = 0,
          defs = M.empty
        }
    initBlock = 0

genCFG :: Program -> CFG
genCFG p =
  let (_, st) = runCFGM (procProgram p)
   in cfg st

-- TODO clean this monstrosity up
toDot :: CFG -> String
toDot cfg =
  "digraph {\n"
    ++ foldr (\(_, bb) acc -> bbToDot bb ++ "\n" ++ acc) [] (M.toList cfg)
    ++ "}"
  where
    printStmts :: [Stmt] -> String
    printStmts (Cond _ e _ : t) = "if (" ++ printTree e ++ ")" ++ if null t then "" else "\n" ++ printStmts t
    printStmts (stmt : t) = printTree stmt ++ if null t then "" else "\n" ++ printStmts t
    printStmts [] = ""
    pstr s =
      unpack
        ( replace (pack " ") (pack "\\ ") $
            replace (pack "{") (pack "\\{") $
              replace (pack "\n") (pack "\\l\\\n|") $
                replace (pack "}\n") (pack "\\}") $
                  replace (pack ">") (pack "\\>") $
                    replace (pack "<") (pack "\\<") $
                      pack (printStmts s)
        )
    showL :: Label -> String
    showL l = "L" ++ show l

    bbToDot :: BB -> String
    bbToDot bb =
      showL (label bb)
        ++ " [shape=record,style=filled,fillcolor=lightgrey,label=\""
        ++ "{"
        ++ showL (label bb)
        ++ "\n|"
        ++ (pstr . reverse) (stmts bb)
        ++ "\\l\\\n}\"];\n\n"
        ++ foldr (\s acc -> showL (label bb) ++ " -> " ++ show s ++ ";\n" ++ acc) [] (succs bb)
        ++ foldr (\p acc -> addOnlyEntry p (label bb) acc) [] (preds bb)
    addOnlyEntry :: Node -> Label -> String -> String
    addOnlyEntry fne@(FnEntry _) lab acc = show fne ++ " -> " ++ showL lab ++ ";\n"
    addOnlyEntry _ _ acc = acc
