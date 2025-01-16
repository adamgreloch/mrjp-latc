{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NamedFieldPuns #-}

module CFGDefs where

import AbsLatte (Ident (..), Type)
import Data.Bifunctor qualified
import Data.List (find)
import Data.Map qualified as M

data Label = Entry | BlockLabel Int | JumpLabel Int deriving (Eq, Ord)

instance (Show Label) where
  show Entry = "Entry"
  show (BlockLabel n) = "L" ++ show n
  show (JumpLabel n) = "J" ++ show n

type SLoc = Int

data When = WhenTrue | WhenFalse | WhenLoop | WhenDone deriving (Eq)

instance Show When where
  show WhenTrue = "True"
  show WhenFalse = "False"
  show WhenLoop = "Loop"
  show WhenDone = "Done"

data Node = FnEntry Ident | FnBlock Label | FnRet Ident deriving (Eq)

instance Show Node where
  show (FnEntry (Ident s)) = "FnEntry_" ++ s
  show (FnBlock l) = show l
  show (FnRet (Ident s)) = "FnRet_" ++ s

type Bindings = M.Map Ident [SLoc]

data Def = DArg Type Label | DVar Type Label | DFun Type [(Type, Ident)] deriving (Show)

type Defs = M.Map SLoc Def

data BB' a = BB'
  { label :: Label,
    stmts :: a,
    preds :: [Node],
    succs :: [(Node, When)],
    bindings :: Bindings
  }
  deriving (Show)

type CFG' a = M.Map Label (BB' a)

type CFGsNoDefs' a = M.Map Ident (CFG' a)

data Opt = CSE deriving (Show, Eq)

data CFGInfo = CFGInfo
  { cfgInfoBindings :: Bindings,
    cfgInfoDefs :: Defs,
    opts :: [Opt]
  }
  deriving (Show)

type CFGs' a = (CFGsNoDefs' a, CFGInfo)

setOptWhen :: Bool -> Opt -> CFGs' a -> CFGs' a
setOptWhen True opt (cnd, info) = (cnd, info {opts = opt : opts info})
setOptWhen False _ cfgs = cfgs

succWhen :: When -> BB' a -> Maybe Label
succWhen when bb = extractLabel =<< find isBlock (succs bb)
  where
    isBlock :: (Node, When) -> Bool
    isBlock (FnBlock _, w) = w == when
    isBlock _ = False

    extractLabel :: (Node, When) -> Maybe Label
    extractLabel (FnBlock l, _) = Just l
    extractLabel nw = error $ "FnBlock expected but got: " ++ show nw

succDone :: BB' a -> Maybe Label
succDone = succWhen WhenDone

succTrue :: BB' a -> Maybe Label
succTrue = succWhen WhenTrue

succFalse :: BB' a -> Maybe Label
succFalse = succWhen WhenFalse

emptyBB :: Label -> BB' [a]
emptyBB lab = BB' {label = lab, stmts = [], preds = [], succs = [], bindings = M.empty}

lookupBB :: Label -> CFG' [a] -> BB' [a]
lookupBB lab cfg = do
  case M.lookup lab cfg of
    Just bb -> bb
    Nothing -> emptyBB lab

replaceRefToLabel :: Label -> Label -> Node -> CFG' [a] -> CFG' [a]
replaceRefToLabel labFrom labTo (FnBlock lab) cfg =
  let bb = lookupBB lab cfg
   in let bb' = bb {preds = map repl (preds bb), succs = map (Data.Bifunctor.first repl) (succs bb)}
       in M.insert lab bb' cfg
  where
    repl :: Node -> Node
    repl n@(FnBlock l) = if l == labFrom then FnBlock labTo else n
    repl n = n
replaceRefToLabel _ _ _ cfg = cfg

startBB :: CFG' a -> BB' a
startBB cfg = snd (M.findMin cfg)

deleteBB :: BB' a -> CFG' a -> CFG' a
deleteBB bb = M.delete (label bb)

insertBB :: BB' a -> CFG' a -> CFG' a
insertBB bb = M.insert (label bb) bb

reverseCode :: BB' [a] -> BB' [a]
reverseCode bb = bb {stmts = reverse (stmts bb)}

getSuccs :: BB' a -> [Label]
getSuccs bb = justBlocks $ succs bb
  where
    justBlocks :: [(Node, When)] -> [Label]
    justBlocks ((FnBlock lab1, _) : t) = lab1 : justBlocks t
    justBlocks (_ : t) = justBlocks t
    justBlocks [] = []

getSuccsAsBB :: BB' [a] -> CFG' [a] -> [BB' [a]]
getSuccsAsBB bb cfg = map (`lookupBB` cfg) $ justBlocks $ succs bb
  where
    justBlocks :: [(Node, When)] -> [Label]
    justBlocks ((FnBlock lab1, _) : t) = lab1 : justBlocks t
    justBlocks (_ : t) = justBlocks t
    justBlocks [] = []
