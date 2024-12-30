module CFGDefs where

import AbsLatte (Ident (..), Type)
import Data.List (find)
import Data.Map qualified as M

type Label = Int

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
  show (FnBlock l) = "L" ++ show l
  show (FnRet (Ident s)) = "FnRet_" ++ s

type Bindings = M.Map Ident SLoc

data Def = DVar Type Label | DFun Type deriving (Show)

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

data CFGInfo = CFGInfo
  { cfgInfoBindings :: Bindings,
    cfgInfoDefs :: Defs
  } deriving (Show)

type CFGs' a = (CFGsNoDefs' a, CFGInfo)

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
