module CFGDefs
where

import AbsLatte (Ident (..), Stmt)
import Data.Map qualified as M
import Data.List (find)

type Label = Int

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

data BB' a = BB'
  { label :: Label,
    stmts :: a,
    preds :: [Node],
    succs :: [(Node, When)]
  }
  deriving (Show)

type CFG' a = M.Map Label (BB' a)

type CFGs' a = M.Map Ident (CFG' a)



succWhen :: When -> BB' a -> Maybe Label
succWhen when bb = (\(FnBlock l, b) -> Just l) =<< find isBlock (succs bb)
  where
    isBlock :: (Node, When) -> Bool
    isBlock (FnBlock _, w) = w == when
    isBlock _ = False

succDone :: BB' a -> Maybe Label
succDone = succWhen WhenDone

succTrue :: BB' a -> Maybe Label
succTrue = succWhen WhenTrue

succFalse :: BB' a -> Maybe Label
succFalse = succWhen WhenFalse
