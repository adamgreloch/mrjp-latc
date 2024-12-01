{-# LANGUAGE StrictData #-}

module FIR where

import AbsLatte
import Control.Monad.State
  ( MonadState (get, put),
    modify,
  )
import Data.Map (Map)
import Data.Map qualified as M

-- This is a first-level, linear IR that mirrors LLVM IR
-- Goals:
--  1. CFG should be derivable out of this (CT 4.4.4)
--  2. Later on, also some variable definition/use dependence graph

-- Regarding dependecy graph:
-- vertices = Locs/addrs?

-- | Note: String cannot be an Imm, since it has to be allocated
data VType = VInt | VStr | VBool | VVoid deriving (Show)

data Addr = Cmp Int | Var Ident Int | Temp Int deriving (Show)

data Loc
  = -- | immediate integer literal
    LImmInt Int
  | -- | immediate boolean literal
    LImmBool Bool
  | -- | address of a temporary register (i.e. LAddr 1 ~> %loc_i)
    LAddr VType Addr
  | -- | indicates that the identifier is bound to a function with a return type
    LFun VType
  | -- | current function argument (i.e. LArg "foo" ~> %arg_foo)
    LArg VType String
  deriving (Show)

typeOfLoc :: Loc -> VType
typeOfLoc l = case l of
  (LImmInt _) -> VInt
  (LImmBool _) -> VBool
  (LAddr tp _) -> tp
  (LFun tp) -> tp
  (LArg tp _) -> tp

toVType :: Type -> VType
toVType tp =
  case tp of
    (Int _) -> VInt
    (Str _) -> VStr
    (Bool _) -> VBool
    (Void _) -> VVoid
    (Fun {}) -> error "should not need to check the fn type"

type SLoc = Int

type AddrTypes = Map Addr VType

-- TODO: code will probably need to be more structured to differentiate basic blocks
type Code = [Op]

data TopDefFIR = FnDefFIR String Code

instance (Show TopDefFIR) where
  show (FnDefFIR s code) =
    "\n" ++ s ++ foldr (\op acc -> "\n\t" ++ show op ++ acc) "\n" (reverse code)

type ProgramFIR = [TopDefFIR]

type Label = Int

data BB = BB
  { label :: Label,
    stmts :: [Stmt],
    preds :: [BB],
    succs :: [BB]
  }
  deriving (Show)

type CFG = M.Map Label BB

newBB :: Label -> [Stmt] -> BB
newBB label stmts =
  BB {label, stmts, preds = [], succs = []}

addBlockToCFG :: (MonadState Store m) => BB -> m ()
addBlockToCFG bb = do
  st <- get
  put (st {cfg = M.insert (label bb) bb (cfg st)})
  return ()

addPred :: (MonadState Store m) => Label -> BB -> m ()
addPred label pred = do
  st <- get
  let g = cfg st
  case M.lookup label g of
    Nothing -> error "no block with such label in cfg"
    Just bb -> do
      let newbb = bb {preds = pred : preds bb}
      put (st {cfg = M.insert label bb g})
      return ()

data Store = Store_
  { locs :: Map SLoc Loc,
    lastTemp :: Int,
    lastLabel :: Label,
    code :: Code,
    cfg :: CFG
  }
  deriving (Show)

class Emittable a where
  emit :: (MonadState Store m) => a -> m ()

class Printable a where
  printCode :: a -> String

-- | Unary operands
data Op1
  = Call

-- | Binary operands
-- TODO add signed/unsigned
data Op2
  = Add
  | Sub
  | Mul
  | Div
  deriving (Show)

data Op
  = BinOp Addr Op2 Loc Loc
  | Load Addr Addr
  | Store Loc Addr
  | RetVoid
  | Ret Loc
  | Alloca Addr
  | EntryLabel
  | Label Int
  | CondBr Loc Label Label
  | Br Label
  deriving (Show)

data Meta
  = FnDecl String Code

instance (Emittable Code) where
  emit c = modify (\st -> st {code = c ++ code st})

instance (Emittable Meta) where
  emit _ = return ()

instance (Emittable Op) where
  emit o = modify (\st -> st {code = o : code st})

-- | Takes emmited code from Store and cleans Store.code
takeCode :: (MonadState Store m) => m Code
takeCode = do
  st <- get
  let res = code st
  put (st {code = []})
  return res

-- Printable needs to know type table
-- instance (Printable Op2) where
--   printCode op =
--     case op of
--       Add -> "add"
--       Sub -> "sub"
--       Mul -> "mul"
--       FIR.Div -> "div"
--
-- instance (Printable Op) where
--   printCode (BinOp a o l1 l2) = printCode a ++ " = " ++ printCode o ++ printCode l1 ++ printCode l2
