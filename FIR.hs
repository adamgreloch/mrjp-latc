{-# LANGUAGE StrictData #-}

module FIR where

import AbsLatte
import Common (Printable (printCode))
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
data VType = VInt | VStr | VBool | VVoid deriving (Eq)

instance Show VType where
  show VInt = "I"
  show VStr = "S"
  show VBool = "B"
  show VVoid = "V"

data Addr = Cmp Int | Var Ident Int | Temp Int

instance Show Addr where
  show (Cmp i) = "%cmp_" ++ show i
  show (Var (Ident s) i) = "%" ++ s ++ show i
  show (Temp i) = "%t" ++ show i

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
  | LLabel (Maybe Label)
  | LString String

instance Show Loc where
  show (LImmInt i) = show i
  show (LImmBool b) = show b
  show (LAddr tp addr) = show addr ++ "(" ++ show tp ++ ")"
  show (LLabel lab) = case lab of Nothing -> "L?"; (Just l) -> show lab

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
type Code = [Instr]

instance Printable Code where
  printCode :: Code -> String
  printCode (i : t) =
    ( case i of
        instr -> show instr
    )
      ++ if null t then "" else "\n" ++ printCode t

data TopDefFIR = FnDefFIR String Code

instance (Show TopDefFIR) where
  show (FnDefFIR s code) =
    "\n" ++ s ++ foldr (\op acc -> "\n\t" ++ show op ++ acc) "\n" (reverse code)

type ProgramFIR = [TopDefFIR]

type Label = Int

data Store = Store_ {code :: Code, locs :: Map Ident Loc, lastTemp :: Int, lastLabel :: Label}
  deriving (Show)

class Emittable a where
  emit :: (MonadState Store m) => a -> m ()

-- | Unary operands (Loc := Op1 Loc or Loc Op1 Loc)
data Op1
  = Br
  | Asgn
  | Not
  | Neg
  deriving (Show)

-- | Binary operands (Loc := Loc Op2 Loc)
data Op2
  = Add
  | Sub
  | Mul
  | Div
  | Mod
  | Load
  | Store
  | CondBr
  | LTh
  | LEq
  | GTh
  | GEq
  | Eq
  | NEq
  | And
  | Or
  deriving (Show)

data Instr
  = Bin Op2 Loc Loc Loc
  | Unar Op1 Loc Loc
  | Call Loc Ident [Loc]
  | IRet Loc
  | IRetVoid
  | ILabel Label
  deriving (Show)

instance (Emittable Code) where
  emit c = modify (\st -> st {code = c ++ code st})

instance (Emittable Instr) where
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
