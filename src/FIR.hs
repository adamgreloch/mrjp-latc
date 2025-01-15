{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StrictData #-}

module FIR where

import AbsLatte
import CFGDefs (Label)
import Common (Printable (printCode))
import Data.Map (Map)

data VType = VInt | VStr | VBool | VVoid | VLabel deriving (Eq, Ord)

instance Show VType where
  show VInt = "i32"
  show VStr = "i8*"
  show VBool = "i1"
  show VVoid = "void"
  show VLabel = "label"

data Addr = Cmp Int | Var Ident Int (Maybe Int) | ArgVar Ident | Temp Int deriving (Eq, Ord)

instance Show Addr where
  show (Cmp i) = "%cmp_" ++ show i
  show (Var (Ident s) src num) =
    "%"
      ++ s
      ++ "_"
      ++ show src
      ++ "_"
      ++ maybe "?" show num
  show (ArgVar (Ident s)) =
    "%" ++ s ++ "_0_0"
  show (Temp i) = "%t" ++ show i

data Loc
  = -- | immediate integer literal
    LImmInt Int
  | -- | immediate boolean literal
    LImmBool Bool
  | -- | address of a temporary register (i.e. LAddr 1 ~> %loc_i)
    LAddr VType Addr
  | LLabel (Maybe Label)
  | LString String
  deriving (Eq, Ord)

instance Show Loc where
  show (LImmInt i) = show i
  show (LImmBool True) = "1"
  show (LImmBool False) = "0"
  show (LAddr _ addr) = show addr
  show (LLabel lab) = "%" ++ maybe "?" show lab
  show (LString s) = '\"' : s ++ "\""

typeOfLoc :: Loc -> VType
typeOfLoc l = case l of
  (LImmInt _) -> VInt
  (LImmBool _) -> VBool
  (LAddr tp _) -> tp
  (LString _) -> VStr
  (LLabel _) -> VLabel

toVType :: Type -> VType
toVType tp =
  case tp of
    (Int _) -> VInt
    (Str _) -> VStr
    (Bool _) -> VBool
    (Void _) -> VVoid
    (Fun {}) -> error "should not need to check the fn type"

initValue :: VType -> Loc
initValue vtp =
  case vtp of
    VInt -> LImmInt 0
    VBool -> LImmBool False
    VStr -> LString ""
    _else -> error $ show vtp ++ " as init type?"

type AddrTypes = Map Addr VType

type Code = [Instr]

instance Printable Code where
  printCode :: Code -> String
  printCode (i : t) =
    ( case i of
        instr -> show instr
    )
      ++ if null t then "" else "\n" ++ printCode t
  printCode [] = ""

data TopDefFIR = FnDefFIR String Code

instance (Show TopDefFIR) where
  show (FnDefFIR s code) =
    "\n" ++ s ++ foldr (\op acc -> "\n\t" ++ show op ++ acc) "\n" (reverse code)

type ProgramFIR = [TopDefFIR]

-- | Unary operands (Loc := Op1 Loc or Loc Op1 Loc)
data Op1
  = Asgn
  | Not
  | Neg
  deriving (Show, Eq, Ord)

-- | Binary operands (Loc := Loc Op2 Loc)
data Op2
  = Add
  | Sub
  | Mul
  | Div
  | Mod
  | CondBr
  | LTh
  | LEq
  | GTh
  | GEq
  | Eq
  | NEq
  | And
  | Or
  deriving (Show, Eq, Ord)

data Instr
  = Bin Op2 Loc Loc Loc
  | Unar Op1 Loc Loc
  | Br Loc
  | Call Loc Ident [Loc]
  | IRet Loc
  | IRetVoid
  | ILabel Label
  | Phi Loc [(Label, Loc)]
  deriving (Show, Eq, Ord)

isRel :: Op2 -> Bool
isRel LTh = True
isRel LEq = True
isRel GTh = True
isRel GEq = True
isRel Eq = True
isRel NEq = True
isRel _ = False
