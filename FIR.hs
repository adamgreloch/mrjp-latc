{-# LANGUAGE StrictData #-}

module FIR where

import AbsLatte
import CFGDefs (Bindings, Defs, Label)
import Common (Printable (printCode))
import Control.Monad.State
  ( MonadState (get, put),
    modify,
  )
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Set (Set)

data VType = VInt | VStr | VBool | VVoid deriving (Eq, Ord)

instance Show VType where
  show VInt = "I"
  show VStr = "S"
  show VBool = "B"
  show VVoid = "V"

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
    "%" ++ s
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
  show (LImmBool b) = show b
  show (LAddr tp addr) = show addr ++ "(" ++ show tp ++ ")"
  show (LLabel lab) = "%L" ++ maybe "?" show lab
  show (LString s) = '\"' : s ++ "\""

typeOfLoc :: Loc -> VType
typeOfLoc l = case l of
  (LImmInt _) -> VInt
  (LImmBool _) -> VBool
  (LAddr tp _) -> tp
  (LString _) -> VStr
  (LLabel _) -> error "request type of label?"

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

data FIRStore = FIRStore_
  { code :: Code,
    locs :: Map Ident Loc,
    lastTemp :: Int,
    lastLabel :: Label,
    blockLabel :: Label,
    blockBindings :: Bindings,
    globalBindings :: Bindings,
    defs :: Defs,

    -- | helps retrieving appropriate binding in cases like
    -- int a = 2; // a_1
    -- {
    --   a = a + 1 // this is still a_1
    --   int a = 2; // a_2
    --   ...
    -- }
    definedAlready :: Map Label (Set Ident) 
  }
  deriving (Show)

class Emittable a where
  emit :: (MonadState FIRStore m) => a -> m ()

-- | Unary operands (Loc := Op1 Loc or Loc Op1 Loc)
data Op1
  = Asgn
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
  | Br Loc
  | Call Loc Ident [Loc]
  | IRet Loc
  | IRetVoid
  | ILabel Label
  | Phi Loc [(Label, Loc)]
  deriving (Show)

instance (Emittable Code) where
  emit c = modify (\st -> st {code = c ++ code st})

instance (Emittable Instr) where
  emit o = modify (\st -> st {code = o : code st})

-- | Takes emmited code from FIRStore and cleans FIRStore.code
takeCode :: (MonadState FIRStore m) => m Code
takeCode = do
  st <- get
  let res = code st
  put (st {code = []})
  return res
