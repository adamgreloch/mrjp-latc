{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TypeCheckLatte (typeCheckProgram) where

import AbsLatte
import Control.Monad.Except
  ( ExceptT,
    MonadError (throwError),
    catchError,
    runExceptT,
  )
import Control.Monad.Reader
  ( MonadReader (ask, local),
    Reader,
    asks,
    runReader,
  )
import Data.Either (isLeft)
import Data.List (nubBy)
import Data.Map (Map)
import Data.Map qualified as M
import GHC.IO.Handle.FD (stderr)
import Helper
import System.Exit (exitFailure)
import System.IO (hPutStrLn)
import Prelude hiding (lookup)
import Common

type TypeError = TypeError' BNFC'Position

data TypeError' a
  = -- | Thrown when block ended without an explicit return from function when expected
    NoReturnError
      -- | error position
      a
      -- | function identifier
      Ident
  | -- | Undefined variable error
    UndefinedVar
      -- | error position
      a
      -- | variable identifier
      Ident
  | -- | Undefined function error
    UndefinedFn
      -- | error position
      a
      -- | function identifier
      Ident
  | -- | Thrown when the same identifier is declared twice in one block
    NameNotUniqueInBlock
      -- | error position
      a
      -- | variable/function identifier
      Ident
      -- | position of previous declaration
      a
  | -- | Thrown when the same identifier is used at least
    -- twice in function's declaration of arguments
    ArgNameNotUniqueInFnDecl
      -- | error position
      a
      -- | function identifier
      Ident
  | -- | Thrown in case of a type mismatch
    TypeMismatch
      -- | encountered type
      Type
      -- | expected (inferred) type
      Type
  | -- | Thrown when encountered a boolean type in a situation
    -- where it's illegal
    UnexpectedBoolType
      -- | error position
      a
  | -- | Thrown in case a return statement type differs from
    -- function's declared return type
    RetTypeMismatch
      -- | encountered return type
      Type
      -- | expected return type
      Type
  | -- | Thrown when function is used like a variable
    FnUsedAsVar
      -- | error position
      a
      -- | function identifier
      Ident
      -- | function declaration position
      a
  | -- | Thrown when variable is used like a function
    VarUsedAsFn
      -- | error position
      a
      -- | variable identifier
      Ident
      -- | variable declaration position
      a
  | -- | Thrown when applied wrong number of arguments to a function
    SigArgCountMismatch
      -- | error position
      a
      -- | function identifier
      Ident
      -- | encountered argument count
      Int
      -- | function declaration position
      a
      -- | expected argument count
      Int
  | -- | Thrown when some encountered argument type differs from expected type
    -- during function application
    SigTypeMismatch
      -- | error position
      a
      -- | function identifier
      Ident
      -- | encountered argument type
      Type
      -- | expected declared argument type
      Type
  | -- | Thrown when main() has non-zero number of arguments
    BadMainSig
      -- | error position
      a
      -- | number of encountered arguments in declaration
      Int
  | -- | Thrown when main() return type differs from int
    BadMainRetType
      -- | error position
      a
      -- | encountered type
      Type
  | -- | Error type wrapper for statement pretty printing
    StmtError
      -- | statement in which type error error was thrown
      Stmt
      -- | the actual type error
      TypeError
  | -- | Error type wrapper for TopDef (FnDef) pretty printing
    TopDefError
      -- | TopDef in which type error error was thrown
      TopDef
      -- | the actual type error
      TypeError
  | -- | Something really bad happened. Fix your code
    UnexpectedError

type TC a = ExceptT TypeError (Reader TEnv) a

type VPType = VPType' BNFC'Position

data VPType' a = TVar a Type | TFn a Type [Arg] deriving (Show)

instance HasPosition (VPType' BNFC'Position) where
  hasPosition vpt = case vpt of
    TVar p _ -> p
    TFn p _ _ -> p

-- TODO make this tuple a datatype
type TEnv = (Ident, Type, BNFC'Position, Map Ident VPType)

type Ret = Either TEnv Type

data Value = IntV Integer | StrV String | BoolV Bool | VoidV deriving (Show)

type ConstOrVarType = ExprType' BNFC'Position

-- | If an expression consists of constants or can be short circuited
-- to one, the ExprType will be a Const. Otherwise, it is a Var
data ExprType' a = Const a Value | Var (Type' a)

initTEnv :: TEnv
initTEnv =
  ( Ident "main",
    Void nop,
    BNFC'NoPosition,
    foldr
      addPredefinedFun
      M.empty
      [ ("printString", Void nop, [Arg nop (Str nop) (Ident "v")]),
        ("printInt", Void nop, [Arg nop (Int nop) (Ident "v")]),
        ("error", Void nop, []),
        ("readInt", Int nop, []),
        ("readString", Str nop, [])
      ]
  )
  where
    addPredefinedFun :: (String, Type, [Arg]) -> Map Ident VPType -> Map Ident VPType
    addPredefinedFun (fnname, ret, args) = M.insert (Ident fnname) (TFn nop ret args)
    nop = BNFC'NoPosition

lookup :: Ident -> TEnv -> Maybe VPType
lookup idt (_, _, _, mp) = M.lookup idt mp

insert :: Ident -> VPType -> TEnv -> TEnv
insert idt vpt (fnidt, ret, bp, mp) = (fnidt, ret, bp, M.insert idt vpt mp)

setRetType :: Type -> TEnv -> TEnv
setRetType ret (fnidt, _, bp, mp) = (fnidt, ret, bp, mp)

setBlockPos :: BNFC'Position -> TEnv -> TEnv
setBlockPos bp (fnidt, ret, _, mp) = (fnidt, ret, bp, mp)

blockPos :: TEnv -> BNFC'Position
blockPos (_, _, bp, _) = bp

nextRetType :: TEnv -> Type
nextRetType (_, ret, _, _) = ret

instance Show TypeError where
  show (NoReturnError p fn) = "no return from function " ++ show fn ++ " found while expected from its signature at " ++ at p
  show (UndefinedVar p var) = "undefined variable " ++ show var ++ " at " ++ at p
  show (UndefinedFn p fn) = "undefined function " ++ show fn ++ " at " ++ at p
  show (NameNotUniqueInBlock p idt p') = "redefinition of name " ++ show idt ++ " at " ++ at p ++ " that was already declared in that block at " ++ at p'
  show (ArgNameNotUniqueInFnDecl p fn) = "argument names for function " ++ show fn ++ " declared at " ++ at p ++ " are not unique"
  show (TypeMismatch found expected) = "expected " ++ typeFrom expected ++ " but got " ++ typeAt found
  show (RetTypeMismatch found expected) = "expected to return " ++ typeFrom expected ++ " but got " ++ typeAt found
  show (FnUsedAsVar p fn p') = "function " ++ show fn ++ " previously declared at " ++ at p' ++ " used as a variable at " ++ at p
  show (VarUsedAsFn p var p') = "variable " ++ show var ++ " previously declared at " ++ at p' ++ " used as a function at " ++ at p
  show (BadMainSig p n) = at p ++ ": main has " ++ show n ++ " argument(s) but should have 0"
  show (BadMainRetType p t) = at p ++ ": main has return type " ++ show t ++ " but should have int"
  show (SigTypeMismatch _ fn tp extp) = "signature type mismatch for function " ++ show fn ++ ". Got " ++ typeAt tp ++ ", but expected " ++ typeFrom extp
  show (SigArgCountMismatch p fn n p' exn) = "passed " ++ show n ++ " argument(s) to function " ++ show fn ++ " at " ++ at p ++ ", but expected " ++ show exn ++ " as declared at " ++ at p'
  show (StmtError stmt err) = "in statement:\n" ++ printStmt stmt ++ "\n" ++ show err
  show (TopDefError td err) = "in function:\n" ++ printTopDef td ++ "\n" ++ show err
  show (UnexpectedBoolType p) = "unexpected boolean at " ++ at p
  show UnexpectedError = "Unexpected typechecker error. This should not happen..."

getType :: ConstOrVarType -> Type
getType (Var tp) = tp
getType (Const p (IntV _)) = Int p
getType (Const p (BoolV _)) = Bool p
getType (Const p (StrV _)) = Str p
getType (Const p VoidV) = Void p

typeCheckExpr :: Expr -> TC ConstOrVarType
typeCheckExpr (EVar p var) = do
  env <- ask
  case lookup var env of
    (Just (TVar _ tp)) -> return (Var tp)
    (Just (TFn p' _ _)) -> throwError (FnUsedAsVar p var p')
    Nothing -> throwError (UndefinedVar p var)
typeCheckExpr (ELitInt p int) = return (Const p (IntV int))
typeCheckExpr (ELitTrue p) = return (Const p (BoolV True))
typeCheckExpr (ELitFalse p) = return (Const p (BoolV False))
typeCheckExpr (EApp p fn exprs) = do
  env <- ask
  case lookup fn env of
    (Just (TVar p' _)) -> throwError (VarUsedAsFn p fn p')
    Nothing -> throwError (UndefinedFn p fn)
    (Just (TFn p' ret args)) ->
      if length exprs == length args
        then do
          mapM_ typeCheckArgs (zip exprs args)
          return (Var ret)
        else throwError (SigArgCountMismatch p fn (length exprs) p' (length args))
  where
    typeCheckArgs :: (Expr, Arg) -> TC ()
    typeCheckArgs (e, arg) = do
      ctp <- typeCheckExpr e
      let extp = argType arg
      let tp = getType ctp
      if extp ~ tp
        then return ()
        else throwError (SigTypeMismatch p fn tp extp)
typeCheckExpr (EString p _) = return (Var (Str p))
typeCheckExpr (Neg p e) = expectType (Int p) e
typeCheckExpr (Not p e) = expectType (Bool p) e
typeCheckExpr (EMul _ e1 op e2) =
  case op of
    (Times _) -> expectIntBinOp e1 (*) e2
    (Div _) -> expectIntBinOp e1 div e2
    (Mod _) -> expectIntBinOp e1 mod e2
typeCheckExpr (EAdd _ e1 (Minus _) e2) = expectIntBinOp e1 (-) e2
-- TODO compile-time const addition evaluation
-- strings get in a way a bit for now (implementation detail)
typeCheckExpr (EAdd _ e1 (Plus _) e2) = expectSameNotBoolType e1 e2
typeCheckExpr (ERel p e1 op e2) = do
  do
    v1 <- typeCheckExpr e1
    v2 <- typeCheckExpr e2
    case (v1, v2) of
      -- FIXME prooobaably could be done better
      (Const _ (IntV n1), Const _ (IntV n2)) -> return (Const p (BoolV (f n1 n2)))
      (Const _ (StrV s1), Const _ (StrV s2)) -> return (Const p (BoolV (f s1 s2)))
      (Const _ (BoolV b1), Const _ (BoolV b2)) -> return (Const p (BoolV (f b1 b2)))
      (_, _) -> do
        let (tp1, tp2) = (getType v1, getType v2)
        if tp1 ~ tp2
          then return (Var (Bool p))
          else throwError (TypeMismatch tp1 tp2)
  where
    f :: (Ord a) => a -> a -> Bool
    f = case op of
      LTH _ -> (<)
      LE _ -> (<=)
      GTH _ -> (>)
      GE _ -> (>=)
      EQU _ -> (==)
      NE _ -> (/=)
typeCheckExpr (EAnd p e1 e2) = shortCircuit False p e1 e2
typeCheckExpr (EOr p e1 e2) = shortCircuit True p e1 e2

-- | Short circuit if at least one expr is const b
shortCircuit :: Bool -> BNFC'Position -> Expr -> Expr -> TC ConstOrVarType
shortCircuit b p e1 e2 = do
  ctp1 <- typeCheckExpr e1
  ctp2 <- typeCheckExpr e2
  _ <- assertSameTypes p ctp1 ctp2
  case (ctp1, ctp2) of
    (Const _ (BoolV v), _) | v == b -> return (Const p (BoolV b))
    (_, Const _ (BoolV v)) | v == b -> return (Const p (BoolV b))
    (_, _) -> return (Var (Bool p))

expectSameNotBoolType :: Expr -> Expr -> TC ConstOrVarType
expectSameNotBoolType e1 e2 = do
  t <- expectSameType e1 e2
  case getType t of
    (Bool p) -> throwError (UnexpectedBoolType p)
    _otherwise -> return t

assertSameTypes :: BNFC'Position -> ConstOrVarType -> ConstOrVarType -> TC ConstOrVarType
assertSameTypes p ctp1 ctp2 = do
  let (tp1, tp2) = (getType ctp1, getType ctp2)
  if tp1 ~ tp2
    then return (Var (Bool p))
    else throwError (TypeMismatch tp1 tp2)

expectSameType :: Expr -> Expr -> TC ConstOrVarType
expectSameType e1 e2 = do
  tp1 <- typeCheckExpr e1
  expectType (getType tp1) e2

-- expectType2 :: Type -> Expr -> Expr -> TC ConstOrVarType
-- expectType2 extp e1 e2 = do
--   _ <- expectType extp e1
--   expectType extp e2

expectIntBinOp :: Expr -> (Integer -> Integer -> Integer) -> Expr -> TC ConstOrVarType
expectIntBinOp e1 op e2 = do
  ctp1 <- expectType int e1
  ctp2 <- expectType int e2
  case (ctp1, ctp2) of
    (Const p (IntV v1), Const _ (IntV v2)) -> return (Const p (IntV (op v1 v2)))
    (_, _) -> return ctp2
  where
    int = Int BNFC'NoPosition

expectType :: Type -> Expr -> TC ConstOrVarType
expectType extp e = do
  ctp <- typeCheckExpr e
  let tp = getType ctp
  if extp ~ tp
    then return ctp
    else throwError (TypeMismatch tp extp)

expectUniqueIdent :: BNFC'Position -> Ident -> TC ()
expectUniqueIdent p idt = do
  env <- ask
  case lookup idt env of
    Nothing -> return ()
    Just vpt ->
      let p' = hasPosition vpt
       in if p' < blockPos env
            then return ()
            else throwError (NameNotUniqueInBlock p idt p')

expectIdentType :: BNFC'Position -> Ident -> Type -> TC Ret
expectIdentType p idt extp = do
  env <- ask
  case lookup idt env of
    (Just (TVar _ tp)) ->
      if extp ~ tp
        then asks Left
        else throwError (TypeMismatch tp extp)
    (Just (TFn p' _ _)) -> throwError (FnUsedAsVar p idt p')
    Nothing -> throwError (UndefinedVar p idt)

verifyNextRetType :: Type -> TC Ret
verifyNextRetType tp = do
  env <- ask
  let extp = nextRetType env
  if extp ~ tp
    then return (Right tp)
    else throwError (RetTypeMismatch tp extp)

typeCheckProgram :: Int -> Program -> IO ()
typeCheckProgram v (Program _ tds) = do
  putStrV v "\n[Type check]\n"
  case runReader (runExceptT (typeCheckTopDefs tds)) initTEnv of
    (Left te) -> do
      hPutStrLn stderr ("ERROR\nType check error " ++ show te)
      exitFailure
    (Right tenv) -> do
      hPutStrLn stderr "OK\n"
      putStrV v (show tenv)

unique :: [Arg] -> Bool
unique args = length args == length (nubBy eq args)
  where
    eq a1 a2 = argName a1 == argName a2

checkIfMain :: TopDef -> TC ()
checkIfMain (FnDef p ret fn args _)
  | fn /= Ident "main" = return ()
  | not (null args) = throwError (BadMainSig p (length args))
  | not $ ret ~ Int BNFC'NoPosition = throwError (BadMainRetType p ret)
  | otherwise = return ()

addFnDefToEnv :: TopDef -> TC TEnv
addFnDefToEnv fnd@(FnDef p ret fn args _) = do
  checkIfMain fnd
  if not $ unique args
    then throwError (ArgNameNotUniqueInFnDecl p fn)
    else do
      asks (insert fn (TFn p ret args))

typeCheckFnDef :: TopDef -> TC TEnv
typeCheckFnDef fnd@(FnDef p expret fn args b) = do
  checkIfMain fnd
  if not $ unique args
    then throwError (ArgNameNotUniqueInFnDecl p fn)
    else do
      env <- ask -- Assumes FnDef is already in the env
      ret <- local (const $ setRetType expret $ addArgsToTEnv env) (typeCheckBlock b)
      if isLeft ret && not (expret ~ Void BNFC'NoPosition)
        then throwError (NoReturnError p fn)
        else return env -- Assumes typeCheckBlock already checked all the return types
  where
    addArgsToTEnv :: TEnv -> TEnv
    addArgsToTEnv tenv = foldr (\arg acc -> insert (argName arg) (TVar p (argType arg)) acc) tenv args

expectItemType :: BNFC'Position -> Type -> Item -> TC TEnv
expectItemType p extp item =
  case item of
    (NoInit _ var) -> do
      expectUniqueIdent p var
      asks (insert var (TVar p extp))
    (Init _ var e) -> do
      expectUniqueIdent p var
      ctp <- typeCheckExpr e
      let tp = getType ctp
      if extp ~ tp
        then asks (insert var (TVar p tp))
        else throwError (TypeMismatch tp extp)

typeCheckTopDefs :: [TopDef] -> TC TEnv
typeCheckTopDefs tds = do
  -- FnDef is the only TopDef possible
  env' <- readerSeq addFnDefToEnv tds
  local (const env') (readerSeq (\a -> catchError (typeCheckFnDef a) (handler a)) tds)
  where
    handler td err = throwError (TopDefError td err)

typeCheckBlock :: Block -> TC Ret
typeCheckBlock (Block p stmts) =
  local (setBlockPos p) (typeCheckStmts stmts)

typeCheckStmts :: [Stmt] -> TC Ret
typeCheckStmts stmts = do
  readerEitherSeq (\st -> catchError (typeCheckStmt st) (handler st)) stmts
  where
    handler stmt err = throwError (StmtError stmt err)

typeCheckStmt :: Stmt -> TC Ret
typeCheckStmt (Empty _) = asks Left
typeCheckStmt (BStmt _ b) = typeCheckBlock b
typeCheckStmt (Decl p tp items) = Left <$> readerSeq (expectItemType p tp) items
typeCheckStmt (Ass p idt e) = typeCheckExpr e >>= expectIdentType p idt . getType
typeCheckStmt (Incr p idt) = expectIdentType p idt (Int p)
typeCheckStmt (Decr p idt) = expectIdentType p idt (Int p)
typeCheckStmt (Ret _ e) = typeCheckExpr e >>= verifyNextRetType . getType
typeCheckStmt (VRet _) = verifyNextRetType (Void BNFC'NoPosition)
typeCheckStmt (Cond p be s) = do
  ctp <- expectType (Bool p) be
  ret <- typeCheckStmt s
  case ctp of
    (Const _ (BoolV True)) -> return ret
    _else -> asks Left
typeCheckStmt (CondElse p be s1 s2) = do
  ctp <- expectType (Bool p) be
  ret1 <- typeCheckStmt s1
  ret2 <- typeCheckStmt s2
  case ctp of
    (Const _ (BoolV val)) ->
      if val
        then return ret1
        else return ret2
    _else ->
      ( case (ret1, ret2) of
          (Right a, Right b) | a ~ b -> return ret1
          _else -> asks Left
      )
typeCheckStmt (While p be s) = do
  _ <- expectType (Bool p) be
  typeCheckStmt s
typeCheckStmt (SExp _ e) = do
  _ <- typeCheckExpr e
  asks Left
