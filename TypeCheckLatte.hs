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
import Data.List (nubBy)
import Data.Map (Map)
import Data.Map qualified as M
import GHC.IO.Handle.FD (stderr)
import Helper
import System.Exit (exitFailure)
import System.IO (hPutStrLn)
import Prelude hiding (lookup)

type TypeError = TypeError' BNFC'Position

data TypeError' a
  = -- | Undefined variable error
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
  | -- | Something really bad happened. Fix your code
    UnexpectedError

type TC a = ExceptT TypeError (Reader TEnv) a

type VPType = VPType' BNFC'Position

data VPType' a = TVar a Type | TFn a Type [Arg] deriving (Show)

instance HasPosition (VPType' BNFC'Position) where
  hasPosition vpt = case vpt of
    TVar p _ -> p
    TFn p _ _ -> p

type TEnv = (Type, BNFC'Position, Map Ident VPType)

initTEnv :: TEnv
initTEnv =
  ( Void nop,
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
lookup idt (_, _, mp) = M.lookup idt mp

insert :: Ident -> VPType -> TEnv -> TEnv
insert idt vpt (ret, bp, mp) = (ret, bp, M.insert idt vpt mp)

setRetType :: Type -> TEnv -> TEnv
setRetType ret (_, bp, mp) = (ret, bp, mp)

setBlockPos :: BNFC'Position -> TEnv -> TEnv
setBlockPos bp (ret, _, mp) = (ret, bp, mp)

blockPos :: TEnv -> BNFC'Position
blockPos (_, bp, _) = bp

nextRetType :: TEnv -> Type
nextRetType (ret, _, _) = ret

readerSeq :: (MonadReader r m) => (a -> m r) -> [a] -> m r
readerSeq mf (h : t) = do
  env <- mf h
  local (const env) (readerSeq mf t)
readerSeq _ [] = ask

instance Show TypeError where
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
  show (UnexpectedBoolType p) = "unexpected boolean at " ++ at p
  show UnexpectedError = "Unexpected typechecker error. This should not happen..."

typeCheckExpr :: Expr -> TC Type
typeCheckExpr (EVar p var) = do
  env <- ask
  case lookup var env of
    (Just (TVar _ tp)) -> return tp
    (Just (TFn p' _ _)) -> throwError (FnUsedAsVar p var p')
    Nothing -> throwError (UndefinedVar p var)
typeCheckExpr (ELitInt p _) = return (Int p)
typeCheckExpr (ELitTrue p) = return (Bool p)
typeCheckExpr (ELitFalse p) = return (Bool p)
typeCheckExpr (EApp p fn exprs) = do
  env <- ask
  case lookup fn env of
    (Just (TVar p' _)) -> throwError (VarUsedAsFn p fn p')
    Nothing -> throwError (UndefinedFn p fn)
    (Just (TFn p' ret args)) ->
      if length exprs == length args
        then do
          mapM_ typeCheckArgs (zip exprs args)
          return ret
        else throwError (SigArgCountMismatch p fn (length args) p' (length exprs))
  where
    typeCheckArgs :: (Expr, Arg) -> TC ()
    typeCheckArgs (e, arg) = do
      tp <- typeCheckExpr e
      let extp = argType arg
      if extp ~ tp
        then return ()
        else throwError (SigTypeMismatch p fn tp extp)
typeCheckExpr (EString p _) = return (Str p)
typeCheckExpr (Neg p e) = expectType (Int p) e
typeCheckExpr (Not p e) = expectType (Bool p) e
typeCheckExpr (EMul p e1 _ e2) = expectType2 (Int p) e1 e2
typeCheckExpr (EAdd p e1 (Minus _) e2) = expectType2 (Int p) e1 e2
typeCheckExpr (EAdd _ e1 (Plus _) e2) = expectSameNotBoolType e1 e2
typeCheckExpr (ERel p e1 _ e2) = do
  _ <- expectSameType e1 e2
  return (Bool p)
typeCheckExpr (EAnd p e1 e2) = expectType2 (Bool p) e1 e2
typeCheckExpr (EOr p e1 e2) = expectType2 (Bool p) e1 e2

expectSameNotBoolType :: Expr -> Expr -> TC Type
expectSameNotBoolType e1 e2 = do
  t <- expectSameType e1 e2
  case t of
    (Bool p) -> throwError (UnexpectedBoolType p)
    _otherwise -> return t

expectSameType :: Expr -> Expr -> TC Type
expectSameType e1 e2 = do
  tp1 <- typeCheckExpr e1
  expectType tp1 e2

expectType2 :: Type -> Expr -> Expr -> TC Type
expectType2 extp e1 e2 = do
  _ <- expectType extp e1
  expectType extp e2

expectType :: Type -> Expr -> TC Type
expectType extp e = do
  tp <- typeCheckExpr e
  if extp ~ tp
    then return tp
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

expectIdentType :: BNFC'Position -> Ident -> Type -> TC TEnv
expectIdentType p idt extp = do
  env <- ask
  case lookup idt env of
    (Just (TVar _ tp)) ->
      if extp ~ tp
        then ask
        else throwError (TypeMismatch tp extp)
    (Just (TFn p' _ _)) -> throwError (FnUsedAsVar p idt p')
    Nothing -> throwError (UndefinedVar p idt)

verifyNextRetType :: Type -> TC TEnv
verifyNextRetType tp = do
  env <- ask
  let extp = nextRetType env
  if extp ~ tp
    then ask
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
addFnDefToEnv (FnDef p ret fn args b) = do
  checkIfMain (FnDef p ret fn args b)
  if not $ unique args
    then throwError (ArgNameNotUniqueInFnDecl p fn)
    else do
      asks (insert fn (TFn p ret args))

typeCheckFnDef :: TopDef -> TC TEnv
typeCheckFnDef (FnDef p ret fn args b) = do
  checkIfMain (FnDef p ret fn args b)
  if not $ unique args
    then throwError (ArgNameNotUniqueInFnDecl p fn)
    else do
      env <- ask -- Assumes that FnDef is already in the env
      _ <- local (const $ setRetType ret $ addArgsToTEnv env) (typeCheckBlock b)
      return env
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
      tp <- typeCheckExpr e
      if extp ~ tp
        then asks (insert var (TVar p tp))
        else throwError (TypeMismatch tp extp)

typeCheckTopDefs :: [TopDef] -> TC TEnv
typeCheckTopDefs tds = do
  -- FnDef is the only TopDef possible
  env' <- readerSeq addFnDefToEnv tds
  local (const env') (readerSeq typeCheckFnDef tds)

typeCheckBlock :: Block -> TC TEnv
typeCheckBlock (Block p stmts) =
  local (setBlockPos p) (typeCheckStmts stmts)

typeCheckStmts :: [Stmt] -> TC TEnv
typeCheckStmts stmts = do
  readerSeq (\st -> catchError (typeCheckStmt st) (handler st)) stmts
  where
    handler :: Stmt -> TypeError -> TC TEnv
    handler stmt err = throwError (StmtError stmt err)

typeCheckStmt :: Stmt -> TC TEnv
typeCheckStmt (Empty _) = ask
typeCheckStmt (BStmt _ b) = typeCheckBlock b
typeCheckStmt (Decl p tp items) = readerSeq (expectItemType p tp) items
typeCheckStmt (Ass p idt e) = typeCheckExpr e >>= expectIdentType p idt
typeCheckStmt (Incr p idt) = expectIdentType p idt (Int p)
typeCheckStmt (Decr p idt) = expectIdentType p idt (Int p)
typeCheckStmt (Ret _ e) = typeCheckExpr e >>= verifyNextRetType
typeCheckStmt (VRet _) = verifyNextRetType (Void BNFC'NoPosition)
typeCheckStmt (Cond p be s) = do
  _ <- expectType (Bool p) be
  typeCheckStmt s
typeCheckStmt (CondElse p be s1 s2) = do
  _ <- expectType (Bool p) be
  _ <- typeCheckStmt s1
  typeCheckStmt s2
typeCheckStmt (While p be s) = do
  _ <- expectType (Bool p) be
  typeCheckStmt s
typeCheckStmt (SExp _ e) = do
  _ <- typeCheckExpr e
  ask
