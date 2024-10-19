{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TypeCheckLatte (typeCheckProgram) where

import AbsLatte
import Control.Monad (when)
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
import PrintLatte
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
  | -- | Thrown when expression (r-value) is passed as a reference argument
    -- to a function
    RValuePassedAsRef
      -- | error position
      a
      -- | function identifier
      Ident
      -- | r-value passed
      Expr
      -- | function reference argument that got an r-value instead
      Arg
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
lookup id (_, _, mp) = M.lookup id mp

insert :: Ident -> VPType -> TEnv -> TEnv
insert id vpt (ret, bp, mp) = (ret, bp, M.insert id vpt mp)

setRetType :: Type -> TEnv -> TEnv
setRetType ret (_, bp, mp) = (ret, bp, mp)

setBlockPos :: BNFC'Position -> TEnv -> TEnv
setBlockPos bp (ret, _, mp) = (ret, bp, mp)

blockPos :: TEnv -> BNFC'Position
blockPos (_, bp, _) = bp

nextRetType :: TEnv -> Type
nextRetType (ret, _, _) = ret

instance Show TypeError where
  show (UndefinedVar p var) = "undefined variable " ++ show var ++ " at " ++ at p
  show (UndefinedFn p fn) = "undefined function " ++ show fn ++ " at " ++ at p
  show (NameNotUniqueInBlock p id p') = "redefinition of name " ++ show id ++ " at " ++ at p ++ " that was already declared in that block at " ++ at p'
  show (ArgNameNotUniqueInFnDecl p fn) = "argument names for function " ++ show fn ++ " declared at " ++ at p ++ " are not unique"
  show (TypeMismatch found expected) = "expected " ++ typeFrom expected ++ " but got " ++ typeAt found
  show (RetTypeMismatch found expected) = "expected to return " ++ typeFrom expected ++ " but got " ++ typeAt found
  show (FnUsedAsVar p fn p') = "function " ++ show fn ++ " previously declared at " ++ at p' ++ " used as a variable at " ++ at p
  show (VarUsedAsFn p var p') = "variable " ++ show var ++ " previously declared at " ++ at p' ++ " used as a function at " ++ at p
  show (BadMainSig p n) = at p ++ ": main has " ++ show n ++ " argument(s) but should have 0"
  show (BadMainRetType p t) = at p ++ ": main has return type " ++ show t ++ " but should have int"
  show (SigTypeMismatch p fn tp extp) = "signature type mismatch for function " ++ show fn ++ ". Got " ++ typeAt tp ++ ", but expected " ++ typeFrom extp
  show (SigArgCountMismatch p fn n p' exn) = "passed " ++ show n ++ " argument(s) to function " ++ show fn ++ " at " ++ at p ++ ", but expected " ++ show exn ++ " as declared at " ++ at p'
  show (StmtError stmt err) = "in statement:\n" ++ printStmt stmt ++ "\n" ++ show err
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
typeCheckExpr (EAdd p e1 (Plus _) e2) = expectSameNotBoolType e1 e2
typeCheckExpr (ERel p e1 _ e2) = do
  expectSameNotBoolType e1 e2
  return (Bool p)
typeCheckExpr (EAnd p e1 e2) = expectType2 (Bool p) e1 e2
typeCheckExpr (EOr p e1 e2) = expectType2 (Bool p) e1 e2

expectSameNotBoolType :: Expr -> Expr -> TC Type
expectSameNotBoolType e1 e2 = do
  t <- expectSameType e1 e2
  case t of
    (Bool p) -> throwError (UnexpectedBoolType p)
    _ -> return t

expectSameType :: Expr -> Expr -> TC Type
expectSameType e1 e2 = do
  tp1 <- typeCheckExpr e1
  expectType tp1 e2

expectType2 :: Type -> Expr -> Expr -> TC Type
expectType2 extp e1 e2 = do
  expectType extp e1
  expectType extp e2

expectType :: Type -> Expr -> TC Type
expectType extp e = do
  tp <- typeCheckExpr e
  if extp ~ tp
    then return tp
    else throwError (TypeMismatch tp extp)

expectUniqueIdent :: BNFC'Position -> Ident -> TC ()
expectUniqueIdent p id = do
  env <- ask
  case lookup id env of
    Nothing -> return ()
    Just vpt ->
      let p' = hasPosition vpt
       in if p' < blockPos env
            then return ()
            else throwError (NameNotUniqueInBlock p id p')

typeCheckProgram :: Int -> Program -> IO ()
typeCheckProgram v (Program _ tds) = do
  putStrV v "\n[Type check]\n"
  case runReader (runExceptT (typeCheckTopDefs tds)) initTEnv of
    (Left te) -> do
      hPutStrLn stderr ("Type check error " ++ show te)
      exitFailure
    (Right tenv) -> putStrV v ("Type check passed:\n" ++ show tenv)

unique :: [Arg] -> Bool
unique args = length args == length (nubBy eq args)
  where
    eq a1 a2 = argName a1 == argName a2

checkIfMain :: TopDef -> TC ()
checkIfMain (FnDef p ret fn args b)
  | fn /= Ident "main" = return ()
  | not (null args) = throwError (BadMainSig p (length args))
  | not $ ret ~ Int BNFC'NoPosition = throwError (BadMainRetType p ret)
  | otherwise = return ()

typeCheckFnDef :: TopDef -> TC TEnv
typeCheckFnDef (FnDef p ret fn args b) = do
  checkIfMain (FnDef p ret fn args b)
  if not $ unique args
    then throwError (ArgNameNotUniqueInFnDecl p fn)
    else do
      env' <- asks (insert fn (TFn p ret args))
      local (const $ setRetType ret $ addArgsToTEnv args env') (typeCheckBlock b)
  where
    addArgsToTEnv :: [Arg] -> TEnv -> TEnv
    addArgsToTEnv args tenv = foldr (\arg acc -> insert (argName arg) (TVar p (argType arg)) acc) tenv args

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
typeCheckTopDefs (h : t) = do
  -- FnDef is the only TopDef possible
  env' <- typeCheckFnDef h
  local (const env') (typeCheckTopDefs t)
typeCheckTopDefs [] = ask

typeCheckBlock :: Block -> TC TEnv
typeCheckBlock (Block p stmts) =
  local (setBlockPos p) (typeCheckStmts stmts)

typeCheckStmts :: [Stmt] -> TC TEnv
typeCheckStmts (h : t) = do
  env <- catchError (typeCheckStmt h) (handler h)
  local (const env) (typeCheckStmts t)
  where
    handler :: Stmt -> TypeError -> TC TEnv
    handler stmt err = throwError (StmtError h err)
typeCheckStmts [] = ask

typeCheckStmt :: Stmt -> TC TEnv
typeCheckStmt (Empty _) = ask
typeCheckStmt (Decl p tp items) = do
  -- TODO check if this does what i think it does
  expectItemTypes p tp items
    where
      expectItemTypes p tp (h:t) = do
        env' <- expectItemType p tp h
        local (const env') (expectItemTypes p tp t)
      expectItemTypes p tp [] = ask
typeCheckStmt (Ass p id e) = do
  tp <- typeCheckExpr e
  env <- ask
  case lookup id env of
    (Just (TVar p' extp)) ->
      if extp ~ tp
        then ask
        else throwError (TypeMismatch tp extp)
    (Just (TFn p' _ _)) -> throwError (FnUsedAsVar p id p')
    Nothing -> throwError (UndefinedVar p id)
typeCheckStmt (Ret _ e) = do
  env <- ask
  let extp = nextRetType env
  tp <- typeCheckExpr e
  if extp ~ tp
    then ask
    else throwError (RetTypeMismatch tp extp)
typeCheckStmt (VRet _) = do
  env <- ask
  let extp = nextRetType env
  if extp ~ void
    then ask
    else throwError (RetTypeMismatch void extp)
  where
    void = Void BNFC'NoPosition
typeCheckStmt (Cond p be s) = do
  expectType (Bool p) be
  typeCheckStmt s
  ask
typeCheckStmt (CondElse p be s1 s2) = do
  expectType (Bool p) be
  typeCheckStmt s1
  typeCheckStmt s2
  ask
typeCheckStmt (While p be s) = do
  expectType (Bool p) be
  typeCheckStmt s
  ask
typeCheckStmt (SExp _ e) = do
  typeCheckExpr e
  ask
