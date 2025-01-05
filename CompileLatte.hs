{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE StrictData #-}

module Main where

import AbsLatte
import CFG
import Control.Monad (foldM, when)
import Control.Monad.Except
  ( ExceptT,
    MonadError (throwError),
    catchError,
    runExceptT,
  )
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader
  ( MonadReader (ask, local),
    ReaderT,
    asks,
    runReaderT,
  )
import Control.Monad.State
  ( MonadState (get),
    StateT,
    gets,
    runStateT,
  )
import Control.Monad.State.Lazy (modify)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import GHC.IO.Handle.FD (stderr)
import Helper
import LexLatte (Token, mkPosToken)
import ParLatte (myLexer, pProgram)
import PrintLatte (printTree)
import SSA
import SkelLatte ()
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn)
import TypeCheckLatte
import Prelude hiding (lookup)
import TransformAbsToFIR (genFIR)

type Err = Either String

type ParseFun a = [Token] -> Err a

type Loc = Int

data Value = IntV Integer | StrV String | BoolV Bool | VoidV deriving (Show)

type Store = Map Loc Value

data VP = Var Loc | Fn {declPos :: BNFC'Position, retType :: Type, fnEnv :: Env, args :: [Arg], block :: Block} deriving (Show)

type Env = Map Ident VP

type RuntimeError = RuntimeError' BNFC'Position

data RuntimeError' a
  = -- | Thrown when block ended without an explicit return from function when expected
    NoReturnError
      -- | error position
      a
      -- | function identifier
      Ident
  | -- | Thrown when error() is thrown in the program
    RuntimeError
      -- | throw position
      a
  | -- | Division by zero error
    DivByZero
      -- | error position
      a
  | -- | Thrown when no valid main() was found
    MainNotFound
  | -- | Error type wrapper for statement pretty printing
    StmtError
      -- | statement in which runtime error error was thrown
      Stmt
      -- | the actual runtime error
      RuntimeError
  | -- | Thrown when interpreter enters an invalid state, because
    -- typechecker gave a false positive
    TypeCheckerFalsePositive

instance Show RuntimeError where
  show (NoReturnError p fn) = "no return from function " ++ show fn ++ " found while expected at " ++ at p
  show (RuntimeError p) = "thrown at " ++ at p
  show (DivByZero p) = "division by zero at " ++ at p
  show MainNotFound = "\nmain() not found"
  show (StmtError stmt err) = "in statement:\n" ++ printStmt stmt ++ "\n" ++ show err
  show TypeCheckerFalsePositive = "\nType checker false positive. This should not happen..."

type IM a = ExceptT RuntimeError (StateT Store (ReaderT Env IO)) a

lookupValue :: Loc -> IM Value
lookupValue l = do gets (fromJust . M.lookup l)

lookupLoc :: Ident -> IM Loc
lookupLoc var = do
  env <- ask
  case M.lookup var env of
    Just (Var l) -> return l
    _othr -> throwError TypeCheckerFalsePositive

addToNewLoc :: Value -> IM Loc
addToNewLoc v = do
  st <- get
  let l = M.size st
  modify (M.insert l v)
  return l

unpackInt :: Expr -> IM Integer
unpackInt e = do
  v <- evalExpr e
  case v of
    IntV x -> return x
    _othr -> throwError TypeCheckerFalsePositive

unpackBool :: Expr -> IM Bool
unpackBool e = do
  v <- evalExpr e
  case v of
    BoolV b -> return b
    _othr -> throwError TypeCheckerFalsePositive

mapInt :: (Integer -> Integer) -> Expr -> IM Value
mapInt f e = do
  n <- unpackInt e
  return (IntV (f n))

mapBool :: (Bool -> Bool) -> Expr -> IM Value
mapBool f e = do
  b <- unpackBool e
  return (BoolV (f b))

mapStr :: (String -> String) -> Expr -> IM Value
mapStr f e = do
  v <- evalExpr e
  case v of
    StrV x -> return (StrV (f x))
    _othr -> throwError TypeCheckerFalsePositive

evalExpr :: Expr -> IM Value
evalExpr (EVar _ var) = lookupLoc var >>= lookupValue
evalExpr (ELitInt _ int) = return (IntV int)
evalExpr (ELitTrue _) = return (BoolV True)
evalExpr (ELitFalse _) = return (BoolV False)
evalExpr (EApp _ (Ident "printInt") [e]) = do
  (IntV i) <- evalExpr e
  liftIO $ print i
  return VoidV
evalExpr (EApp _ (Ident "printString") [e]) = do
  (StrV str) <- evalExpr e
  liftIO $ putStrLn str
  return VoidV
evalExpr (EApp _ (Ident "readInt") []) = do
  input <- liftIO getLine
  return (IntV $ read input)
evalExpr (EApp _ (Ident "readString") []) = do
  input <- liftIO getLine
  return (StrV input)
evalExpr (EApp p (Ident "error") []) = do
  throwError (RuntimeError p)
evalExpr (EApp _ idt exprs) = do
  env <- ask
  case M.lookup idt env of
    Just fn -> do
      env'' <- foldM addArgToEnv (M.insert idt fn (fnEnv fn)) (zip exprs (args fn))
      res <- local (const env'') (evalBlock (block fn))
      case (retType fn, res) of
        (Void _, _) -> return VoidV
        (_, Returned resv) -> return resv
        (_, _) -> throwError (NoReturnError (declPos fn) idt)
    _othr -> throwError TypeCheckerFalsePositive
  where
    addArgToEnv :: Env -> (Expr, Arg) -> IM Env
    addArgToEnv env (e, Arg _ _ argname) = do
      -- perform a copy of expr's value and insert it to a new loc
      l' <- evalExpr e >>= addToNewLoc
      return (M.insert argname (Var l') env)
evalExpr (EString _ str) = return (StrV str)
evalExpr (Neg _ e) = mapInt negate e
evalExpr (Not _ e) = mapBool not e
evalExpr (EMul p e1 (Div _) e2) =
  do
    n1 <- unpackInt e1
    n2 <- unpackInt e2
    if n2 == 0
      then throwError (DivByZero p)
      else return (IntV (div n1 n2))
evalExpr (EMul _ e1 op e2) =
  do
    n1 <- unpackInt e1
    n2 <- unpackInt e2
    return (IntV (f n1 n2))
  where
    f = case op of
      (Times _) -> (*)
      (Mod _) -> mod
evalExpr (EAdd _ e1 (Plus _) e2) =
  do
    v1 <- evalExpr e1
    case v1 of
      StrV s1 -> mapStr (s1 ++) e2
      IntV n1 -> mapInt (n1 +) e2
      _othr -> throwError TypeCheckerFalsePositive
evalExpr (EAdd _ e1 (Minus _) e2) =
  do
    n1 <- unpackInt e1
    mapInt (n1 -) e2
evalExpr (ERel _ e1 op e2) =
  do
    v1 <- evalExpr e1
    v2 <- evalExpr e2
    case (v1, v2) of
      (IntV n1, IntV n2) -> return (BoolV (f n1 n2))
      (StrV s1, StrV s2) -> return (BoolV (f s1 s2))
      (_, _) -> throwError TypeCheckerFalsePositive
  where
    f :: (Ord a) => a -> a -> Bool
    f = case op of
      LTH _ -> (<)
      LE _ -> (<=)
      GTH _ -> (>)
      GE _ -> (>=)
      EQU _ -> (==)
      NE _ -> (/=)
evalExpr (EAnd _ e1 e2) = do
  b1 <- unpackBool e1
  mapBool (b1 &&) e2
evalExpr (EOr _ e1 e2) = do
  b1 <- unpackBool e1
  mapBool (b1 ||) e2

-- | Tells whether execution flow ended with an explicit return
-- statement or not
data Result = Returned Value | Cont Env

evalBlock :: Block -> IM Result
evalBlock (Block _ stmts) = evalStmts stmts

evalStmts :: [Stmt] -> IM Result
evalStmts (h : t) = do
  res <- catchError (evalStmt h) (handler h)
  case res of
    Cont env -> local (const env) (evalStmts t)
    v -> return v
  where
    handler :: Stmt -> RuntimeError -> IM Result
    handler stmt err = throwError (StmtError stmt err)
evalStmts [] = do asks Cont

evalFnDef :: TopDef -> IM Env
evalFnDef (FnDef p ret fn args bl) = do
  env <- ask
  -- env doesn't yet contain anything about this fn,
  -- it must be mapped during application to make recursion possible
  asks (M.insert fn (Fn p ret env args bl))

passEnv :: Env -> IM Result
passEnv env = return (Cont env)

returnValue :: Value -> IM Result
returnValue val = return (Returned val)

evalItem :: Type -> Item -> IM Env
evalItem tp item = do
  (idt, v) <- idValue
  l <- addToNewLoc v
  asks (M.insert idt (Var l))
  where
    idValue :: IM (Ident, Value)
    idValue =
      case item of
        NoInit _ idt -> return (idt, defaultValue)
        Init _ idt e -> do
          v <- evalExpr e
          return (idt, v)
    defaultValue = case tp of
      Int _ -> IntV 0
      Str _ -> StrV ""
      Bool _ -> BoolV False
      _othr -> error "Should never happen"

evalStmt :: Stmt -> IM Result
evalStmt (Ret _ e) = evalExpr e >>= returnValue
evalStmt (VRet _) =
  -- returning Voidt is a bit artificial, but helps with error catching
  returnValue VoidV
evalStmt (Cond _ e st) = do
  BoolV b <- evalExpr e
  if b then evalStmt st else ask >>= passEnv
evalStmt (CondElse _ e st1 st2) = do
  BoolV b <- evalExpr e
  if b then evalStmt st1 else evalStmt st2
evalStmt (While p e st) = do
  BoolV b <- evalExpr e
  if b
    then do
      _ <- evalStmt st
      evalStmt (While p e st)
    else ask >>= passEnv
evalStmt stmt = evalStmt' stmt >>= passEnv
  where
    evalStmt' :: Stmt -> IM Env
    evalStmt' (Empty _) = ask
    evalStmt' (Decl _ tp items) = do
      -- TODO again, same note as in TC
      mapM_ (evalItem tp) items
      ask
    evalStmt' (Ass _ var e) = do
      l <- lookupLoc var
      v <- evalExpr e
      modify (M.insert l v)
      ask
    evalStmt' (SExp _ e) = evalExpr e >> ask
    evalStmt' _ = error "todo"

evalTopDefs :: [TopDef] -> IM Env
evalTopDefs (h : t) = do
  env' <- evalFnDef h
  local (const env') (evalTopDefs t)
evalTopDefs [] = ask

evalProgram :: Program -> IM ()
evalProgram (Program _ tds) = do
  env <- evalTopDefs tds
  case M.lookup (Ident "main") env of
    (Just (Fn _ _ env' _ block)) -> do
      _ <- local (const env') (evalBlock block)
      return ()
    _otherwise -> throwError MainNotFound

interpret :: Int -> Program -> IO ()
interpret v p = do
  (res, st) <- runReaderT (runStateT (runExceptT (evalProgram p)) M.empty) M.empty
  case res of
    Left runtimeErr -> do
      hPutStrLn stderr ("Runtime error " ++ show runtimeErr)
      exitFailure
    Right _ -> do
      putStrV v (show st)

runFile :: Verbosity -> ParseFun Program -> FilePath -> IO ()
runFile v p f = putStrV v f >> readFile f >>= run v p

run :: Verbosity -> ParseFun Program -> String -> IO ()
run v p s =
  case p ts of
    Left err -> do
      hPutStrLn stderr ("ERROR\n" ++ err)
      putStrV v "\n Tokens:"
      mapM_ (putStrV v . showPosToken . mkPosToken) ts
      exitFailure
    Right tree -> do
      putStrV v "Parse Successful!"
      compileProgram v tree
  where
    ts = myLexer s
    showPosToken ((l, c), t) = concat [show l, ":", show c, "\t", show t]

-- instance (Show (FIRTranslationError' a)) where
--   show _ = ""

compileProgram :: Int -> Program -> IO ()
compileProgram v tree = do
  putStrV v $ "[Abstract Syntax]\n" ++ show tree
  putStrV v $ "[Linearized tree]\n" ++ printTree tree
  tcinfo <- typeCheckProgram v tree
  -- putStrV v $ "[FIR]\n" ++ show (transformAbsToFIR tree)
  cfgs <- genCFGs tcinfo tree
  putStrV v $ "[CFGs]\n" ++ show cfgs
  let fircfgs = genFIR cfgs
  putStrV v $ "[FIRCFGs]\n" ++ show fircfgs
  ssacfgs <- toSSA fircfgs
  putStrV v $ "[SSACFGs]\n" ++ show ssacfgs
  when (v == 1) $ putStrLn $ toDot cfgs
  when (v == 2) $ putStrLn $ toDot fircfgs
  when (v == 3) $ putStrLn $ toDot ssacfgs

usage :: IO ()
usage = do
  putStrLn $
    unlines
      [ "usage: Call with one of the following argument combinations:",
        "  --help          Display this help message.",
        "  (no arguments)  Parse stdin verbosely.",
        "  (files)         Parse content of files verbosely.",
        "  -s (files)      Silent mode. Parse content of files silently.",
        "  -g (files)      Print CFG in DOT format.",
        "  -f (files)      Print FIRCFG in DOT format.",
        "  -S (files)      Print SSACFG in DOT format."
      ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> getContents >>= run 5 pProgram
    "-s" : fs -> mapM_ (runFile 0 pProgram) fs
    "-g" : fs -> mapM_ (runFile 1 pProgram) fs
    "-f" : fs -> mapM_ (runFile 2 pProgram) fs
    "-S" : fs -> mapM_ (runFile 3 pProgram) fs
    fs -> mapM_ (runFile 5 pProgram) fs
