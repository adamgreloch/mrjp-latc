module TransformAbsToFIR
  ( transformAbsToFIR,
    FIRTranslationError',
  )
where

import AbsLatte
import Common
import Control.Monad.Except
  ( ExceptT,
    MonadError (throwError),
    runExceptT,
  )
import Control.Monad.Reader
  ( MonadReader (ask, local),
    Reader,
    asks,
    runReader,
  )
import Control.Monad.State
  ( MonadState (get, put),
    StateT,
    gets,
    modify,
    runStateT,
  )
import Data.Map (Map)
import Data.Map qualified as M
import FIR

data FIRTranslationError' a
  = UnexpectedError a
  | UncaughtFrontendErr String
  deriving (Show)

type FIRTranslationError = FIRTranslationError' BNFC'Position

type Env = Map Ident SLoc

type GenM a = ExceptT FIRTranslationError (StateT Store (Reader Env)) a

newSLoc :: GenM SLoc
newSLoc = gets (M.size . locs)

freshTemp :: GenM Addr
freshTemp = do
  st <- get
  let fresh = lastTemp st + 1
  put (st {lastTemp = fresh})
  return fresh

getLoc :: Ident -> GenM Loc
getLoc idt = do
  env <- ask
  case M.lookup idt env of
    Just sloc -> do
      st <- get
      maybe onErr return (M.lookup sloc (locs st))
    Nothing -> onErr
  where
    onErr :: GenM Loc
    onErr = throwError (UncaughtFrontendErr "No such location")

maybeGetLoc :: Ident -> GenM (Maybe Loc)
maybeGetLoc idt = do
  env <- ask
  case M.lookup idt env of
    Just sloc -> do
      st <- get
      maybe onErr (return . Just) (M.lookup sloc (locs st))
    Nothing -> return Nothing
  where
    onErr :: GenM (Maybe Loc)
    onErr = throwError (UncaughtFrontendErr "No such location")

genExp :: Expr -> GenM Loc
genExp (ELitInt _ n) = return (LImmInt (fromIntegral n))
-- rough example

-- TODO we will probably want to store the expression depth
-- and emit based on temp usage (to maintain log(n))
genExp (EAdd _ e1 (Plus _) e2) = do
  loc1 <- genExp e1
  loc2 <- genExp e2
  tmp <- freshTemp
  emit $ BinOp tmp Add loc1 loc2
  return (LAddr (typeOfLoc loc1) tmp)
genExp (EVar _ id) = getLoc id

genStmt :: Stmt -> GenM Env
genStmt (Decl _ tp items) = do
  readerSeq declareItem items
  where
    declareItem :: Item -> GenM Env
    declareItem (NoInit _ idt) = do
      env <- ask
      sloc <- newSLoc
      modify (\st -> st {locs = M.insert sloc (LImmInt 0) (locs st)})
      return $ M.insert idt sloc env
    declareItem (Init _ idt e) = do
      loc <- genExp e
      -- TODO assert expr type of loc is the same as vtp
      env <- ask
      sloc <- newSLoc
      modify (\st -> st {locs = M.insert sloc loc (locs st)})
      return $ M.insert idt sloc env
genStmt (Ass _ idt e) = do
  loc <- genExp e
  idloc <- getLoc idt
  case idloc of
    (LAddr _ addr) -> emit $ Store loc addr
    _otherwise -> throwError (UncaughtFrontendErr "Assigning to non-addr")
  ask
genStmt (SExp _ e) = do
  _ <- genExp e
  ask
genStmt (VRet _) = do
  emit RetVoid
  ask
genStmt (AbsLatte.Ret _ e) = do
  loc <- genExp e
  emit $ FIR.Ret loc
  ask

genBlock :: Block -> GenM Code
genBlock (Block _ stmts) = do
  _ <- readerSeq genStmt stmts
  takeCode

genTopDefFIR :: TopDef -> GenM TopDefFIR
genTopDefFIR (FnDef _ _ (Ident s) args block) = do
  env' <- readerSeq addArg args
  code <- local (const env') (genBlock block)
  -- FIXME No emit here?
  return (FnDefFIR s code)
  where
    addArg :: Arg -> GenM Env
    addArg (Arg _ tp argid@(Ident argname)) = do
      st <- get
      sloc <- newSLoc
      put (st {locs = M.insert sloc (LArg (toVType tp) argname) (locs st)})
      asks (M.insert argid sloc)

genProgramFIR :: Program -> GenM ProgramFIR
genProgramFIR (Program _ topdefs) = mapM genTopDefFIR topdefs

runGenM :: GenM a -> (Either FIRTranslationError a, Store)
runGenM m = runReader (runStateT (runExceptT m) newStore) M.empty
  where
    newStore = Store_ {locs = M.empty, lastTemp = 0, code = []}

transformAbsToFIR :: Program -> (Either FIRTranslationError ProgramFIR, Store)
transformAbsToFIR p = runGenM (genProgramFIR p)
