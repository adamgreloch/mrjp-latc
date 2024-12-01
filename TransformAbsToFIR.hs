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

data Env = Env {slocs :: Map Ident SLoc, currBB :: Label}

type GenM a = ExceptT FIRTranslationError (StateT Store (Reader Env)) a

newSLoc :: GenM SLoc
newSLoc = gets (M.size . locs)

freshTemp :: GenM Addr
freshTemp = do
  st <- get
  let fresh = lastTemp st + 1
  put (st {lastTemp = fresh})
  return (Temp fresh)

freshVar :: Ident -> GenM Addr
freshVar idt = do
  env <- ask
  loc <- maybeGetLoc idt
  case loc of
    (Just (LAddr _ (Var _ n))) -> return (Var idt (n + 1))
    _else -> return (Var idt 0)

freshLabel :: GenM Label
freshLabel = do
  st <- get
  let fresh = lastLabel st + 1
  put (st {lastLabel = fresh})
  return fresh

maybeGetSLoc :: Ident -> GenM (Maybe SLoc)
maybeGetSLoc idt = asks (M.lookup idt . slocs)

getSLoc :: Ident -> GenM SLoc
getSLoc idt = do
  sl <- maybeGetSLoc idt
  maybe (error "no such idt") return sl

maybeGetLoc :: Ident -> GenM (Maybe Loc)
maybeGetLoc idt = do
  env <- ask
  sloc <- maybeGetSLoc idt
  case sloc of
    (Just n) -> gets (M.lookup n . locs)
    Nothing -> return Nothing

getLoc :: Ident -> GenM Loc
getLoc idt = do
  env <- ask
  sloc <- getSLoc idt
  st <- get
  maybe (error "no such sloc") return (M.lookup sloc (locs st))

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
genExp (ELitTrue _) = return (LImmBool True)

genStmts :: [Stmt] -> GenM Env
genStmts [] = ask
genStmts (Decl _ tp items : t) = do
  env' <- readerSeq declareItem items
  local (const env') (genStmts t)
  where
    declareItem :: Item -> GenM Env
    declareItem (NoInit _ idt) = do
      env <- ask
      sloc <- newSLoc
      modify (\st -> st {locs = M.insert sloc (LImmInt 0) (locs st)})
      mapIdtToSloc idt sloc
    declareItem (Init _ idt e) = do
      loc <- genExp e
      -- TODO assert expr type of loc is the same as vtp
      env <- ask
      sloc <- newSLoc
      modify (\st -> st {locs = M.insert sloc loc (locs st)})
      mapIdtToSloc idt sloc
genStmts (Ass _ idt e : t) = do
  loc <- genExp e
  sloc <- getSLoc idt
  modify (\st -> st {locs = M.insert sloc loc (locs st)})
  genStmts t
genStmts (BStmt _ b : t) = do
  code <- genBlock b
  emit code
  genStmts t
genStmts (SExp _ e : t) = do
  _ <- genExp e
  genStmts t
genStmts (VRet _ : t) = do
  emit RetVoid
  genStmts t
genStmts (AbsLatte.Ret _ e : t) = do
  loc <- genExp e
  emit $ FIR.Ret loc
  genStmts t
genStmts (Cond _ e s : t) = do
  loc <- genExp e
  lab1 <- freshLabel
  lab2 <- freshLabel
  emit $ CondBr loc lab1 lab2
  emit $ Label lab1
  _ <- genStmts [s]
  emit $ Br lab2
  emit $ Label lab2
  genStmts t

currBBLabel :: GenM Label
currBBLabel = asks currBB

mapIdtToSloc :: Ident -> SLoc -> GenM Env
mapIdtToSloc idt sloc = do
  env <- ask
  return $ env {slocs = M.insert idt sloc (slocs env)}

genBlock :: Block -> GenM Code
genBlock (Block _ stmts) = do
  _ <- genStmts stmts
  takeCode

genTopDefFIR :: TopDef -> GenM TopDefFIR
genTopDefFIR (FnDef _ _ (Ident s) args block) = do
  emit EntryLabel
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
      mapIdtToSloc argid sloc

genProgramFIR :: Program -> GenM ProgramFIR
genProgramFIR (Program _ topdefs) = mapM genTopDefFIR topdefs

runGenM :: GenM a -> (Either FIRTranslationError a, Store)
runGenM m = runReader (runStateT (runExceptT m) emptyStore) emptyEnv
  where
    emptyStore =
      Store_
        { locs = M.empty,
          lastTemp = 0,
          lastLabel = 0,
          code = [],
          cfg = M.empty
        }
    emptyEnv =
      Env
        { slocs = M.empty,
          currBB = 0
        }

transformAbsToFIR :: Program -> (Either FIRTranslationError ProgramFIR, Store)
transformAbsToFIR p = runGenM (genProgramFIR p)
