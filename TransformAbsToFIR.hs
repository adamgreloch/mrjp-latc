module TransformAbsToFIR
  ( FIRTranslationError',
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
    State,
    gets,
    modify,
    runState,
  )
import Data.Map (Map)
import Data.Map qualified as M
import FIR
import GHC.Base (assert)

data FIRTranslationError' a
  = UnexpectedError a
  | UncaughtFrontendErr String
  deriving (Show)

type FIRTranslationError = FIRTranslationError' BNFC'Position

type GenM a = State Store a

freshTemp :: GenM Addr
freshTemp = do
  st <- get
  let fresh = lastTemp st + 1
  put (st {lastTemp = fresh})
  return (Temp fresh)

freshLabel :: GenM Label
freshLabel = do
  st <- get
  let fresh = lastLabel st + 1
  put (st {lastLabel = fresh})
  return fresh

getLoc :: Ident -> GenM Loc
getLoc idt = do
  st <- get
  case M.lookup idt (locs st) of
    (Just loc) -> return loc
    Nothing -> error $ "no loc for " ++ show idt

genExp :: Expr -> GenM Loc
genExp (ELitInt _ n) = return (LImmInt (fromIntegral n))
-- rough example

-- TODO we will probably want to store the expression depth
-- and emit based on temp usage (to maintain log(n))
genExp (EAdd _ e1 (Plus _) e2) = do
  loc1 <- genExp e1
  loc2 <- genExp e2
  tmp <- freshTemp
  let locType = assert (typeOfLoc loc1 == typeOfLoc loc2) (typeOfLoc loc1)
  emit $ Bin Add (LAddr locType tmp) loc1 loc2
  return (LAddr (typeOfLoc loc1) tmp)
genExp (EVar _ id) = getLoc id
genExp (ELitTrue _) = return (LImmBool True)

example :: [Stmt]
example =
  [ Decl
      (Just (2, 3))
      (Int (Just (2, 3)))
      [ Init (Just (2, 7)) (Ident "a") (EAdd (Just (2, 11)) (ELitInt (Just (2, 11)) 4) (Plus (Just (2, 13))) (ELitInt (Just (2, 15)) 20))
      ],
    Decl
      (Just (3, 3))
      (Int (Just (3, 3)))
      [ Init (Just (3, 7)) (Ident "b") (EAdd (Just (3, 11)) (EVar (Just (3, 11)) (Ident "a")) (Plus (Just (3, 13))) (ELitInt (Just (3, 15)) 1))
      ],
    Decl
      (Just (4, 3))
      (Int (Just (4, 3)))
      [ Init (Just (4, 7)) (Ident "c") (EVar (Just (4, 11)) (Ident "a"))
      ],
    Ass (Just (5, 3)) (Ident "b") (EAdd (Just (5, 7)) (EVar (Just (5, 7)) (Ident "c")) (Plus (Just (5, 9))) (EVar (Just (5, 11)) (Ident "a"))),
    Ret (Just (6, 3)) (EVar (Just (6, 10)) (Ident "c"))
  ]

genStmts :: [Stmt] -> GenM ()
genStmts [] = return ()
genStmts (Decl _ tp items : t) = do
  mapM_ declareItem items
  genStmts t
  where
    declareItem :: Item -> GenM ()
    declareItem (NoInit _ idt) = do
      -- TODO extend for bool and string
      let vloc = LAddr VInt (Var idt 0)
      modify (\st -> st {locs = M.insert idt vloc (locs st)})
      emit $ Unar Asgn vloc (LImmInt 0)
    declareItem (Init _ idt e) = do
      loc <- genExp e
      let vloc = LAddr VInt (Var idt 0)
      modify (\st -> st {locs = M.insert idt vloc (locs st)})
      emit $ Unar Asgn vloc loc
genStmts (Ass _ idt e : t) = do
  let vloc = LAddr VInt (Var idt 0)
  modify (\st -> st {locs = M.insert idt vloc (locs st)})
  loc <- genExp e
  emit $ Unar Asgn vloc loc
  genStmts t
genStmts (SExp _ e : t) = do
  _ <- genExp e
  genStmts t
genStmts (VRet _ : t) = do
  emit IRetVoid
  genStmts t
genStmts (Ret _ e : t) = do
  loc <- genExp e
  emit $ IRet loc
  genStmts t
genStmts (BStmt _ b : t) = error "should never happen"
genStmts (Cond _ e s : t) = error "ee?"

runGenM :: GenM a -> (a, Store)
runGenM m = runState m initStore
  where
    initStore =
      Store_
        { lastLabel = 0,
          lastTemp = 0,
          code = [],
          locs = M.empty
        }

genFIR :: [Stmt] -> Code
genFIR stmts = let (_, st) = runGenM $ genStmts stmts in reverse (code st)

showCode :: Code -> String
showCode = foldr (\v acc -> show v ++ "\n" ++ acc) []
