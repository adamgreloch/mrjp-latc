module TransformAbsToFIR
  ( FIRTranslationError',
    genFIR,
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
genExp (EVar _ id) = return (LAddr VInt (Var id 0))
genExp (ELitInt _ n) = return (LImmInt (fromIntegral n))
genExp (ELitTrue _) = return (LImmBool True)
genExp (ELitFalse _) = return (LImmBool False)
genExp (EApp _ idt exprs) = do
  tmp <- freshTemp
  -- TODO extend for other types
  let resLoc = LAddr VInt tmp
  locs <- mapM genExp exprs
  emit $ Call resLoc idt locs
  return resLoc
genExp (EString _ s) = return (LString s)
genExp (AbsLatte.Neg _ e) = do
  loc <- genExp e
  tmp <- freshTemp
  let retLoc = LAddr (typeOfLoc loc) tmp
  emit $ Unar FIR.Neg retLoc loc
  return retLoc
genExp (AbsLatte.Not _ e) = do
  loc <- genExp e
  tmp <- freshTemp
  let retLoc = LAddr (typeOfLoc loc) tmp
  emit $ Unar FIR.Not retLoc loc
  return retLoc

-- TODO we will probably want to store the expression depth
-- and emit based on temp usage (to maintain log(n))
genExp (EAdd _ e1 addOp e2) = do
  loc1 <- genExp e1
  loc2 <- genExp e2
  tmp <- freshTemp
  let locType = assert (typeOfLoc loc1 == typeOfLoc loc2) (typeOfLoc loc1)
  let retLoc = LAddr locType tmp
  emit $ Bin op retLoc loc1 loc2
  return retLoc
  where
    op = case addOp of
      (Plus _) -> Add
      (Minus _) -> Sub
genExp (EMul _ e1 mulOp e2) = do
  loc1 <- genExp e1
  loc2 <- genExp e2
  tmp <- freshTemp
  let locType = assert (typeOfLoc loc1 == typeOfLoc loc2) (typeOfLoc loc1)
  let resLoc = LAddr locType tmp
  emit $ Bin op resLoc loc1 loc2
  return resLoc
  where
    op = case mulOp of
      (Times _) -> Add
      (AbsLatte.Div _) -> FIR.Div
      (AbsLatte.Mod _) -> FIR.Mod
genExp (ERel _ e1 relOp e2) = do
  loc1 <- genExp e1
  loc2 <- genExp e2
  tmp <- freshTemp
  let resLoc = LAddr VBool tmp
  emit $ Bin op resLoc loc1 loc2
  return resLoc
  where
    op = case relOp of
      LTH _ -> LTh
      LE _ -> LEq
      GTH _ -> GTh
      GE _ -> GEq
      EQU _ -> Eq
      NE _ -> NEq
genExp (EAnd _ e1 e2) = do
  loc1 <- genExp e1
  loc2 <- genExp e2
  tmp <- freshTemp
  let resLoc = LAddr VBool tmp
  emit $ Bin And resLoc loc1 loc2
  return resLoc
genExp (EOr _ e1 e2) = do
  loc1 <- genExp e1
  loc2 <- genExp e2
  tmp <- freshTemp
  let resLoc = LAddr VBool tmp
  emit $ Bin Or resLoc loc1 loc2
  return resLoc

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

example1 :: [Stmt]
example1 =
  [ Cond
      (Just (8, 3))
      ( ERel
          (Just (8, 7))
          (EVar (Just (8, 7)) (Ident "n"))
          (LE (Just (8, 9)))
          (ELitInt (Just (8, 12)) 0)
      )
      ( BStmt
          (Just (8, 15))
          ( Block
              (Just (8, 15))
              [ Ret (Just (9, 5)) (ELitInt (Just (9, 12)) 0)
              ]
          )
      ),
    Ret
      (Just (11, 3))
      ( EAdd
          (Just (11, 10))
          ( EApp (Just (11, 10)) (Ident "f") [EAdd (Just (11, 12)) (EVar (Just (11, 12)) (Ident "n")) (Minus (Just (11, 13))) (ELitInt (Just (11, 14)) 1)]
          )
          (Plus (Just (11, 17)))
          (EVar (Just (11, 19)) (Ident "n"))
      )
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
  loc <- genExp e
  let vloc = LAddr VInt (Var idt 0)
  modify (\st -> st {locs = M.insert idt vloc (locs st)})
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
genStmts (Incr p idt : t) = do
  genExp (EAdd p (EVar p idt) (Plus p) (ELitInt p 1))
  genStmts t
genStmts (Decr p idt : t) = do
  genExp (EAdd p (EVar p idt) (Minus p) (ELitInt p 1))
  genStmts t

-- in control instructions we don't care about their
-- true/false bodies as these are a part of other blocks
-- the labels will be set later
genStmts (Cond _ e _ : t) = do
  loc <- genExp e
  emit $ Bin CondBr loc (LLabel Nothing) (LLabel Nothing)
  genStmts t
genStmts (CondElse _ e _ _ : t) = do
  loc <- genExp e
  emit $ Bin CondBr loc (LLabel Nothing) (LLabel Nothing)
  genStmts t
genStmts (While _ e _ : t) = do
  loc <- genExp e
  emit $ Bin CondBr loc (LLabel Nothing) (LLabel Nothing)
  genStmts t
genStmts (BStmt _ b : t) = error "should never happen"

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
genFIR stmts = let (_, st) = runGenM $ genStmts (reverse stmts) in code st
