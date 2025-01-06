module TransformAbsToFIR (genFIR) where

import AbsLatte
import CFGDefs
import Control.Monad (unless)
import Control.Monad.State
  ( MonadState (get, put),
    State,
    gets,
    modify,
    runState,
  )
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import FIR
import GHC.Base (assert)

data FIRStore = FIRStore_
  { code :: Code,
    locs :: Map Ident Loc,
    lastJumpLabel :: Label,
    lastTemp :: Int,
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

type GenM a = State FIRStore a

class Emittable a where
  emit :: (MonadState FIRStore m) => a -> m ()

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

freshTemp :: GenM Addr
freshTemp = do
  st <- get
  let fresh = lastTemp st + 1
  put (st {lastTemp = fresh})
  return (Temp fresh)

freshJumpLabel :: GenM Label
freshJumpLabel = do
  st <- get
  case lastJumpLabel st of
    JumpLabel n -> do
      let fresh = JumpLabel (n + 1)
      put (st {lastJumpLabel = fresh})
      return fresh
    _else -> error "why"

genExp :: Expr -> GenM Loc
genExp (EVar _ idt) = getVarLocFromBinding idt
genExp (ELitInt _ n) = return (LImmInt (fromIntegral n))
genExp (ELitTrue _) = return (LImmBool True)
genExp (ELitFalse _) = return (LImmBool False)
genExp (EApp _ idt exprs) = do
  tp <- getFnRetTypeFromBinding idt
  locs <- mapM genExp exprs
  tmp <- freshTemp
  let resLoc = LAddr tp tmp
  emit $ Call resLoc idt locs
  return resLoc
genExp (EString _ s) = return (LString s)
genExp (AbsLatte.Neg _ e) = do
  loc <- genExp e
  tmp <- freshTemp
  let retLoc = LAddr (typeOfLoc loc) tmp
  emit $ Bin Sub retLoc (LImmInt 0) loc
  return retLoc
genExp (AbsLatte.Not _ e) = do
  loc <- genExp e
  tmp <- freshTemp
  let retLoc = LAddr (typeOfLoc loc) tmp
  emit $ Bin Eq retLoc loc (LImmBool False)
  return retLoc

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

-- For short-circuiting purposes, meeting LLVM SSA requirements and leaving
-- CFG at all readable the following compromise has been made: the BB
-- is identified with `BlockLabel` labels and it can nest blocks
-- marked with `JumpLabel`. These blocks are created in EAnd and EOr generators
-- below and are ignored by CFG. We also put phis by hand since it is easy.
-- Creating a new BB just to short-circuit would make things too messy.
genExp (EAnd _ e1 e2) = genShortCircuit e1 e2 True
genExp (EOr _ e1 e2) = genShortCircuit e1 e2 False

genShortCircuit :: Expr -> Expr -> Bool -> GenM Loc
genShortCircuit e1 e2 nextIfTrue = do
  blockLab <- gets blockLabel
  loc1 <- genExp e1
  labNext <- freshJumpLabel
  labSkip <- freshJumpLabel
  let (onTrue, onFalse) = if nextIfTrue then (labNext, labSkip) else (labSkip, labNext)
  emit $ Bin CondBr loc1 (LLabel (Just onTrue)) (LLabel (Just onFalse))
  emit $ ILabel labNext
  loc2 <- genExp e2
  emit $ Br (LLabel (Just labSkip))
  emit $ ILabel labSkip
  tmp <- freshTemp
  let resLoc = LAddr VBool tmp
  emit $ Phi resLoc [(blockLab, loc1), (labNext, loc2)]
  return resLoc

wasDefinedInBlock :: Ident -> GenM Bool
wasDefinedInBlock idt = do
  st <- get
  case M.lookup (blockLabel st) (definedAlready st) of
    Nothing -> return False
    Just s -> return $ S.member idt s

defineInBlock :: Ident -> GenM ()
defineInBlock idt = do
  st <- get
  currLab <- gets blockLabel
  let da = definedAlready st
  let s = M.findWithDefault S.empty currLab da
  put (st {definedAlready = M.insert currLab (S.insert idt s) da})

-- TODO cleanup these accessors
getVarLocFromBinding :: Ident -> GenM Loc
getVarLocFromBinding idt = do
  st <- get
  case M.lookup idt (blockBindings st) of
    Just slocs -> findProperLoc slocs
    Nothing -> error $ "block binding not found: " ++ show idt ++ "\nall bindings: " ++ show (blockBindings st)
  where
    findProperLoc :: [SLoc] -> GenM Loc
    findProperLoc (sloc : t) = do
      st <- get
      case M.lookup sloc (defs st) of
        -- we are before SSA conversion, so the variable is uncounted (Nothing)
        Just def -> do
          res1 <- wasDefinedInBlock idt
          res2 <- fromThisLab def
          if not res2 || res1
            then defToLoc def
            else findProperLoc t
        Nothing -> error "def not found, inconsistency"
    findProperLoc [] = error "proper loc not found"

    defToLoc :: Def -> GenM Loc
    defToLoc def = case def of
      (DVar tp (BlockLabel lab)) -> return (LAddr (toVType tp) (Var idt lab Nothing))
      (DArg tp _) -> return (LAddr (toVType tp) (ArgVar idt))
      (DFun _ _) -> error "tried getting fun def"
      _else -> error "impossible"
    fromThisLab :: Def -> GenM Bool
    fromThisLab def = do
      currLab <- gets blockLabel
      case def of
        (DVar _ lab) -> return $ currLab == lab
        (DArg _ _) -> return False
        (DFun _ _) -> error "tried getting fun def"

getFnRetTypeFromBinding :: Ident -> GenM VType
getFnRetTypeFromBinding idt = do
  st <- get
  -- NOTE: valid only when fn declarations cannot be nested
  case M.lookup idt (globalBindings st) of
    Just (sloc : _) ->
      case M.lookup sloc (defs st) of
        Just (DFun tp _) -> return $ toVType tp
        _else -> error $ "fn def not found: " ++ show sloc ++ "\nall defs: " ++ show (defs st)
    Just [] -> error "defs vs. bindings inconsistency"
    Nothing -> error $ "block binding not found: " ++ show idt ++ "\nall bindings: " ++ show (blockBindings st)

genStmts :: [Stmt] -> GenM ()
genStmts [] = emit $ Br (LLabel Nothing)
genStmts (Empty _ : t) = genStmts t
genStmts (Decl _ tp items : t) = do
  mapM_ declareItem items
  genStmts t
  where
    vtp :: VType
    vtp = toVType tp
    declareItem :: Item -> GenM ()
    declareItem (NoInit _ idt) = do
      defineInBlock idt
      iloc <- getVarLocFromBinding idt
      emit $ Unar Asgn iloc (initValue vtp)
    declareItem (Init _ idt e) = do
      loc <- genExp e
      defineInBlock idt
      iloc <- getVarLocFromBinding idt
      emit $ Unar Asgn iloc loc
genStmts (Ass _ idt e : t) = do
  loc <- genExp e
  vloc <- getVarLocFromBinding idt
  modify (\st -> st {locs = M.insert idt vloc (locs st)})
  emit $ Unar Asgn vloc loc
  genStmts t
genStmts (SExp _ e : t) = do
  _ <- genExp e
  genStmts t
genStmts (VRet _ : t) = do
  emit IRetVoid
  unless (null t) $ error "BB should end with VRet"
genStmts (Ret _ e : t) = do
  loc <- genExp e
  emit $ IRet loc
  unless (null t) $ error "BB should end with Ret"
genStmts (Incr p idt : t) = do
  let e = EAdd p (EVar p idt) (Plus p) (ELitInt p 1)
  genStmts (Ass p idt e : t)
genStmts (Decr p idt : t) = do
  let e = EAdd p (EVar p idt) (Minus p) (ELitInt p 1)
  genStmts (Ass p idt e : t)

-- in control instructions we don't care about their
-- true/false bodies as these are a part of other blocks
-- the labels will be set later
genStmts (Cond _ e _ : t) = do
  loc <- genExp e
  emit $ Bin CondBr loc (LLabel Nothing) (LLabel Nothing)
  unless (null t) $ error "BB should end with CondBr"
genStmts (CondElse _ e _ _ : t) = do
  loc <- genExp e
  emit $ Bin CondBr loc (LLabel Nothing) (LLabel Nothing)
  unless (null t) $ error "BB should end with CondElse"
genStmts (While _ e _ : t) = do
  loc <- genExp e
  emit $ Bin CondBr loc (LLabel Nothing) (LLabel Nothing)
  unless (null t) $ error "BB should end with CondBr (While)"
genStmts (BStmt _ _ : _) = error "should never happen"

withJumpLabel :: BB' Code -> BB' Code
withJumpLabel bb =
  case stmts bb of
    h : t ->
      bb
        { stmts =
            ( case h of
                Bin CondBr loc (LLabel Nothing) (LLabel Nothing) -> Bin CondBr loc (LLabel $ succTrue bb) (LLabel $ succFalse bb)
                Br (LLabel Nothing) -> Br (LLabel $ succDone bb)
                _else -> h
            )
              : t
        }
    [] -> error "tried setting labels in empty bb?"

genBB :: BB' [Stmt] -> GenM (BB' Code)
genBB bb = do
  -- FIXME move to Env?
  modify (\st -> st {blockBindings = bindings bb, blockLabel = label bb})
  genStmts (reverse (stmts bb))
  stmts <- takeCode
  return $ withJumpLabel $ bb {stmts}

genCFGs :: CFGsNoDefs' [Stmt] -> GenM (CFGsNoDefs' Code)
genCFGs = mapM $ mapM genBB

genFIR :: CFGs' [Stmt] -> CFGs' Code
genFIR (cfgs, info) =
  let (cfgs', _) = runState m initStore
   in (cfgs', info)
  where
    m = genCFGs cfgs
    initStore =
      FIRStore_
        { lastJumpLabel = JumpLabel 0,
          lastTemp = 0,
          code = [],
          locs = M.empty,
          blockLabel = BlockLabel 0,
          blockBindings = M.empty,
          globalBindings = cfgInfoBindings info,
          defs = cfgInfoDefs info,
          definedAlready = M.empty
        }
