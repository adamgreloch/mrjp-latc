module SSAToLLVM (toLLVM) where

import AbsLatte (Ident (..), Type, Type' (..))
import CFG
import CFGDefs
import Control.Monad.State
  ( MonadState (get, put),
    StateT,
    gets,
    modify,
    runStateT,
  )
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Set (Set)
import Data.Set qualified as S
import FIR
import SSA (SSA (..))

type IR = [String]

data Store = Store
  { ir :: IR,
    currIR :: IR,
    depth :: Int,
    globalBindings :: Bindings,
    globalDefs :: Defs,
    nextStringNum :: Int,
    stringConstants :: Map String Int,
    stringLengths :: Map Int Int,
    stringIR :: IR,
    stringsUsed :: Set Int,
    nextCmpLoc :: Int
  }

type IRM a = StateT Store IO a

indent :: Int -> String
indent n = concat $ replicate n " "

freshCmpLoc :: IRM Loc
freshCmpLoc = do
  n <- gets nextCmpLoc
  let n' = n + 1
  modify (\st -> st {nextCmpLoc = n'})
  return (LAddr VInt (Cmp n))

freshStringNum :: IRM Int
freshStringNum = do
  n <- gets nextStringNum
  let n' = n + 1
  modify (\st -> st {nextStringNum = n'})
  return n'

markUsed :: Int -> IRM ()
markUsed n = modify (\st -> st {stringsUsed = S.insert n (stringsUsed st)})

takeUsed :: IRM [Int]
takeUsed = do
  res <- gets stringsUsed
  modify (\st -> st {stringsUsed = S.empty})
  return $ S.toList res

addStrConstant :: String -> IRM Int
addStrConstant str = do
  st <- get
  case M.lookup str (stringConstants st) of
    Nothing -> do
      n <- freshStringNum
      emitString $ printStrConst n %= "internal constant" % "[" ++ show l ++ " x i8] c\"" ++ str ++ "\\00\""
      modify
        ( \st ->
            st
              { stringConstants = M.insert str n (stringConstants st),
                stringLengths = M.insert n l (stringLengths st)
              }
        )
      markUsed n
      return n
    Just n -> do
      markUsed n
      return n
  where
    l = length str + 1 -- including null byte

printStrConst :: Int -> String
printStrConst n = "@s" ++ show n

printStrPtr :: Int -> String
printStrPtr n = "%sp" ++ show n

emitString :: String -> IRM ()
emitString s = modify (\st -> st {stringIR = s : stringIR st})

emitGlobally :: String -> IRM ()
emitGlobally s = modify (\st -> st {ir = (indent (2 * depth st) ++ s) : ir st})

emit :: String -> IRM ()
emit s = modify (\st -> st {currIR = (indent (2 * depth st) ++ s) : currIR st})
  where
    indent :: Int -> String
    indent n = concat $ replicate n " "

emitLabel :: Label -> IRM ()
emitLabel l = modify (\st -> st {currIR = (show l ++ ":") : currIR st})

depthIn :: IRM ()
depthIn = modify (\st -> st {depth = depth st + 1})

depthOut :: IRM ()
depthOut = modify (\st -> st {depth = depth st - 1})

infixl 9 %

(%) :: String -> String -> String
(%) s1 s2 = s1 ++ " " ++ s2

infixl 9 %=

(%=) :: String -> String -> String
(%=) s1 s2 = s1 % "=" % s2

infixl 9 %>

(%>) :: String -> String -> String
(%>) s1 s2 = s1 ++ "," % s2

commas :: [String] -> [String]
commas [] = []
commas [h] = [h]
commas (h : t) = (h ++ ", ") : commas t

printLocWithType loc = printLocType loc % show loc

op2ToLLVM :: Op2 -> String
op2ToLLVM op =
  case op of
    Add -> "add"
    Sub -> "sub"
    Mul -> "mul"
    Div -> "sdiv"
    Mod -> "srem"
    LTh -> "icmp slt"
    LEq -> "icmp sle"
    GTh -> "icmp sgt"
    GEq -> "icmp sge"
    Eq -> "icmp eq"
    NEq -> "icmp ne"
    _else -> error $ "should not be needed for" % show op

printLoc :: Loc -> IRM String
printLoc (LString s) = do
  n <- addStrConstant s
  return $ printStrPtr n
printLoc loc = return $ show loc

irInstr :: Instr -> IRM ()
irInstr (ILabel lab) = do
  emitLabel lab
irInstr IRetVoid = emit "ret void"
irInstr (IRet loc) = do
  ls <- printLoc loc
  emit $ "ret" % printLocType loc % ls
irInstr (Br loc) = do
  ls <- printLoc loc
  emit $ "br" % printLocType loc % ls
irInstr (Call retLoc fidt@(Ident fns) locs) = do
  (rettp, args) <- lookupFn fidt
  locsStr <-
    mapM
      ( \loc -> do
          ls <- printLoc loc
          return (printLocType loc % ls)
      )
      locs
  emit $
    (case typeOfLoc retLoc of VVoid -> ""; _else -> show retLoc %= "")
      ++ "call"
        % printLocType retLoc
        % "("
      ++ printArgTypes args
      ++ ") @"
      ++ fns
      ++ "("
      ++ concat (commas locsStr)
      ++ ")"
irInstr (Bin CondBr loc1 loc2 loc3) =
  emit $ "br" % printLocWithType loc1 %> printLocWithType loc2 %> printLocWithType loc3
irInstr (Bin op loc1 loc2@(LAddr VStr _) loc3) = operateOnStrings op loc1 loc2 loc3
irInstr (Bin op loc1 loc2@(LString _) loc3) = operateOnStrings op loc1 loc2 loc3
irInstr (Bin op loc1 loc2 loc3) =
  emit $ show loc1 %= op2ToLLVM op % printLocWithType loc2 %> show loc3
irInstr (Phi loc pops) = do
  locsStr <-
    mapM
      ( \(lab, loc) -> do
          ls <- printLoc loc
          return $ "[" % ls ++ "," % "%" ++ show lab % "]"
      )
      pops
  emit $
    show loc
      %= "phi"
      % printLocType loc
      % concat (commas locsStr)
irInstr _ = return ()

operateOnStrings op loc1 loc2 loc3 | isRel op = do
  cmpLoc <- freshCmpLoc
  irInstr (Call cmpLoc (Ident "strcmp") [loc2, loc3])
  irInstr (Bin op loc1 cmpLoc (LImmInt 0))
operateOnStrings Add loc1 loc2 loc3 = irInstr (Call loc1 (Ident "concatStrings") [loc2, loc3])
operateOnStrings _ _ _ _ = error "only rel and concat are allowed on strings"

irBB :: BB' Code -> IRM ()
irBB bb = do
  emitLabel $ label bb
  mapM_ irInstr (reverse $ stmts bb)

strPtrsToIR :: [Int] -> IRM IR
strPtrsToIR =
  mapM
    ( \n -> do
        st <- get
        let l = fromJust $ M.lookup n (stringLengths st)
        return $
          indent (2 * depth st)
            ++ printStrPtr n %= "getelementptr ["
            ++ show l
            ++ " x i8], ["
            ++ show l
            ++ " x i8]* "
            ++ printStrConst n
            ++ ", i32 0, i32 0"
    )

irCFG :: CFG' Code -> IRM ()
irCFG cfg = do
  mapM_ irBB cfg
  ns <- takeUsed
  cir <- gets currIR
  case cir of
    [] -> return ()
    _else -> do
      sir <- strPtrsToIR ns
      modify (\st -> st {ir = init cir ++ reverse (last cir : sir) ++ ir st, currIR = []})

printType :: Type -> String
printType = show . toVType

printLocType :: Loc -> String
printLocType = show . typeOfLoc

printArgs :: [(Type, Ident)] -> String
printArgs l = concat (commas $ map (\(tp, Ident s) -> printType tp % "%" ++ s) l)

printArgTypes :: [(Type, Ident)] -> String
printArgTypes l = concat (commas $ map (\(tp, Ident s) -> printType tp) l)

-- TODO readString and error

irCFGs :: CFGsNoDefs' Code -> IRM ()
irCFGs cfgs = do
  let kv = M.toList cfgs
  mapM_
    ( \(fidt@(Ident fns), bb) -> do
        st <- get
        (rettp, args) <- lookupFn fidt
        emitGlobally $
          "define"
            % printType rettp
            % "@"
            ++ fns
            ++ "("
            ++ printArgs args
            ++ ") {"
        -- emitLabel Entry
        depthIn
        irCFG bb
        depthOut
        emitGlobally "}"
    )
    kv

lookupFn :: Ident -> IRM (Type, [(Type, Ident)])
lookupFn idt = do
  st <- get
  case M.lookup idt (globalBindings st) of
    Just (sloc : t) -> case M.lookup sloc (globalDefs st) of
      Just df@(DFun tp args) -> return (tp, args)
      _else -> error $ "no such def" % show idt
    Just _ -> error "impossible"
    Nothing -> error $ "no such bind" % show idt

-- TODO add printInt, printString, target triple, etc
toLLVM :: SSA -> IO IR
toLLVM (SSA (cfgs, info)) = do
  (_, st) <- runStateT m initStore
  let prolog =
        [ "target triple = \"x86_64-pc-linux-gnu\"",
          "declare void @printInt(i32)",
          "declare void @printString(i8*)",
          "declare void @error()",
          "declare i32 @readInt()",
          "declare i32 @strcmp(i8*, i8*)",
          "declare i8* @concatStrings(i8*, i8*)"
        ]
  return $ prolog ++ reverse (stringIR st) ++ reverse (ir st)
  where
    m = irCFGs cfgs
    initStore =
      Store
        { ir = [],
          currIR = [],
          depth = 0,
          globalBindings = cfgInfoBindings info,
          globalDefs = cfgInfoDefs info,
          nextStringNum = 0,
          stringConstants = M.empty,
          stringLengths = M.empty,
          stringIR = [],
          stringsUsed = S.empty,
          nextCmpLoc = 0
        }
