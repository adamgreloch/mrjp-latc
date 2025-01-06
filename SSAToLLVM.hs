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
import Data.Map qualified as M
import Data.Maybe (fromJust)
import FIR
import SSA (SSA (..))

type IR = [String]

data Store = Store
  { ir :: IR,
    depth :: Int,
    globalBindings :: Bindings,
    globalDefs :: Defs
  }

type IRM a = StateT Store IO a

emit :: String -> IRM ()
emit s = modify (\st -> st {ir = (indent (2 * depth st) ++ s) : ir st})
  where
    indent :: Int -> String
    indent n = concat $ replicate n " "

emitLabel :: Label -> IRM ()
emitLabel l = modify (\st -> st {ir = (show l ++ ":") : ir st})

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

irInstr :: Instr -> IRM ()
irInstr (ILabel lab) = do
  emitLabel lab
irInstr IRetVoid = emit "ret void"
irInstr (IRet loc) = emit $ "ret" % printLocType loc % show loc
irInstr (Br loc) = emit $ "br" % printLocType loc % show loc
irInstr (Call retLoc fidt@(Ident fns) locs) = do
  (rettp, args) <- lookupFn fidt
  emit $
    show retLoc
      %= "call"
      % printLocType retLoc
      % "("
      ++ printArgTypes args
      ++ ") @"
      ++ fns
      ++ "("
      ++ concat (commas $ map (\loc -> printLocType loc % show loc) locs)
      ++ ")"
irInstr (Bin CondBr loc1 loc2 loc3) =
  emit $ "br" % printLocWithType loc1 %> printLocWithType loc2 %> printLocWithType loc3
irInstr (Bin op loc1 loc2 loc3) =
  emit $ show loc1 %= op2ToLLVM op % printLocWithType loc2 %> show loc3
irInstr (Phi loc pops) =
  emit $ show loc %= "phi" % printLocType loc % "[" ++ concat (commas $ map (\(lab, loc) -> show loc ++ ":" % "%" ++ show lab) pops) ++ "]"
irInstr _ = return ()

irBB :: BB' Code -> IRM ()
irBB bb = do
  emitLabel $ label bb
  mapM_ irInstr (reverse $ stmts bb)

irCFG :: CFG' Code -> IRM ()
irCFG = mapM_ irBB

printType :: Type -> String
printType = show . toVType

printLocType :: Loc -> String
printLocType = show . typeOfLoc

printArgs :: [(Type, Ident)] -> String
printArgs l = concat (commas $ map (\(tp, Ident s) -> printType tp % "%" ++ s) l)

printArgTypes :: [(Type, Ident)] -> String
printArgTypes l = concat (commas $ map (\(tp, Ident s) -> printType tp) l)

irCFGs :: CFGsNoDefs' Code -> IRM ()
irCFGs cfgs = do
  let kv = M.toList cfgs
  mapM_
    ( \(fidt@(Ident fns), bb) -> do
        st <- get
        (rettp, args) <- lookupFn fidt
        emit $
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
        emit "}"
    )
    kv

lookupFn :: Ident -> IRM (Type, [(Type, Ident)])
lookupFn idt = do
  st <- get
  let sloc = head $ fromJust $ M.lookup idt (globalBindings st)
  case M.lookup sloc (globalDefs st) of
    Just df@(DFun tp args) -> return (tp, args)
    _else -> error "no such def"

-- TODO add printInt, printString, target triple, etc
toLLVM :: SSA -> IO IR
toLLVM (SSA (cfgs, info)) = do
  (_, st) <- runStateT m initStore
  return $ reverse $ ir st
  where
    m = irCFGs cfgs
    initStore =
      Store
        { ir = [],
          depth = 0,
          globalBindings = cfgInfoBindings info,
          globalDefs = cfgInfoDefs info
        }
