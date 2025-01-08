{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}

module Main where

import AbsLatte
import CFG
import Control.Monad (when)
import GHC.IO.Handle.FD (stderr)
import Helper
import LexLatte (Token, mkPosToken)
import ParLatte (myLexer, pProgram)
import PrintLatte (printTree)
import SSA
import SSAToLLVM
import SkelLatte ()
import System.Environment (getArgs)
import System.Exit (ExitCode (ExitSuccess), exitFailure)
import System.FilePath (replaceFileName, takeFileName, (-<.>))
import System.IO (hPutStrLn)
import System.Posix
  ( ProcessStatus (Exited),
    executeFile,
    forkProcess,
    getProcessStatus,
  )
import TransformAbsToFIR (genFIR)
import TypeCheckLatte
import Prelude hiding (lookup)

type Err = Either String

type ParseFun a = [Token] -> Err a

runFile :: Verbosity -> ParseFun Program -> FilePath -> IO ()
runFile v p f = putStrV v f >> readFile f >>= run v p o
  where
    o = replaceFileName f (takeFileName f -<.> "ll")

run :: Verbosity -> ParseFun Program -> FilePath -> String -> IO ()
run v p o s =
  case p ts of
    Left err -> do
      hPutStrLn stderr ("ERROR\n" ++ err)
      putStrV v "\n Tokens:"
      mapM_ (putStrV v . showPosToken . mkPosToken) ts
      exitFailure
    Right tree -> do
      putStrV v "Parse Successful!"
      compileProgram v tree o
      execCmd "llvm-as" ["-o", o -<.> "bc_", o]
      execCmd "llvm-link" ["-o", o -<.> "bc", o -<.> "bc_", "./lib/runtime.ll"]
      return ()
  where
    ts = myLexer s

    showPosToken ((l, c), t) = concat [show l, ":", show c, "\t", show t]

    execCmd cmd args = do
      result <- forkProcess (executeFile cmd True args Nothing) >>= getProcessStatus True False
      case result of
        Just (Exited ExitSuccess) ->
          hPutStrLn stderr $ cmd ++ " succeeded"
        _otherwise -> hPutStrLn stderr $ cmd ++ " failed"

compileProgram :: Int -> Program -> FilePath -> IO ()
compileProgram v tree o = do
  putStrV v $ "[Abstract Syntax]\n" ++ show tree
  putStrV v $ "[Linearized tree]\n" ++ printTree tree
  tcinfo <- typeCheckProgram v tree
  cfgs <- genCFGs tcinfo tree
  putStrV v $ "[CFGs]\n" ++ show cfgs
  let fircfgs = genFIR cfgs
  putStrV v $ "[FIRCFGs]\n" ++ show fircfgs
  when (v == 1) $ putStrLn $ toDot cfgs
  when (v == 2) $ putStrLn $ toDot fircfgs
  ssa@(SSA ssacfgs) <- toSSA fircfgs
  putStrV v $ "[SSACFGs]\n" ++ show ssacfgs
  when (v == 3) $ putStrLn $ toDot ssacfgs
  ir <- toLLVM ssa
  putStrV v $ "[LLVMIR]\n" ++ show ir
  when (v == 4) $ mapM_ putStrLn ir
  writeFile o ""
  mapM_ (\s -> appendFile o (s ++ "\n")) ir

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
        "  -S (files)      Print SSACFG in DOT format.",
        "  -l (files)      Emit LLVM IR."
      ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    "-s" : fs -> mapM_ (runFile 0 pProgram) fs
    "-g" : fs -> mapM_ (runFile 1 pProgram) fs
    "-f" : fs -> mapM_ (runFile 2 pProgram) fs
    "-S" : fs -> mapM_ (runFile 3 pProgram) fs
    "-l" : fs -> mapM_ (runFile 4 pProgram) fs
    fs -> mapM_ (runFile 0 pProgram) fs
