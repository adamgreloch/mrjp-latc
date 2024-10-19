module Helper where

import AbsLatte
import Control.Monad (when)
import Data.Text (pack, replace, unpack)
import PrintLatte

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

(~) :: Type -> Type -> Bool
(~) = eq
  where
    eq (Int _) (Int _) = True
    eq (Str _) (Str _) = True
    eq (Bool _) (Bool _) = True
    eq (Void _) (Void _) = True
    eq _ _ = False

argType :: Arg -> Type
argType (Arg _ tp _) = tp

isLValue :: Expr -> Bool
isLValue e = case e of
  (EVar _ _) -> True
  _ -> False

argName :: Arg -> Ident
argName (Arg _ _ name) = name

at :: BNFC'Position -> String
at Nothing = "?:?"
at (Just (line, col)) = show line ++ ":" ++ show col

typeAt :: Type -> String
typeAt t =
  show t
    ++ case hasPosition t of
      Nothing -> ""
      p -> " at " ++ at p

typeFrom :: Type -> String
typeFrom t = show t ++ " from " ++ at (hasPosition t)

printLineNr :: BNFC'Position -> String
printLineNr Nothing = "?"
printLineNr (Just (line, col)) = show line

printStmt :: Stmt -> String
printStmt stmt =
  "  " ++ unpack (replace (pack "\n") (pack "\n  ") pstr)
  where
    pstr = pack (printTree stmt)


