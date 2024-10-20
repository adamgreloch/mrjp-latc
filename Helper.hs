module Helper where

import AbsLatte
import Control.Monad (when)
import Data.Text (pack, replace, unpack)
import PrintLatte

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

infixr 9 ~
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
  _othr -> False

argName :: Arg -> Ident
argName (Arg _ _ name) = name

at :: BNFC'Position -> String
at Nothing = "?:?"
at (Just (line, col)) = show line ++ ":" ++ show col

from :: BNFC'Position -> String
from Nothing = ""
from (Just (line, col)) = "from " ++ show line ++ ":" ++ show col

typeAt :: Type -> String
typeAt t =
  show t
    ++ case hasPosition t of
      Nothing -> ""
      p -> " at " ++ at p

typeFrom :: Type -> String
typeFrom t = show t ++ " " ++ from (hasPosition t)

printLineNr :: BNFC'Position -> String
printLineNr Nothing = "?"
printLineNr (Just (line, _)) = show line

printIdent :: Ident -> String
printIdent (Ident idt) = idt

printType :: Type -> String
printType (Int _) = "int"
printType (Str _) = "string"
printType (Bool _) = "boolean"
printType (Void _) = "void"
printType (Fun _ rt ts) = show rt ++ "(" ++ foldr (\t acc -> show t ++ ", " ++ acc) "" ts

printStmt :: Stmt -> String
printStmt stmt =
  printLineNr (hasPosition stmt) ++ " | " ++ unpack (replace (pack "\n") (pack "\n  | ") pstr)
  where
    pstr = pack (printTree stmt)

printArg :: Arg -> String
printArg (Arg _ tp idt) = printType tp ++ " " ++ printIdent idt

printTopDef :: TopDef -> String
printTopDef (FnDef p ret fn args _) =
  printLineNr p ++ " | " ++ show ret ++ " " ++ show fn ++ "(" ++ foldr (\t acc -> printArg t ++ (if null acc then "" else ", " ++ acc)) "" args ++ ")"

