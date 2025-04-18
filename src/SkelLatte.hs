-- File generated by the BNF Converter (bnfc 2.9.5).

-- Templates for pattern matching on abstract syntax

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module SkelLatte where

import Prelude (($), Either(..), String, (++), Show, show)
import qualified AbsLatte

type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transIdent :: AbsLatte.Ident -> Result
transIdent x = case x of
  AbsLatte.Ident string -> failure x

transProgram :: Show a => AbsLatte.Program' a -> Result
transProgram x = case x of
  AbsLatte.Program _ topdefs -> failure x

transTopDef :: Show a => AbsLatte.TopDef' a -> Result
transTopDef x = case x of
  AbsLatte.FnDef _ type_ ident args block -> failure x

transArg :: Show a => AbsLatte.Arg' a -> Result
transArg x = case x of
  AbsLatte.Arg _ type_ ident -> failure x

transBlock :: Show a => AbsLatte.Block' a -> Result
transBlock x = case x of
  AbsLatte.Block _ stmts -> failure x

transStmt :: Show a => AbsLatte.Stmt' a -> Result
transStmt x = case x of
  AbsLatte.Empty _ -> failure x
  AbsLatte.BStmt _ block -> failure x
  AbsLatte.Decl _ type_ items -> failure x
  AbsLatte.Ass _ ident expr -> failure x
  AbsLatte.Incr _ ident -> failure x
  AbsLatte.Decr _ ident -> failure x
  AbsLatte.Ret _ expr -> failure x
  AbsLatte.VRet _ -> failure x
  AbsLatte.Cond _ expr stmt -> failure x
  AbsLatte.CondElse _ expr stmt1 stmt2 -> failure x
  AbsLatte.While _ expr stmt -> failure x
  AbsLatte.SExp _ expr -> failure x

transItem :: Show a => AbsLatte.Item' a -> Result
transItem x = case x of
  AbsLatte.NoInit _ ident -> failure x
  AbsLatte.Init _ ident expr -> failure x

transType :: Show a => AbsLatte.Type' a -> Result
transType x = case x of
  AbsLatte.Int _ -> failure x
  AbsLatte.Str _ -> failure x
  AbsLatte.Bool _ -> failure x
  AbsLatte.Void _ -> failure x
  AbsLatte.Fun _ type_ types -> failure x

transExpr :: Show a => AbsLatte.Expr' a -> Result
transExpr x = case x of
  AbsLatte.EVar _ ident -> failure x
  AbsLatte.ELitInt _ integer -> failure x
  AbsLatte.ELitTrue _ -> failure x
  AbsLatte.ELitFalse _ -> failure x
  AbsLatte.EApp _ ident exprs -> failure x
  AbsLatte.EString _ string -> failure x
  AbsLatte.Neg _ expr -> failure x
  AbsLatte.Not _ expr -> failure x
  AbsLatte.EMul _ expr1 mulop expr2 -> failure x
  AbsLatte.EAdd _ expr1 addop expr2 -> failure x
  AbsLatte.ERel _ expr1 relop expr2 -> failure x
  AbsLatte.EAnd _ expr1 expr2 -> failure x
  AbsLatte.EOr _ expr1 expr2 -> failure x

transAddOp :: Show a => AbsLatte.AddOp' a -> Result
transAddOp x = case x of
  AbsLatte.Plus _ -> failure x
  AbsLatte.Minus _ -> failure x

transMulOp :: Show a => AbsLatte.MulOp' a -> Result
transMulOp x = case x of
  AbsLatte.Times _ -> failure x
  AbsLatte.Div _ -> failure x
  AbsLatte.Mod _ -> failure x

transRelOp :: Show a => AbsLatte.RelOp' a -> Result
transRelOp x = case x of
  AbsLatte.LTH _ -> failure x
  AbsLatte.LE _ -> failure x
  AbsLatte.GTH _ -> failure x
  AbsLatte.GE _ -> failure x
  AbsLatte.EQU _ -> failure x
  AbsLatte.NE _ -> failure x
