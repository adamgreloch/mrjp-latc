module Common where

import AbsLatte (Stmt, Stmt' (..))
import Control.Monad.Reader
  ( MonadReader (ask, local),
    asks,
  )
import PrintLatte (printTree)

-- These two MonadReader functions are helpful, but can probably be generalized in
-- a smarter way (possibly merged). It really depends

readerSeq :: (MonadReader r m) => (a -> m r) -> [a] -> m r
readerSeq mf (h : t) = do
  env <- mf h
  local (const env) (readerSeq mf t)
readerSeq _ [] = ask

readerEitherSeq :: (MonadReader l m) => (a -> m (Either l r)) -> [a] -> m (Either l r)
readerEitherSeq mf (h : t) = do
  res <- mf h
  case res of
    (Left l) -> local (const l) (readerEitherSeq mf t)
    (Right r) -> return (Right r)
readerEitherSeq _ [] = asks Left

class Printable a where
  printCode :: a -> String

instance Printable [Stmt] where
  printCode (s : t) =
    ( case s of
        (While _ e _) -> "while (" ++ printTree e ++ ") {...}"
        (Cond _ e _) -> "if (" ++ printTree e ++ ") {...}"
        (CondElse _ e _ _) -> "if (" ++ printTree e ++ ") {...} else {...}"
        stmt -> printTree stmt
    )
      ++ if null t then "" else "\n" ++ printCode t
  printCode [] = ""

