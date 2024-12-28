module Common where

import Control.Monad.Reader
  ( MonadReader (ask, local),
    asks,
  )

-- These two monadreader functions are helpful, but can probably be generized in
-- a smarter way (possibly merged). It really depends

readerSeq :: (MonadReader r m) => (a -> m r) -> [a] -> m r
readerSeq mf (h : t) = do
  env <- mf h
  local (const env) (readerSeq mf t)
readerSeq _ [] = ask

readerEitherSeq :: (MonadReader r m) => (a -> m (Either r l)) -> [a] -> m (Either r l)
readerEitherSeq mf (h : t) = do
  res <- mf h
  case res of
    (Left l) -> local (const l) (readerEitherSeq mf t)
    (Right r) -> return (Right r)
readerEitherSeq _ [] = asks Left

class Printable a where
  printCode :: a -> String
