module SSA (toFIRCFGs) where

import AbsLatte
import CFG
import Common
import Control.Monad.Reader
  ( MonadReader (local),
    Reader,
    asks,
    runReader,
  )
import Control.Monad.State
  ( MonadState (get, put),
    StateT,
    gets,
    modify,
    runStateT,
  )
import Data.Map qualified as M
import FIR
import TransformAbsToFIR

type FIRBB = BB' [Instr]

type FIRCFGs = CFGs' [Instr]

toFIRCFGs :: CFGs -> FIRCFGs
toFIRCFGs = mapTo genFIR
