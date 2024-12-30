module SSA (toFIRCFGs) where

import CFG
import FIR
import TransformAbsToFIR

type FIRCFGs = CFGs' [Instr]

toFIRCFGs :: CFGs -> FIRCFGs
toFIRCFGs = mapTo genFIR
