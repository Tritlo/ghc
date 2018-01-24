module TcSimplify where

import GhcPrelude
import TcRnTypes  ( TcM, Cts, Implication )
import TcType ( TcSigmaType )
import Bag ( Bag )


-- This boot file exists solely to make tcCheckHoleFit and tcSubsumes avaialble
-- in TcErrors

tcSubsumes :: TcSigmaType -> TcSigmaType -> TcM Bool
tcCheckHoleFit :: Bool -> Cts -> TcSigmaType -> TcSigmaType -> TcM (Bag Implication)
