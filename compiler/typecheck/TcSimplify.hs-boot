module TcSimplify where

import GhcPrelude
import TcRnTypes  ( TcM, Cts )
import TcType ( TcSigmaType, TcType )

-- This boot file exists solely to make tcCheckHoleFit and tcSubsumes avaialble
-- in TcErrors

tcSubsumes :: TcSigmaType -> TcSigmaType -> TcM Bool
tcCheckHoleFit :: Cts -> [TcType] -> TcSigmaType -> TcSigmaType -> TcM Bool
