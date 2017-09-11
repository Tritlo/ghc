module TcSimplify where
import TcRnTypes  ( TcM )
import TcType ( TcSigmaType )

-- This boot file exists solely to make tcSubsume avaialble in TcErrors

tcSubsumes :: TcSigmaType -> TcSigmaType -> TcM Bool
