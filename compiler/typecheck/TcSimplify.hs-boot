module TcSimplify where
import TcRnTypes  ( TcM , Implication)
import TcType ( TcSigmaType )

-- This boot file exists to make tcCanSubsume avaialble in TcErrors

tcSubsumes :: [Implication] -> TcSigmaType -> TcSigmaType -> TcM Bool
