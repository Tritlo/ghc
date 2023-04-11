-----------------------------------------------------------------------------
--
-- Code generation for coverage
--
-- (c) Galois Connections, Inc. 2006
--
-----------------------------------------------------------------------------

module GHC.StgToCmm.Hpc ( initHpc, mkTickBox, mkTraceBox, mkTraceBump ) where

import GHC.Prelude
import GHC.Platform

import GHC.StgToCmm.Monad
import GHC.StgToCmm.Utils

import GHC.Cmm.Graph
import GHC.Cmm.Expr
import GHC.Cmm.CLabel
import GHC.Cmm.Utils

import GHC.Unit.Module
import GHC.Types.HpcInfo

import Control.Monad

mkTickBox :: Platform -> Module -> Int -> CmmAGraph
mkTickBox platform mod n
  = mkStore tick_box (CmmMachOp (MO_Add W64)
                                [ CmmLoad tick_box b64 NaturallyAligned
                                , CmmLit (CmmInt 1 W64)
                                ])
  where
    tick_box = cmmIndex platform W64
                        (CmmLit $ CmmLabel $ mkHpcTicksLabel $ mod)
                        n
mkTraceBox :: Platform -> Module -> Int -> CmmAGraph
mkTraceBox platform mod n
  = mkStore box_to_update (CmmLit (CmmInt (fromIntegral n) W64))
    where
        index_box = cmmIndex platform W64
                    (CmmLit $ CmmLabel $ mkHpcTraceInfoLabel $ mod) 0
        box_to_update = cmmIndexExpr platform W64
                         (CmmLit $ CmmLabel $ mkHpcTraceLabel $ mod)
                         (CmmLoad index_box b64 NaturallyAligned)

mkTraceBump :: Platform -> Module -> CmmAGraph
mkTraceBump platform mod
  = mkStore index_box rem
  where
    add1 = (CmmMachOp (MO_Add W64)
             [ CmmLoad index_box b64 NaturallyAligned
             , CmmLit (CmmInt 1 W64) ])
    rem = (CmmMachOp (MO_S_Rem W64)
             [ add1
             , CmmLoad size_box b64 NaturallyAligned])
    infoLabel = cmmIndex platform W64
                (CmmLit $ CmmLabel $ mkHpcTraceInfoLabel $ mod)
    index_box = infoLabel 0
    size_box = infoLabel 1

-- | Emit top-level tables for HPC and return code to initialise
initHpc :: Module -> HpcInfo -> FCode ()
initHpc _ NoHpcInfo{}
  = return ()
initHpc this_mod (HpcInfo tickCount traceLength _hashNo)
  = do do_hpc <- stgToCmmOptHpc <$> getStgToCmmConfig
       when do_hpc $ do
           emitDataLits (mkHpcTicksLabel this_mod)
                        [ CmmInt 0 W64
                        | _ <- take tickCount [0 :: Int ..]
                        ]
           emitDataLits (mkHpcTraceInfoLabel this_mod)
                        [ CmmInt 0 W64,
                          CmmInt (fromIntegral traceLength) W64 ]
           emitDataLits (mkHpcTraceLabel this_mod)
                        [ CmmInt (fromIntegral tickCount) W64
                        | _ <- take traceLength [0 :: Int ..]
                        ]

