-----------------------------------------------------------------------------
--
-- Code generation for coverage
--
-- (c) Galois Connections, Inc. 2006
--
-----------------------------------------------------------------------------

module GHC.StgToCmm.Hpc ( initHpc, mkTickBox,
                          mkTraceBox, mkTraceBump,
                          mkEvalTraceBox, mkEvalTraceBump, mkEvalTraceDump,
                          mkGlobalCounterBump, mkGlobalTraceBox,
                          mkStoreGlobalEval
                          ) where

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
                        (CmmLit $ CmmLabel $ mkHpcTicksLabel $ mod) n



mkTraceBox :: Platform -> Module -> Int -> CmmAGraph
mkTraceBox platform mod n
  = mkStore box_to_update (CmmLit (CmmInt (fromIntegral n) W64))
    where
        index_box = cmmIndex platform W64
                    (CmmLit $ CmmLabel $ mkHpcTraceInfoLabel $ mod) 0
        box_to_update = cmmIndexExpr platform W64
                         (CmmLit $ CmmLabel $ mkHpcTraceLabel $ mod)
                         (CmmLoad index_box b64 NaturallyAligned)

-- Write the current number of evals
mkEvalTraceBox :: Platform -> Module -> CmmAGraph
mkEvalTraceBox platform mod
  = mkStore box_to_update (CmmLoad g_eval b64 NaturallyAligned)
    where
        index_box = cmmIndex platform W64
                    (CmmLit $ CmmLabel $ mkHpcTraceInfoLabel $ mod) 0
        g_eval = (CmmLit $ CmmLabel $ mkHpcGlobalEvalsLabel)
        box_to_update = cmmIndexExpr platform W64
                         (CmmLit $ CmmLabel $ mkHpcEvalTraceLabel $ mod)
                         (CmmLoad index_box b64 NaturallyAligned)



mkGlobalTraceBox :: Platform -> Module -> CmmAGraph
mkGlobalTraceBox platform mod
  = mkStore box_to_update (CmmLoad g_counter b64 NaturallyAligned)
    where
        index_box = cmmIndex platform W64
                    (CmmLit $ CmmLabel $ mkHpcTraceInfoLabel $ mod) 0
        g_counter = (CmmLit $ CmmLabel $ mkHpcGlobalCounterLabel)
        box_to_update = cmmIndexExpr platform W64
                         (CmmLit $ CmmLabel $ mkHpcGlobalTraceLabel $ mod)
                         (CmmLoad index_box b64 NaturallyAligned)

-- So hs_hpc_globalcounter is not an array, but this works anyway.
mkGlobalCounterBump :: Platform -> CmmAGraph
mkGlobalCounterBump platform
  = mkStore g_counter add1
  where
    add1 = (CmmMachOp (MO_Add W64)
             [ CmmLoad g_counter b64 NaturallyAligned
             , CmmLit (CmmInt 1 W64) ])
    g_counter = (CmmLit $ CmmLabel $ mkHpcGlobalCounterLabel)

mkEvalTraceBump, mkEvalTraceDump :: Platform -> Module -> CmmAGraph
mkEvalTraceBump = mkTraceIndOp (MO_Add W64)
mkEvalTraceDump = mkTraceIndOp (MO_Sub W64)



-- Add or substract, no remainder
mkTraceIndOp :: MachOp -> Platform -> Module -> CmmAGraph
mkTraceIndOp op platform mod
  = mkStore g_eval op1
  where
    op1 = (CmmMachOp op
             [ CmmLoad g_eval b64 NaturallyAligned
             , CmmLit (CmmInt 1 W64) ])
    g_eval = (CmmLit $ CmmLabel $ mkHpcGlobalEvalsLabel)
    infoLabel = cmmIndex platform W64
                (CmmLit $ CmmLabel $ mkHpcTraceInfoLabel $ mod)
    index_box = infoLabel 1

mkStoreGlobalEval :: Platform -> Module -> CmmAGraph
mkStoreGlobalEval platform mod
  = mkStore index_box (CmmLoad g_eval b64 NaturallyAligned)
  where
    g_eval = (CmmLit $ CmmLabel $ mkHpcGlobalEvalsLabel)
    infoLabel = cmmIndex platform W64
                (CmmLit $ CmmLabel $ mkHpcTraceInfoLabel $ mod)
    index_box = infoLabel 1



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
    size_box = infoLabel 2


-- | Emit top-level tables for HPC and return code to initialise
initHpc :: Module -> HpcInfo -> FCode ()
initHpc _ NoHpcInfo{}
  = return ()
initHpc this_mod (HpcInfo tickCount traceLength _hashNo)
  = do do_hpc <- stgToCmmOptHpc <$> getStgToCmmConfig
       let max_val = fromIntegral tickCount
       when do_hpc $ do
           emitDataLits (mkHpcTicksLabel this_mod)
                        [ CmmInt 0 W64
                        | _ <- take tickCount [0 :: Int ..]
                        ]
           emitDataLits (mkHpcTraceInfoLabel this_mod)
                        [ CmmInt 0 W64,
                          CmmInt 0 W64,
                          CmmInt (fromIntegral traceLength) W64]
           emitDataLits (mkHpcTraceLabel this_mod)
                        [ CmmInt max_val W64
                        | _ <- take traceLength [0 :: Int ..]
                        ]
           emitDataLits (mkHpcEvalTraceLabel this_mod)
                        [ CmmInt 0 W64
                        | _ <- take traceLength [0 :: Int ..]
                        ]
           emitDataLits (mkHpcGlobalTraceLabel this_mod)
                        [ CmmInt 0 W64
                        | _ <- take traceLength [0 :: Int ..]
                        ]

