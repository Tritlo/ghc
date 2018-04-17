module TcHoleErrors where

import TcRnTypes  ( TcM, Ct, Implication )
import Outputable ( SDoc )
import VarEnv     ( TidyEnv )

findValidHoleFits :: TidyEnv -> [Implication] -> [Ct] -> Ct
                  -> TcM (TidyEnv, SDoc)
