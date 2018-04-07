module TcValidSubstitutions where

import TcRnTypes  ( TcM, Ct, Implication )
import Outputable ( SDoc )
import VarEnv     ( TidyEnv )

findValidSubstitutions :: TidyEnv -> [Implication]
                        -> [Ct] -> Ct
                        -> TcM (TidyEnv, SDoc)
