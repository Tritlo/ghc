module TcValidSubstitutions where

import TcRnTypes  ( TcM, Ct, Implication )
import Outputable ( SDoc )

findValidSubstitutions :: [Implication] -> [Ct] -> Ct -> TcM SDoc