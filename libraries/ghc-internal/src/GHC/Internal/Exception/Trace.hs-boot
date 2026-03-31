{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE NoImplicitPrelude #-}

module GHC.Internal.Exception.Trace ( traceList, traceMsgs ) where

import GHC.Internal.Types (Char, Int, IO)
traceList :: IO [([Char], Int, Int, [Int])]
traceMsgs :: IO [[Char]]
