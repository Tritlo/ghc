{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE NoImplicitPrelude #-}

module GHC.Exception.Trace ( traceList, traceMsgs ) where

import GHC.Types (Char, Int, IO(..))
traceList :: IO [([Char], Int, (Int, Int), ([Int], [Int]))]
traceMsgs :: IO [[Char]]
