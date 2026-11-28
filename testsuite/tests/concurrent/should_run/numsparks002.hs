module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Foreign.StablePtr
import GHC.Conc (numSparks, par)
import System.Mem (performMajorGC)

{-# OPAQUE work #-}
work :: Int -> Int
work n = sum [1 .. n]

spark :: a -> IO ()
spark value = value `par` pure ()

sparkDead :: Int -> IO ()
sparkDead n = spark (work n)

checkFullPool :: Int -> IO ()
checkFullPool liveCount = do
    let live = map work [20 .. 19 + liveCount]
    keep <- newStablePtr live
    mapM_ spark live
    mapM_ sparkDead [20 + liveCount .. 23]
    before <- numSparks
    performMajorGC
    after <- numSparks
    total <- deRefStablePtr keep >>= evaluate . sum
    freeStablePtr keep
    print (before, after, total)

    -- Clear the now evaluated sparks before filling the pool again.
    performMajorGC
    remaining <- numSparks
    unless (remaining == 0) (fail "spark pool was not empty")

main :: IO ()
main = mapM_ checkFullPool [4, 2, 0]
