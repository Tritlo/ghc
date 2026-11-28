module Main (main) where

import Control.Monad (unless)
import Data.Bits (finiteBitSize)
import Data.IORef (newIORef, readIORef)
import System.Mem (performBlockingMajorGC)

-- | Keep small heap objects alive through the synchronous nonmoving census.
main :: IO ()
main = do
    refs <- mapM newIORef [1 .. 20000 :: Int]
    performBlockingMajorGC
    performBlockingMajorGC
    total <- sum <$> mapM readIORef refs
    unless (total == 200010000) (fail "incorrect total")
    print (finiteBitSize (0 :: Int) `div` 8)
