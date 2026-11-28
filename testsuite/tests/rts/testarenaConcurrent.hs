{-# LANGUAGE CApiFFI #-}

module Main (main) where

import Control.Concurrent (forkOn, newEmptyMVar, putMVar, readMVar, takeMVar)
import Control.Monad (forM_, replicateM, unless, void)
import Data.Word (Word8)
import Foreign.Marshal.Pool (freePool, newPool, pooledMallocBytes)
import Foreign.Storable (poke)
import System.Exit (die)

foreign import ccall unsafe "arenaBlocks" arenaBlocks :: IO Word
foreign import capi "Rts.h value BLOCK_SIZE" arenaBlockSize :: Word

workers, pools, rounds :: Int
workers = 4
pools = 128
rounds = 40

main :: IO ()
main = do
    let blockSize = fromIntegral arenaBlockSize
    old <- arenaBlocks
    forM_ [1 .. rounds] $ \iteration -> do
        start <- newEmptyMVar
        ready <- replicateM workers newEmptyMVar
        release <- newEmptyMVar
        done <- replicateM workers newEmptyMVar
        forM_ (zip3 [0 ..] ready done) $ \(cap, live, freed) ->
            void $ forkOn cap $ do
                readMVar start
                owned <- replicateM pools $ do
                    pool <- newPool
                    location <- pooledMallocBytes pool (2 * blockSize + 1)
                    poke location (42 :: Word8)
                    pure pool
                putMVar live ()
                readMVar release
                mapM_ freePool owned
                putMVar freed ()
        putMVar start ()
        -- Each worker owns its pools. It parks before each count is sampled.
        mapM_ takeMVar ready
        live <- arenaBlocks
        putMVar release ()
        mapM_ takeMVar done
        final <- arenaBlocks
        -- A pool acquires one initial block and three more for this request.
        let expected = old + fromIntegral (workers * pools * 4)
        unless (live == expected && final == old) $
            die
                ( "round "
                    ++ show iteration
                    ++ ": live "
                    ++ show live
                    ++ "/"
                    ++ show expected
                    ++ ", final "
                    ++ show final
                    ++ "/"
                    ++ show old
                )
