
module Main(main) where

import Data.Word (Word32, Word64)
import GHC.Float (castWord32ToFloat, castWord64ToDouble)

-- | Decode runtime bits. Opacity keeps the Float primop in the test.
{-# OPAQUE decodeBits #-}
decodeBits :: Word32 -> (Integer, Int)
decodeBits bits = decodeFloat (castWord32ToFloat bits)

-- | Decode Double bit patterns through the runtime primop.
{-# OPAQUE decodeDoubleBits #-}
decodeDoubleBits :: Word64 -> (Integer, Int)
decodeDoubleBits bits = decodeFloat (castWord64ToDouble bits)

-- | Check the sign when encoding the minimum native Int.
{-# OPAQUE encodeNativeMinSigns #-}
encodeNativeMinSigns :: Int -> (Bool, Bool)
encodeNativeMinSigns power =
    let mantissa = toInteger (minBound :: Int)
     in ( encodeFloat mantissa power < (0 :: Float)
        , encodeFloat mantissa power < (0 :: Double)
        )

main = do
    print (encodeNativeMinSigns (-1))
    mapM_
        (print . decodeDoubleBits)
        [0x8000000000000000, 0x0000000000000001, 0x800fffffffffffff, 0x0010000000000000, 0x7fefffffffffffff]
    mapM_ (print . decodeBits)
        [0x00000000, 0x80000000, 0x00000001, 0x807fffff, 0x00800000, 0x7f7fffff]
    sequence_ [ f x y | x <- [0,
                                 1000,
                                 1000000000000,              -- > 2^32
                                 1000000000000000000000000,  -- > 2^64
                                 -1000,
                                 -1000000000000,             -- < -2^32
                                 -1000000000000000000000000] -- < -2^64
                         , y <- [0, -10, 10] ]

f :: Integer -> Int -> IO ()
f x y = do putStrLn "------------------------"
           print x
           print y
           let d :: Double
               d = encodeFloat x y
               (xd, yd) = decodeFloat d
           let f :: Float
               f = encodeFloat x y
               (xf, yf) = decodeFloat f
           print d
           print xd
           print yd
           print f
           print xf
           print yf

