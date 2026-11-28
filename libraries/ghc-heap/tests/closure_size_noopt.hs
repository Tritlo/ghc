import ClosureSizeUtils
import Control.Exception (evaluate)

pap :: Int -> Char -> Int
pap x _ = x
{-# NOINLINE pap #-}

-- Keep the callee unknown until run time so forcing the result produces a PAP.
applyOne :: (a -> b) -> a -> b
applyOne f x = f x
{-# OPAQUE applyOne #-}

main :: IO ()
main = do
  assertSize (id :: Int -> Int) 1
  assertSize (fst :: (Int,Int) -> Int) 1
  assertSize (pap 1) 2
  applied <- evaluate (applyOne pap 1)
  assertSize applied 4
