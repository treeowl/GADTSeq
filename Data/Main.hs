module Main where
import Data.Sequence
import Control.DeepSeq

abigtree n = fromList [1::Int .. n]

main = let t = abigtree (10^7)
       in t `deepseq`
               do
                print (t `index` 5)
                print (t `index` (10^7-12))
                print (t `index` (10^7 `div` 2))
