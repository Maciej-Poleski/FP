module Main where

import System.Random
import Solution

main= do
  i1<- getContents
  let l1= (read i1)::[Int]
  s1<- getStdGen
  let (Rand qs)= solution l1
  print$fst$qs s1