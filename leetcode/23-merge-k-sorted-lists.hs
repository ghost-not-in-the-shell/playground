{-# LANGUAGE UnicodeSyntax #-}

import Data.Bifunctor

merge :: (Ord a) => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge xall@(x:xs) yall@(y:ys)
  | x < y     = x : merge xs yall
  | otherwise = y : merge xall ys

{-
bundle :: (Monoid a) => [a] -> [(a , a)]
bundle []  = []
bundle [x] = [(x , mempty)]
bundle (x₁:x₂:xs) = (x₁,x₂) : bundle xs

sort :: (Ord a) => [[a]] -> [a]
sort []   = []
sort [xs] = xs
sort xss  = sort $ map (uncurry merge) $ bundle xss
-}

sort :: (Ord a) => [[a]] -> [a]
sort []   = []
sort [xs] = xs
sort xss  = uncurry merge $ bimap sort sort $ splitAt (length xss `div` 2) xss
