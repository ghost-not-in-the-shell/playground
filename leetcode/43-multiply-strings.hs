{-# LANGUAGE UnicodeSyntax #-}

mult1 ∷ Integer → Integer → (Integer,Integer)
mult1 m n = (m * n `div` 10, m * n `mod` 10)

multN :: [Integer] → Integer → [(Integer,Integer)]
multN (0:_) _ = [(0,0)]
multN ms    n = map (\ m → mult1 m n) ms

mult :: [Integer] → [Integer] → [[(Integer,Integer)]]
mult ms (0:_) = []
mult ms ns    = map (multN ms) ns

reify :: [[(Integer,Integer)]] → [Integer]
reify [] = []
reify ()
