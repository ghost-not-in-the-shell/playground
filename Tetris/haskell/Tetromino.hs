{-# LANGUAGE TemplateHaskell, UnicodeSyntax #-}
module Tetromino where

import Control.Lens
import System.Random

data Shape
  = I₁ | I₂
  | J₁ | J₂ | J₃ | J₄
  | L₁ | L₂ | L₃ | L₄
  | O
  | S₁ | S₂
  | T₁ | T₂ | T₃ | T₄
  | Z₁ | Z₂
  deriving (Enum, Bounded, Show)

instance Random Shape where
  random gen = case randomR ( fromEnum (minBound ∷ Shape)
                            , fromEnum (maxBound ∷ Shape)) gen of
                 (r , gen) → (toEnum r , gen)

  randomR (s₁ , s₂) gen = case randomR ( fromEnum s₁
                                       , fromEnum s₂) gen of
                            (r , gen) → (toEnum r , gen)

type Coord = (Integer , Integer)

data Tetromino = Tetromino { _center ∷ Coord , _shape ∷ Shape }
  deriving (Show)

makeLenses ''Tetromino

relativeCoord ∷ Shape → [Coord]
relativeCoord I₁ = [(0,-1),(0,0),(0,1),(0,2)]
relativeCoord I₂ = [(-1,0),(0,0),(1,0),(2,0)]

relativeCoord J₁ = [(-1,1),(0,-1),(0,0),(0,1)]
relativeCoord J₂ = [(-1,-1),(-1,0),(0,0),(1,0)]
relativeCoord J₃ = [(0,-1),(0,0),(0,1),(1,-1)]
relativeCoord J₄ = [(-1,0),(0,0),(1,0),(1,1)]

relativeCoord L₁ = [(0,-1),(0,0),(0,1),(1,1)]
relativeCoord L₂ = [(-1,0),(-1,1),(0,0),(1,0)]
relativeCoord L₃ = [(-1,-1),(0,-1),(0,0),(0,1)]
relativeCoord L₄ = [(-1,0),(0,0),(1,0),(1,-1)]

relativeCoord O = [(0,0),(0,1),(1,0),(1,1)]

relativeCoord S₁ = [(-1,0),(0,-1),(0,0),(1,-1)]
relativeCoord S₂ = [(0,-1),(0,0),(1,0),(1,1)]

relativeCoord T₁ = [(-1,0),(0,0),(0,1),(1,0)]
relativeCoord T₂ = [(-1,0),(0,-1),(0,0),(0,1)]
relativeCoord T₃ = [(-1,0),(0,-1),(0,0),(1,0)]
relativeCoord T₄ = [(0,-1),(0,0),(0,1),(1,0)]

relativeCoord Z₁ = [(-1,-1),(0,-1),(0,0),(1,0)]
relativeCoord Z₂ = [(-1,0),(-1,1),(0,-1),(0,0)]

absoluteCoord ∷ Tetromino → [Coord]
absoluteCoord (Tetromino (c₁ , c₂) s)
  = [(c₁ + offset₁ , c₂ + offset₂) | (offset₁ , offset₂) ← relativeCoord s]

rotateShape ∷ Shape → Shape
rotateShape I₁ = I₂
rotateShape I₂ = I₁

rotateShape J₁ = J₂
rotateShape J₂ = J₃
rotateShape J₃ = J₄
rotateShape J₄ = J₁

rotateShape L₁ = L₂
rotateShape L₂ = L₃
rotateShape L₃ = L₄
rotateShape L₄ = L₁

rotateShape O = O

rotateShape S₁ = S₂
rotateShape S₂ = S₁

rotateShape T₁ = T₂
rotateShape T₂ = T₃
rotateShape T₃ = T₄
rotateShape T₄ = T₁

rotateShape Z₁ = Z₂
rotateShape Z₂ = Z₁

extentDown ∷ Tetromino → Integer
extentDown = maximum . map snd . absoluteCoord

extentLeft ∷ Tetromino → Integer
extentLeft = minimum . map fst . absoluteCoord

extentRight ∷ Tetromino → Integer
extentRight = maximum . map fst . absoluteCoord
