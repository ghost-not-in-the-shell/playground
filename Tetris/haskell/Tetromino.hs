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
  deriving (Bounded, Enum)

type Coord = (Integer , Integer)

data Tetromino = Tetromino { _center ∷ Coord , _shape ∷ Shape }

makeLenses ''Tetromino

instance Random Shape where
  random g = case randomR (fromEnum (minBound ∷ Shape) , fromEnum (maxBound ∷ Shape)) g of
               (r , g') → (toEnum r , g')

  randomR (a , b) g = case randomR (fromEnum a , fromEnum b) g of
                        (r , g') → (toEnum r , g')

reifyShape ∷ Shape → [Coord]
reifyShape I₁ = [(0,-1),(0,0),(0,1),(0,2)]
reifyShape I₂ = [(-1,0),(0,0),(1,0),(2,0)]

reifyShape J₁ = [(-1,1),(0,-1),(0,0),(0,1)]
reifyShape J₂ = [(-1,-1),(-1,0),(0,0),(1,0)]
reifyShape J₃ = [(0,-1),(0,0),(0,1),(1,-1)]
reifyShape J₄ = [(-1,0),(0,0),(1,0),(1,1)]

reifyShape L₁ = [(0,-1),(0,0),(0,1),(1,1)]
reifyShape L₂ = [(-1,0),(-1,1),(0,0),(1,0)]
reifyShape L₃ = [(-1,-1),(0,-1),(0,0),(0,1)]
reifyShape L₄ = [(-1,0),(0,0),(1,0),(1,-1)]

reifyShape O = [(0,0),(0,1),(1,0),(1,1)]

reifyShape S₁ = [(-1,0),(0,-1),(0,0),(1,-1)]
reifyShape S₂ = [(0,-1),(0,0),(1,0),(1,1)]

reifyShape T₁ = [(-1,0),(0,0),(0,1),(1,0)]
reifyShape T₂ = [(-1,0),(0,-1),(0,0),(0,1)]
reifyShape T₃ = [(-1,0),(0,-1),(0,0),(1,0)]
reifyShape T₄ = [(0,-1),(0,0),(0,1),(1,0)]

reifyShape Z₁ = [(-1,-1),(0,-1),(0,0),(1,0)]
reifyShape Z₂ = [(-1,0),(-1,1),(0,-1),(0,0)]

reifyTetromino ∷ Tetromino → [Coord]
reifyTetromino (Tetromino (c₁ , c₂) s) =
  [(c₁ + offset₁ , c₂ + offset₂) | (offset₁ , offset₂) ← reifyShape s]

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

rotateTetromino ∷ Tetromino → Tetromino
rotateTetromino = over shape rotateShape

extentDown ∷ Tetromino → Integer
extentDown = maximum . map snd . reifyTetromino

extentLeft ∷ Tetromino → Integer
extentLeft = minimum . map fst . reifyTetromino

extentRight ∷ Tetromino → Integer
extentRight = maximum . map fst . reifyTetromino
