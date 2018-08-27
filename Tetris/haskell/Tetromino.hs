{-# LANGUAGE TemplateHaskell, UnicodeSyntax #-}
module Tetromino where

import Control.Lens

data Shape
  = I₁ | I₂
  | J₁ | J₂ | J₃ | J₄
  | L₁ | L₂ | L₃ | L₄
  | O
  | S₁ | S₂
  | T₁ | T₂ | T₃ | T₄
  | Z₁ | Z₂
  deriving (Enum, Eq)

type Coord = (Int,Int)

data Tetromino = Tetromino { _center ∷ Coord , _shape ∷ Shape }

makeLenses ''Tetromino

reifyS ∷ Shape → [Coord]
reifyS I₁ = [(0,-1),(0,0),(0,1),(0,2)]
reifyS I₂ = [(-1,0),(0,0),(1,0),(2,0)]

reifyS J₁ = [(-1,1),(0,-1),(0,0),(0,1)]
reifyS J₂ = [(-1,-1),(-1,0),(0,0),(1,0)]
reifyS J₃ = [(0,-1),(0,0),(0,1),(1,-1)]
reifyS J₄ = [(-1,0),(0,0),(1,0),(1,1)]

reifyS L₁ = [(0,-1),(0,0),(0,1),(1,1)]
reifyS L₂ = [(-1,0),(-1,1),(0,0),(1,0)]
reifyS L₃ = [(-1,-1),(0,-1),(0,0),(0,1)]
reifyS L₄ = [(-1,0),(0,0),(1,0),(1,-1)]

reifyS O = [(0,0),(0,1),(1,0),(1,1)]

reifyS S₁ = [(-1,0),(0,-1),(0,0),(1,-1)]
reifyS S₂ = [(0,-1),(0,0),(1,0),(1,1)]

reifyS T₁ = [(-1,0),(0,0),(0,1),(1,0)]
reifyS T₂ = [(-1,0),(0,-1),(0,0),(0,1)]
reifyS T₃ = [(-1,0),(0,-1),(0,0),(1,0)]
reifyS T₄ = [(0,-1),(0,0),(0,1),(1,0)]

reifyS Z₁ = [(-1,-1),(0,-1),(0,0),(1,0)]
reifyS Z₂ = [(-1,0),(-1,1),(0,-1),(0,0)]

reifyT ∷ Tetromino → [Coord]
reifyT (Tetromino (c₁ , c₂) s) =
  [(c₁ + offset₁ , c₂ + offset₂) | (offset₁ , offset₂) ← reifyS s]

rotateS ∷ Shape → Shape
rotateS I₁ = I₂
rotateS I₂ = I₁

rotateS J₁ = J₂
rotateS J₂ = J₃
rotateS J₃ = J₄
rotateS J₄ = J₁

rotateS L₁ = L₂
rotateS L₂ = L₃
rotateS L₃ = L₄
rotateS L₄ = L₁

rotateS O = O

rotateS S₁ = S₂
rotateS S₂ = S₁

rotateS T₁ = T₂
rotateS T₂ = T₃
rotateS T₃ = T₄
rotateS T₄ = T₁

rotateS Z₁ = Z₂
rotateS Z₂ = Z₁

rotateT ∷ Tetromino → Tetromino
rotateT = over shape rotateS

extentDown ∷ Tetromino → Int
extentDown = maximum . map snd . reifyT

extentLeft ∷ Tetromino → Int
extentLeft = minimum . map fst . reifyT

extentRight ∷ Tetromino → Int
extentRight = maximum . map fst . reifyT
