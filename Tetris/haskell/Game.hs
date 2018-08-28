{-# LANGUAGE TemplateHaskell, UnicodeSyntax #-}
module Game where

import Control.Monad.Writer
import Control.Lens
import Data.Array
import Tetromino

type Board = Array Coord Bool

data Event = RotateCW
           | MoveDown
           | MoveLeft
           | MoveRight
           | Gravitate
           | Tick
           | Quit
           | None

data Change = On  Coord
            | Off Coord
            | Delay

data Game = Game { _board ∷ Board , _tetromino ∷ Tetromino , _nextShapes ∷ [Shape] }

makeLenses ''Game

reifyGame ∷ Game → [Coord]
reifyGame (Game b t) = filter (inRange (bounds b)) $ reifyTetromino t

on  ∷ Game → [Change]
off ∷ Game → [Change]
on  g = map On  (reifyGame g)
off g = map Off (reifyGame g)

noCollisions ∷ Game → Bool
noCollisions g@(Game b t) = not $ or $ map (b !) $ reifyGame g

downOK  ∷ Game → Bool
leftOK  ∷ Game → Bool
rightOK ∷ Game → Bool
downOK  (Game b t) = extentDown  t <= (snd $ snd $ bounds b)
leftOK  (Game b t) = extentLeft  t >= (fst $ fst $ bounds b)
rightOK (Game b t) = extentRight t <= (fst $ snd $ bounds b)

fits ∷ Game → Bool
fits g = noCollisions g && downOK g && leftOK  g && rightOK g

dropCompleteLines ∷ Board → ([Change] , Board)
dropCompleteLines b = let ((min₁ , min₂) , (max₁ , max₂)) = bounds b
                          xs =          range (min₁ , max₁)
                          ys = reverse (range (min₂ , max₂))
                      in dropCompleteLines' xs ys b

dropCompleteLines' ∷ [Integer] → [Integer] → Board → ([Change] , Board)
dropCompleteLines' _  []     b = return b
dropCompleteLines' xs (y:ys) b = if and [b ! (x , y) | x ← xs]
                                 then tell [Off (x , y) | x ← xs] >>
                                      tell [Delay]                >>
                                      shiftDown xs ys b           >>=
                                      emptyTopRow xs             >>=
                                      dropCompleteLines' xs ys
                                 else dropCompleteLines' xs ys b

shiftDown ∷ [Integer] → [Integer] → Board → ([Change] , Board)
shiftDown xs ys b =
  tell [if b ! (x , y) then On (x , y + 1) else Off (x , y + 1) | x ← xs , y ← ys] >>
  return (b // [((x , y + 1) , b ! (x , y)) | x ← xs , y ← ys])

emptyTopRow ∷ [Integer] → Board → ([Change] , Board)
emptyTopRow xs b =
  tell [Off (x , 0) | x ← xs] >>
  return (b // [((x , 0) , False) | x ← xs])

lockDown ∷ Game → Board
lockDown g@(Game b t) = b // zip (reifyGame g) (repeat True)

nextTetromino ∷ Shape → Game → ([Change] , Maybe Game)
nextTetromino s g = let b = lockDown g
                    in dropCompleteLines b >>= \ b' →
                       let ((min₁ , min₂) , (max₁ , max₂)) = bounds b
                           c₁ = (min₁ + max₁) `div` 2
                           c₂ = min₂
                           t = Tetromino (c₁ , c₂) s
                           g' = Game b' t
                       in tell (on g') >>
                          if noCollisions g'
                          then return $ Just g'
                          else return $ Nothing

createBoard ∷ Integer → Integer → Shape → (Game , [Change])
createBoard w h s = (g , on g)
  where b = listArray ((0,0) , (w-1,h-1)) (repeat False)
        t = Tetromino (w `div` 2 , 0) s
        g = Game b t

updateGame ∷ Event → Game → ([Change] , Game)
updateGame MoveDown g
  | fits (over (tetromino . center) (\ (x , y) → (x , y + 1)) g)
    = let g' = over (tetromino . center) (\ (x , y) → (x , y + 1)) g
      in (off g ++ on g' , g')
updateGame MoveLeft g
  | fits (over (tetromino . center) (\ (x , y) → (x - 1 , y)) g)
    = let g' = over (tetromino . center) (\ (x , y) → (x - 1 , y)) g
      in (off g ++ on g' , g')
updateGame MoveRight g
  | fits (over (tetromino . center) (\ (x , y) → (x + 1 , y)) g)
    = let g' = over (tetromino . center) (\ (x , y) → (x + 1 , y)) g
      in (off g ++ on g' , g')
updateGame Gravitate g
  | fits (over (tetromino . center) (\ (x , y) → (x , y + 1)) g)
    = updateGame MoveDown g >>= updateGame Gravitate
updateGame Tick g = updateGame MoveDown g
updateGame RotateCW g
  | fits (over (tetromino . shape) rotateShape g)
    = let g' = over (tetromino . shape) rotateShape g
      in (off g ++ on g' , g')
updateGame _ g = return g
