{-# LANGUAGE TemplateHaskell, UnicodeSyntax #-}
module Game where

import Control.Monad.Writer
import Control.Lens
import Data.Array
import System.Random
import Tetromino

type Board = Array Coord Bool

data Event = MoveDown
           | MoveLeft
           | MoveRight
           | Gravitate
           | RotateCW
           | Tick
           | Quit
           | None
           deriving (Show)

data Change = On  Coord
            | Off Coord
            | Delay
            deriving (Show)

data Game = Game { _board     ∷ Board
                 , _tetromino ∷ Tetromino
                 , _shapes    ∷ [Shape]
                 }
            deriving (Show)

makeLenses ''Game

reify ∷ Game → [Coord]
reify (Game b t _) = filter (inRange (bounds b)) $ absoluteCoord t

on  ∷ Game → [Change]
off ∷ Game → [Change]
on  g = map On  (reify g)
off g = map Off (reify g)

noCollisions ∷ Game → Bool
noCollisions g@(Game b _ _) = not $ or $ map (b !) $ reify g

downOK  ∷ Game → Bool
leftOK  ∷ Game → Bool
rightOK ∷ Game → Bool
downOK  g@(Game b t _) = extentDown  t <= (snd $ snd $ bounds b)
leftOK  g@(Game b t _) = extentLeft  t >= (fst $ fst $ bounds b)
rightOK g@(Game b t _) = extentRight t <= (fst $ snd $ bounds b)

fits ∷ Game → Bool
fits g = noCollisions g && downOK g && leftOK g && rightOK g

dropCompleteLines ∷ Board → ([Change] , Board)
dropCompleteLines b = let ((min₁ , min₂) , (max₁ , max₂)) = bounds b
                          is =          range (min₁ , max₁)
                          js = reverse (range (min₂ , max₂))
                      in loop is js b
  where loop ∷ [Integer] → [Integer] → Board → ([Change] , Board)
        loop _  []     b = ([] , b)
        loop is (j:js) b = if and [b ! (i , j) | i ← is]
                           then tell [Off (i , j) | i ← is] >>
                                tell [Delay]                >>
                                shiftDown is js b           >>=
                                emptyTopRow is              >>=
                                loop is js
                           else loop is js b

        shiftDown ∷ [Integer] → [Integer] → Board → ([Change] , Board)
        shiftDown is js b =
          tell [if b ! (i , j) then On (i , j+1) else Off (i , j+1) | i ← is , j ← js] >>
          return (b // [((i , j+1) , b ! (i , j)) | i ← is , j ← js])

        emptyTopRow ∷ [Integer] → Board → ([Change] , Board)
        emptyTopRow is b =
          tell [Off (i , 0) | i ← is] >>
          return (b // [((i , 0) , False) | i ← is])

startPos ∷ Game → Coord
startPos (Game b _ _) = let ((min₁ , min₂) , (max₁ , max₂)) = bounds b
                            c₁ = (min₁ + max₁) `div` 2
                            c₂ = min₂
                        in (c₁ , c₂)

newGame ∷ Integer → Integer → StdGen → (Game , [Change])
newGame w h gen =
  let b      = listArray ((0 , 0) , (w-1 , h-1)) (repeat False)
      (s:ss) = randoms gen
      t      = Tetromino (w `div` 2 , 0) s
      g      = Game b t ss
  in (g , on g)

lockDown ∷ Game → ([Change] , Maybe Game)
lockDown g@(Game b t (s:ss)) =
  dropCompleteLines (b // zip (reify g) (repeat True)) >>= \ b' →
  let t'  = Tetromino (startPos g) s
      g'  = Game b' t' ss
  in tell (on g') >>
  if noCollisions g'
  then return $ Just g'
  else return $ Nothing

moveDown ∷ Game → Game
moveDown = over (tetromino . center) (\ (x , y) → (x , y + 1))

moveLeft ∷ Game → Game
moveLeft = over (tetromino . center) (\ (x , y) → (x - 1 , y))

moveRight ∷ Game → Game
moveRight = over (tetromino . center) (\ (x , y) → (x + 1 , y))

rotateCW ∷ Game → Game
rotateCW = over (tetromino . shape) rotateShape

update ∷ Event → Game → ([Change] , Maybe Game)
update MoveDown  g
  | fits (moveDown  g) = (off g ++ on (moveDown  g) , Just (moveDown  g))
update MoveLeft  g
  | fits (moveLeft  g) = (off g ++ on (moveLeft  g) , Just (moveLeft  g))
update MoveRight g
  | fits (moveRight g) = (off g ++ on (moveRight g) , Just (moveRight g))
update RotateCW  g
  | fits (rotateCW  g) = (off g ++ on (rotateCW  g) , Just (rotateCW  g))
update Gravitate g
  | fits (moveDown  g) = update MoveDown  g >>= \ (Just g') →
                         update Gravitate g'
update Tick      g = if fits (moveDown g)
                     then update MoveDown g
                     else lockDown        g
update _         g = return $ Just g
