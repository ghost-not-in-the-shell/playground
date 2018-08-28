{-# LANGUAGE UnicodeSyntax #-}
module Main where

import UI.NCurses as NCurses
import System.Random
import Tetromino
import Game as Game

width ∷ Integer
width = 20

height ∷ Integer
height = 40

delay ∷ Integer
delay = 1000

reifyChanges ∷ Window → [Change] → Curses ()
reifyChanges w [] = return ()
reifyChanges w (On  (x , y) : cs) = updateWindow w $ moveCursor (fromIntegral x) (fromIntegral y) >> drawString "■"
reifyChanges w (Off (x , y) : cs) = updateWindow w $ moveCursor (fromIntegral x) (fromIntegral y) >> drawString " "
reifyChanges w (Delay       : cs) = getEvent w (Just delay) >> return ()

keyEvents ∷ [(NCurses.Event , Game.Event)]
keyEvents = [ (EventSpecialKey KeyDownArrow  , MoveDown)
            , (EventSpecialKey KeyLeftArrow  , MoveLeft)
            , (EventSpecialKey KeyRightArrow , MoveRight)
            , (EventSpecialKey KeyUpArrow    , RotateCW)
            , (EventCharacter  'q'           , Quit)
            , (EventCharacter  'Q'           , Quit)
            , (EventCharacter  'g'           , Gravitate)
            , (EventCharacter  'G'           , Gravitate)
            ]

newShape ∷ IO Shape
newShape = randomRIO (minBound ∷ Shape , maxBound ∷ Shape)

{-
gameLoop ∷ Window → Game → IO ()
gameLoop w g = do
  me ← getEvent w (Just delay)
  case me of
    Nothing → do
      s ← newShape
      let (m , cs) = nextTetromino g s
      reifyChanges w cs
      case m of
        Just g' → gameLoop w g'
        Nothing → return ()
    Just e → do
      let (g' , cs) = updateGame (maybe None id (lookup e keyEvents))
      reifyChanges w cs
      gameLoop w g'
-}

main ∷ IO ()
main = newStdGen >>= \ g →
  let ss = randoms g ∷ [Shape]
      game = Game (makeBoard width height) (head ss) (tail ss)
  in runCurses $ do
  w ← newWindow height width 0 0
  closeWindow w
  return ()
