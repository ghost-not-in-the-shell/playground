{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Game       as Game
import System.Random
import Tetromino
import UI.NCurses as NCurses

delay ∷ Integer
delay = 500

width ∷ Integer
width = 10

height ∷ Integer
height = 20

applyChanges ∷ Window → [Change] → Curses ()
applyChanges w [] = render >> return ()
applyChanges w (On  (x , y) : cs) = updateWindow w (moveCursor y x >> drawString "■") >> applyChanges w cs
applyChanges w (Off (x , y) : cs) = updateWindow w (moveCursor y x >> drawString " ") >> applyChanges w cs
applyChanges w (Delay       : cs) = getEvent w (Just delay) >> applyChanges w cs

keyEvents ∷ [(NCurses.Event , Game.Event)]
keyEvents = [ (EventSpecialKey KeyDownArrow  , MoveDown)
            , (EventSpecialKey KeyLeftArrow  , MoveLeft)
            , (EventSpecialKey KeyRightArrow , MoveRight)
            , (EventSpecialKey KeyUpArrow    , RotateCW)
            , (EventCharacter  'k'           , MoveDown)
            , (EventCharacter  'j'           , MoveLeft)
            , (EventCharacter  'l'           , MoveRight)
            , (EventCharacter  'i'           , RotateCW)
            , (EventCharacter  'g'           , Gravitate)
            , (EventCharacter  'q'           , Quit)
            ]

gameLoop ∷ Window → Game → Curses ()
gameLoop w g =
  getEvent w (Just delay) >>= \ me →
  case me of
    Nothing → let (cs , mg') = update Tick g
              in applyChanges w cs >>
                 case mg' of
                   Nothing → return ()
                   Just g' → gameLoop w g'
    Just k → let e = maybe None id (lookup k keyEvents)
             in case e of
                  Quit → return ()
                  _    → let (cs , Just g') = update e g
                         in applyChanges w cs >>
                            gameLoop w g'


main ∷ IO ()
main = newStdGen >>= \ gen →
       let (g , cs) = newGame width height gen
       in runCurses $ do
         w ← newWindow height width 0 0
         setEcho False
         setCursorMode CursorInvisible
         applyChanges w cs
         render
         gameLoop w g
         closeWindow w
