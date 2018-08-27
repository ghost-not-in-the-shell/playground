{-# LANGUAGE UnicodeSyntax #-}
module Main where

import UI.NCurses
import System.Random
import Tetromino
import Board

delay ∷ Integer
delay = 1000

reifyChanges ∷ Window → [Change] → Curses ()
reifyChanges w [] = return ()
reifyChanges w (On  (x , y) : cs) = updateWindow w $ moveCursor (fromIntegral x) (fromIntegral y) >> drawString "■"
reifyChanges w (Off (x , y) : cs) = updateWindow w $ moveCursor (fromIntegral x) (fromIntegral y) >> drawString " "
reifyChanges w (Delay       : cs) = getEvent w (Just delay) >> return ()

main ∷ IO ()
main = return ()
