{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, UnicodeSyntax #-}
module Board where
import Tetromino
import Control.Monad.Writer
import Control.Lens
import Data.Array
import Prelude hiding (Left, Right)

type Board = Array Coord Bool

data Event = CW | Down | Left | Right | Drop | Tick | Quit | None
  deriving (Eq)

data Change = On Coord | Off Coord | Delay

data Game = Game { _board ∷ Board, _tetromino ∷ Tetromino }

makeLenses ''Game

reify ∷ Board → Tetromino → [Coord]
reify b = filter (inRange (bounds b)) . reifyT

on ∷ Board → Tetromino → [Change]
on b t = map On (reify b t)

off ∷ Board → Tetromino → [Change]
off b t = map Off (reify b t)

noCollisions ∷ Game → Bool
noCollisions (Game b t) = not $ or $ map (b !) $ reify b t

downOK ∷ Game → Bool
downOK (Game b t) = extentDown t <= (snd $ snd $ bounds b)

leftOK ∷ Game → Bool
leftOK (Game b t) = extentLeft t >= (fst $ fst $ bounds b)

rightOK ∷ Game → Bool
rightOK (Game b t) = extentRight t <= (fst $ snd $ bounds b)

fits ∷ Game → Bool
fits g = noCollisions g && downOK g && leftOK g && rightOK g

dropCompleteLines ∷ Board → ([Change],Board)
dropCompleteLines b = let ((min₁,min₂),(max₁,max₂)) = bounds b
                          xs = range (min₁,max₁)
                          ys = range (min₂,max₂)
                      in dropCompleteLines' xs (reverse ys) b

dropCompleteLines' ∷ [Int] → [Int] → Board → ([Change],Board)
dropCompleteLines' _  []     b = ([],b)
dropCompleteLines' xs (y:ys) b = if and [b ! (x , y) | x ← xs]
                                then tell [Off (x , y) | x ← xs] >>
                                     tell [Delay] >>
                                     shiftDown xs ys b >>= \ b' →
                                     emptyTopRow xs b' >>= \ b'' →
                                     tell [Delay] >>
                                     dropCompleteLines' xs ys b''
                                else dropCompleteLines' xs ys b

shiftDown ∷ [Int] → [Int] → Board → ([Change],Board)
shiftDown xs ys b = (
                     [(if b ! (x , y) then On else Off) (x , y + 1) | y ← ys , x ← xs] ,
                     b // [((x , y + 1) , b ! (x,y)) | y ← ys , x ← xs]
                    )

emptyTopRow ∷ [Int] → Board → ([Change],Board)
emptyTopRow xs b = ([Off (x , 0) | x ← xs] , b // [((x,0),False) | x ← xs])

lockDown :: Game → Board
lockDown (Game b t) = b // zip (reify b t) (repeat True)

nextTetromino ∷ Shape → Game → ([Change],Maybe Game)
nextTetromino s g = let b = lockDown g
                    in dropCompleteLines b >>= \ b' →
                       let g' = Game b' t
                           ((min₁,min₂),(max₁,max₂)) = bounds b
                           c₁ = (min₁ + max₁) `div` 2
                           c₂ = min₂
                           t = Tetromino (c₁ , c₂) s
                       in tell (on b' t) >>
                          if noCollisions g'
                          then return $ Just g'
                          else return $ Nothing
                           

createBoard ∷ Int → Int → Shape → (Game , [Change])
createBoard w h s = (g , on b t)
  where b = listArray ((0,0),(w-1,h-1)) (repeat False)
        t = Tetromino (w `div` 2 , 0) s
        g = Game b t

getChanges ∷ Event → Game → ([Change],Game)
getChanges Down g@(Game b t)
  | fits (over (tetromino . center) (\ (x , y) → (x , y + 1)) g)
    = let t' = over center (\ (x , y) → (x , y + 1)) t
      in (off b t ++ on b t' , Game b t')
getChanges Left g@(Game b t)
  | fits (over (tetromino . center) (\ (x , y) → (x - 1 , y)) g)
    = let t' = over center (\ (x , y) → (x - 1 , y)) t
      in (off b t ++ on b t' , Game b t')
getChanges Right g@(Game b t)
  | fits (over (tetromino . center) (\ (x , y) → (x + 1 , y)) g)
    = let t' = over center (\ (x , y) → (x + 1 , y)) t
      in (off b t ++ on b t' , Game b t')
getChanges Tick g = getChanges Down g
getChanges Drop g
  | fits (over (tetromino . center) (\ (x , y) → (x , y + 1)) g)
    = getChanges Down g >>= \ g' →
      getChanges Drop g'
getChanges CW g@(Game b t)
  | fits (over (tetromino . shape) rotateS g)
    = let t' = over shape rotateS t
      in (off b t ++ on b t' , Game b t')
getChanges _ g = ([] , g)
