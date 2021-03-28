module Data.IOMatrix

import Data.IOArray.Prims
import Data.Vect

export
record IOMatrix a where
  constructor MkIOMatrix
  maxWidth  : Int
  maxHeight : Int
  content   : ArrayData (Maybe a)

export
width : IOMatrix a -> Int
width = maxWidth

export
height : IOMatrix a -> Int
height = maxHeight

export
new : HasIO io => (width, height : Int) -> io (IOMatrix a)
new width height
  = pure $ MkIOMatrix width height
         !(primIO (prim__newArray (width * height) Nothing))

toPosition : IOMatrix a -> Int -> Int -> Maybe Int
toPosition (MkIOMatrix w h arr) i j
  = do guard (not (i < 0 || j < 0 || i >= w || j >= h))
       pure (i * h + j)

export
write : HasIO io => IOMatrix a -> Int -> Int -> a -> io Bool
write mat i j el = case toPosition mat i j of
  Nothing => pure False
  Just pos => True <$ primIO (prim__arraySet (content mat) pos (Just el))

export
read : HasIO io => IOMatrix a -> Int -> Int -> io (Maybe a)
read mat i j = case toPosition mat i j of
  Nothing => pure Nothing
  Just pos => primIO (prim__arrayGet (content mat) pos)

export
fromVect : HasIO io => {m, n : Nat} -> Vect m (Vect n a) -> io (IOMatrix a)
fromVect ass = do
  mat <- new (cast n) (cast m)
  populate mat
  pure mat

  where

    populate : IOMatrix a -> io ()
    populate mat = writeAll 0 ass where


      writeRow : Int -> Int -> Vect w a -> io ()
      writeRow i j [] = pure ()
      writeRow i j (a :: as) = do ignore (write mat i j a)
                                  writeRow i (j+1) as

      writeAll : Int -> Vect h (Vect w a) -> io ()
      writeAll i [] = pure ()
      writeAll i (as :: ass) = do writeRow i 0 as
                                  writeAll (i+1) ass
