module Graphics.Netpbm

import Data.IOMatrix
import Data.String
import Data.Vect
import System.File

%default total

data Format = P1 -- | P4

public export
Pixel : Format -> Type
Pixel P1 = Bool
-- Pixel P4 = Bool

export
record Image (fmt : Format) where
  constructor MkImage
  content : IOMatrix (Pixel fmt)

export
width : Image fmt-> Nat
width = integerToNat . cast . width . content

export
height : Image fmt -> Nat
height = integerToNat . cast . height . content

p1ToString : Image P1 -> IO String
p1ToString (MkImage cnt)
  = unlines . (header ++) <$> image where

    w : Int
    w = width cnt

    h : Int
    h = height cnt

    header : List String
    header = [ "P1", unwords [show w, show h] ]

    toNat : Maybe Bool -> Nat
    toNat (Just True) = 1
    toNat _ = 0

    image : IO (List String)
    image = for [0..(h-1)] $ \ i =>
              map unwords $ for [0..(w-1)] $ \ j =>
                show . toNat <$> read cnt i j

export
writeImage : {fmt : _} -> Image fmt -> String -> IO (Either FileError ())
writeImage img fp = do
  str <- case fmt of
           P1 => p1ToString img
  writeFile fp str

magnify : (k : Nat) -> Vect m (Vect n a) -> Vect (m * k) (Vect (n * k) a)
magnify k = magnifyVect . map magnifyVect where

  magnifyVect : Vect len b -> Vect (len * k) b
  magnifyVect [] = []
  magnifyVect (a :: as) = replicate k a ++ magnifyVect as

export
checker : Nat -> IO (Image P1)
checker k = map MkImage $ fromVect $ magnify 25 $
  let l1 = cycle k True False
      l2 = map not l1
  in cycle k l1 l2

  where

    cycle : (n : Nat) -> a -> a -> Vect n a
    cycle Z     l1 l2 = []
    cycle (S n) l1 l2 = l1 :: cycle n l2 l1

test : IO ()
test = ignore $ writeImage !(checker 12) "test.pbm"
