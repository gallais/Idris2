module Graphics.Netpbm

import Data.Bits
import Data.DPair
import Data.IOMatrix
import Data.Fin
import Data.Nat
import Data.String
import Data.Vect

import System.File

%default total

public export
data Format
  = P1 -- | P4
  | P2 -- | P5

export
extension : Format -> String
extension P1 = "pbm"
extension P2 = "pgm"

export
Show Format where
  show P1 = "P1"
  show P2 = "P2"

namespace Pixel

  public export
  Pixel : Format -> Type
  Pixel P1 = Bool
  -- Pixel P4 = Bool
  Pixel P2 = Bits16

  export
  toNat : (fmt : Format) -> Maybe (Pixel fmt) -> Nat

  toNat P1 (Just True) = 1
  toNat P1 _           = 0

  toNat P2 (Just n)    = integerToNat (cast n)
  toNat P2 _           = 0

namespace Image

  export
  record Image (fmt : Format) where
    constructor MkImage
    content : IOMatrix (Pixel fmt)

  export
  fromVect : {m, n : Nat} -> Vect m (Vect n (Pixel fmt)) -> IO (Image fmt)
  fromVect = map MkImage . fromVect

export
width : Image fmt-> Nat
width = integerToNat . cast . width . content

export
height : Image fmt -> Nat
height = integerToNat . cast . height . content

toASCII : {fmt : Format} -> (Maybe (Pixel fmt) -> Nat) -> Image fmt -> IO String
toASCII toNat (MkImage cnt)
  = do img <- image
       pure $ unlines $ header ++ maxVal ++ img

  where

    w : Int
    w = width cnt

    h : Int
    h = height cnt

    header : List String
    header = [ show fmt, unwords [show w, show h] ]

    maxVal : List String
    maxVal = case fmt of
      P1 => []
      P2 => [show (the (Pixel P2) oneBits)]

    image : IO (List String)
    image =
      for [0..(w-1)] $ \ i =>
        map unwords $ for [0..(h-1)] $ \ j =>
          do val <- read cnt i j
             pure $ show (toNat val)

export
writeImage : {fmt : _} -> Image fmt -> String -> IO (Either FileError ())
writeImage img fp = do
  str <- toASCII (toNat _) img
  writeFile (fp ++ "." ++ extension fmt) str

export
magnify : (k, l : Nat) -> Vect m (Vect n a) -> Vect (m * k) (Vect (n * l) a)
magnify k l = magnifyVect . map magnifyVect where

  magnifyVect : {scale : Nat} -> Vect len b -> Vect (len * scale) b
  magnifyVect [] = []
  magnifyVect (a :: as) = replicate scale a ++ magnifyVect as

export
checker : Nat -> IO (Image P1)
checker k = fromVect $ magnify 50 50 $
  let l1 = cycle k True False
      l2 = map not l1
  in cycle k l1 l2

  where

    cycle : (n : Nat) -> a -> a -> Vect n a
    cycle Z     l1 l2 = []
    cycle (S n) l1 l2 = l1 :: cycle n l2 l1

export
diags : Nat -> IO (Image P1)
diags k = fromVect $ magnify 50 50 $ vals
  where

    rng : Vect k (Subset Nat (`LT` k))
    rng = range

    pixel : Nat -> Nat -> Bool
    pixel i j = mod (i + j) 5 == 0

    vals : Vect k (Vect k Bool)
    vals = map (\ i => map ((pixel `on` fst) i) rng) rng

export
lines : Nat -> IO (Image P2)
lines n = fromVect $ magnify 50 700 $ map init range where

  maxVal : Pixel P2
  maxVal = oneBits

  step : Nat
  step = div (integerToNat (cast maxVal)) (pred n)

  init : Subset Nat (`LT` n) -> Vect 1 Bits16
  init i = [cast (natToInteger (fst i * step))]

export

test : IO ()
test = do
  ignore $ writeImage !(checker 12) "checker"
  ignore $ writeImage !(diags 12) "diags"
  ignore $ writeImage !(lines 10) "lines"
