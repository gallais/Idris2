module Graphics.Netpbm

import Data.Bits
import Data.DPair
import Data.IOMatrix
import Data.String
import Data.Vect

import System.File

%default total

public export
data Format
--  ASCII | Binary
  = P1 -- | P4 -- Black and white
  | P2 -- | P5 -- Grayscale
  | P3 -- | P6 -- RGB

export
extension : Format -> String
extension P1 = "pbm"
extension P2 = "pgm"
extension P3 = "ppm"

export
Show Format where
  show P1 = "P1"
  show P2 = "P2"
  show P3 = "P3"

Cast Bits16 Nat where
  cast = believe_me . the Integer . cast

namespace Pixel

  public export
  record RGB where
    constructor MkRGB
    red   : Bits8
    green : Bits8
    blue  : Bits8

  public export
  Pixel : Format -> Type
  Pixel P1 = Bool
  Pixel P2 = Bits16
  Pixel P3 = RGB

  export
  toString : {fmt : Format} -> Pixel fmt -> String
  toString p = case fmt of
    P1 => if p then show 1 else show 0
    P2 => show p
    P3 => unwords $ map show [ p.red, p.green, p.blue ]

  export
  defaultPixel : {fmt : Format} -> Pixel fmt
  defaultPixel = case fmt of
    P1 => False
    P2 => 0
    P3 => MkRGB 0 0 0

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

toASCII : {fmt : Format} -> Image fmt -> IO String
toASCII (MkImage cnt)
  = do img <- image
       pure $ unlines $ header ++ maxVal ++ img ++ [""]

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
      P2 => [show (the Bits16 oneBits)]
      P3 => [show (the Bits8  oneBits)]

    image : IO (List String)
    image =
      for [0..(h-1)] $ \ j =>
        map unwords $
        for [0..(w-1)] $ \ i =>
          do val <- read cnt i j
             pure $ Pixel.toString (fromMaybe defaultPixel val)

export
writeImage : {fmt : _} -> Image fmt -> String -> IO (Either FileError ())
writeImage img fp = do
  str <- toASCII img
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
diags k = fromVect $ magnify 50 50 vals

  where

    rng : Vect k (Subset Nat (`LT` k))
    rng = range

    pixel : Nat -> Nat -> Bool
    pixel i j = mod (i + j) 5 == 0

    vals : Vect k (Vect k Bool)
    vals = map (\ i => map ((pixel `on` fst) i) rng) rng

export
lines : Nat -> IO (Image P2)
lines n = fromVect $ magnify 700 50 $ [map init range] where

  maxVal : Pixel P2
  maxVal = oneBits

  step : Nat
  step = div (integerToNat (cast maxVal)) (pred n)

  init : Subset Nat (`LT` n) -> Bits16
  init i = cast (natToInteger (fst i * step))

export
circle : Nat -> IO (Image P1)
circle r = let
  Size : Nat := 3 * r
  r2 : Nat := r * r
  tolerance : Nat := div r 2 * div r 2
  center : Nat := r + div r 2
  dist : Nat -> Nat -> Nat := \ m, n => max (minus m n) (minus n m)

  pixel : Nat -> Nat -> Bool := \i, j =>
      let x = dist i center in
      let y = dist j center in
      dist r2 (x*x + y*y) <= tolerance

  rng : Vect Size (Subset Nat (`LT` Size)) := range

  in fromVect $ map (\ i => map ((pixel `on` fst) i) rng) rng

export
lgbt : IO (Image P3)
lgbt = fromVect $ magnify 500 70
  [[ MkRGB 255 0   24
   , MkRGB 255 165 44
   , MkRGB 255 255 65
   , MkRGB 0   128 24
   , MkRGB 0   0   249
   , MkRGB 134 0   125
  ]]

export
test : IO ()
test = do
  ignore $ writeImage !(checker 12) "checker"
  ignore $ writeImage !(diags 12)   "diags"
  ignore $ writeImage !(lines 10)   "lines"
  ignore $ writeImage !lgbt         "lgbt"
  ignore $ writeImage !(circle 200) "circle"
