module Data.Array

import Data.Bits
import Data.DPair
import Data.Nat
import Data.Nat.Order
import Data.Vect

%default total

public export
interface Array size arr elt | arr, elt where
  init' : HasIO io => Maybe elt -> io arr
  read  : HasIO io => arr -> Subset Nat (`LT` size) -> io elt
  write : HasIO io => arr -> Subset Nat (`LT` size) -> elt -> io arr

export
init : HasIO io => (n : Nat) -> Array n arr elt => Maybe elt -> io arr
init n = init'

export
tabulate : HasIO io => (n : Nat) -> Array n arr elt =>
           (Subset Nat (`LT` n) -> elt) -> io arr
tabulate n f = do
  vs <- init n (the (Maybe elt) Nothing)
  loop n (\ i, vs => write vs i (f i)) vs

  where
    zero : Subset Nat (`LT` S _)
    zero = Element Z ltZero

    succ : Subset Nat (`LT` bd) -> Subset Nat (`LT` S bd)
    succ (Element k prf) = Element (S k) (LTESucc prf)

    loop : (n : Nat) -> (Subset Nat (`LT` n) -> arr -> io arr) -> arr -> io arr
    loop Z     act vs = pure vs
    loop (S n) act vs = act zero vs >>= loop n (act . succ)

(lte32 : LTE size 32) => Array size Bits32 Bool where
  init' (Just True) = pure oneBits
  init' _ = pure zeroBits

  read arr (Element i ltSize)
    = let 0 bound : LT i 32 = LTEIsTransitive _ _ _ ltSize lte32 in
      pure (testBit arr (Element i bound))

  write arr (Element i ltSize) elt
    = let 0 bound : LT i 32 = LTEIsTransitive _ _ _ ltSize lte32
          act : Bits32 -> Subset Nat (`LT` 32) -> Bits32
          act = if elt then setBit else clearBit
      in
      pure $ act arr (Element i bound)
