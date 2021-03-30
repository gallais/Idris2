module Data.Array

import Control.Monad.Identity

import Data.Bits
import Data.DPair
import Data.Nat
import Data.Nat.Order
import Data.Vect

%default total

public export
interface Monad m => Array m size arr elt | arr, elt where
  init' :  Maybe elt -> m arr
  read  :  arr -> Subset Nat (`LT` size) -> m elt
  write :  arr -> Subset Nat (`LT` size) -> elt -> m arr

export
init : (size : Nat) -> Array m size arr elt => Maybe elt -> m arr
init size @{p} = init' @{p}

export
tabulate : (n : Nat) -> Array m n arr elt =>
           (Subset Nat (`LT` n) -> elt) -> m arr
tabulate n f = do
  vs <- init {arr} {elt} n Nothing
  loop n (\ i, vs => write vs i (f i)) vs

  where
    zero : Subset Nat (`LT` S _)
    zero = Element Z ltZero

    succ : Subset Nat (`LT` bd) -> Subset Nat (`LT` S bd)
    succ (Element k prf) = Element (S k) (LTESucc prf)

    loop : (n : Nat) -> (Subset Nat (`LT` n) -> arr -> m arr) -> arr -> m arr
    loop Z     act vs = pure vs
    loop (S n) act vs = act zero vs >>= loop n (act . succ)

(lte32 : LTE size 32) => Array Identity size Bits32 Bool where
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
