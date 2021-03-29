module Data.Array

import Data.DPair
import Data.Nat
import Data.Vect

%default total

public export
interface Array size arr elt | arr, elt where
  init' : HasIO io => Maybe elt -> io arr
  read  : HasIO io => arr -> Subset Nat (`LT` size) -> io elt
  write : HasIO io => arr -> Subset Nat (`LT` size) -> elt -> io ()

export
init : HasIO io => (n : Nat) -> Array n arr elt => Maybe elt -> io arr
init n = init'

export
tabulate : HasIO io => (n : Nat) -> Array n arr elt =>
           (Subset Nat (`LT` n) -> elt) -> io arr
tabulate n f = do
  vs <- init n (the (Maybe elt) Nothing)
  loop n (\ i => write vs i (f i))
  pure vs

  where
    zero : Subset Nat (`LT` S _)
    zero = Element Z ltZero

    succ : Subset Nat (`LT` bd) -> Subset Nat (`LT` S bd)
    succ (Element k prf) = Element (S k) (LTESucc prf)

    loop : (n : Nat) -> (Subset Nat (`LT` n) -> io ()) -> io ()
    loop Z act = pure ()
    loop (S n) act = do act zero; loop n (act . succ)
