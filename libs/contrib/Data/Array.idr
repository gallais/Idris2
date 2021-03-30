module Data.Array

import Control.Monad.Identity

import Data.Bits
import Data.DPair
import Data.Nat
import Data.Nat.Order
import Data.Nat.Division
import Data.Vect

import Data.IOArray.Prims

%default total

public export
interface Monad m => Array m size arr elt | arr, elt where
  init' :  Maybe elt -> m arr
  read  :  arr -> Subset Nat (`LT` size) -> m elt
  write :  arr -> Subset Nat (`LT` size) -> elt -> m arr
  --       ^--- cannot be made linear because (set/clear)Bit are currently not

export
init : (size : Nat) -> (0 arr : Type) ->
       Array m size arr elt => Maybe elt -> m arr
init size arr @{p} = init' @{p}

export
tabulate : (n : Nat) -> Array m n arr elt =>
           (Subset Nat (`LT` n) -> elt) -> m arr
tabulate n f = do
  let dflt : Maybe elt = Nothing
  vs <- init n arr dflt
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


{size : Nat} -> Array IO size (ArrayData Bits32) Bool where

  init' dflt = let bits : Bits32 = runIdentity (init 32 Bits32 dflt) in
               primIO (prim__newArray (cast (divCeilNZ size 32 SIsNotZ)) bits)

  read arr (Element i ltSize)
    = do let dm : (Nat, Nat)
             dm = divmodNatNZ i 32 SIsNotZ
         let iword : Int = cast (fst dm)
         let ibit  : Subset Nat (`LT` 32)
                   = Element (snd dm) (boundDivmodNatNZ i 32 SIsNotZ)
         bits <- primIO (prim__arrayGet arr iword)
         pure $ runIdentity $ read {elt = Bool} bits ibit

  write arr (Element i ltSize) elt
    = do let dm : (Nat, Nat)
             dm = divmodNatNZ i 32 SIsNotZ
         let iword : Int = cast (fst dm)
         let ibit  : Subset Nat (`LT` 32)
                   = Element (snd dm) (boundDivmodNatNZ i 32 SIsNotZ)
         bits <- primIO (prim__arrayGet arr iword)
         let bits = runIdentity $ write bits ibit elt
         primIO (prim__arraySet arr iword bits)
         pure arr
