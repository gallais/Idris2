module Control.Monad.Random.Interface

import Data.Bits
import Control.Monad.State

%default total

public export
interface Monad m => MonadRandom r m | m where
  constructor MkMonadRandom
  ||| Generate a random value
  random : m r

export
randoms : MonadRandom r m => (r -> a) -> m a
randoms f = map f random


------------------------------------------------------------------------
-- Pseudo-random generators

record Generator (a : Type) where
  constructor MkGenerator
  multiplier : a
  increment : a
  modulus : a

step : Integral a => Generator a -> a -> a
step (MkGenerator mul inc mod) x = (mul * x + inc) `Prelude.mod` mod

withGenerator : Integral a => Monad m => Generator a -> StateT a m a
withGenerator gen = do
  n <- gets (step gen)
  n <$ put n

export
record PseudoRandom (nm : String) (m : Type -> Type) (a : Type) where
  constructor MkPseudoRandom
  getPseudoRandom : StateT Int64 m a

export
Functor m => Functor (PseudoRandom nm m) where
  map f (MkPseudoRandom ma) = MkPseudoRandom (map f ma)

export
Monad m => Applicative (PseudoRandom nm m) where
  pure x = MkPseudoRandom (pure x)
  MkPseudoRandom mf <*> MkPseudoRandom ma = MkPseudoRandom (mf <*> ma)

export
Monad m => Monad (PseudoRandom nm m) where
  MkPseudoRandom ma >>= k = MkPseudoRandom (ma >>= getPseudoRandom . k)

||| @ma   effectful computation requiring random
||| @seed seed value to kickstart the random generator with
export
runPseudoRandom : Functor m => (0 nm : String) -> (ma : PseudoRandom nm m a) -> (seed : Int64) -> m a
runPseudoRandom _ ma seed = evalStateT seed (getPseudoRandom ma)

export
Monad m => MonadRandom Int64 (PseudoRandom "glibc" m) where
  random = MkPseudoRandom $ withGenerator $ MkGenerator 1103515245 12345 (1 `shiftL` 31)

export
Monad m => MonadRandom Int64 (PseudoRandom "random0" m) where
  random = MkPseudoRandom $ withGenerator $ MkGenerator 8121 28411 134456
