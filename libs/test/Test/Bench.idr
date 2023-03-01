||| The content of this module is based on the Haskell library
||| criterion-measurement: https://github.com/haskell/criterion/

module Test.Bench

import Data.Fin
import Data.Maybe
import Data.Stream
import Data.String
import Data.Vect

import System.Clock

%default total

public export
record Benchmarkable where
  constructor MkBenchmarkable
  {0 env : Type}
  allocEnv : Int64 -> IO env
  cleanEnv : Int64 -> env -> IO ()
  runRepeatedly : env -> Int64 -> IO ()
  perRun : Bool

%inline
noop : Applicative m => a -> m ()
noop = const $ pure ()

export %inline
toBenchmarkable : (Int64 -> IO ()) -> Benchmarkable
toBenchmarkable f = MkBenchmarkable noop (const noop) (const f) False

public export
record Measured where
  constructor MkMeasured
  measTime : Double
  measCpuTime : Double
  -- measCycle : Double
  measIters : Int64
  -- measAllocated : Int64
  -- measPeakMbAllocated : Int64
  -- measNumGcs : Int64
  -- measBytesCopied : Int64
  -- measMutatorWallSeconds : Double
  -- measMutatorCpuSeconds : Double
  -- measGcWallSeconds : Double
  -- measGcCpuSeconds : Double

combineResults : (Measured, Double) -> (Measured, Double) -> (Measured, Double)
combineResults (m1, _) (m2, d2) = (m3, d2) where

  combine : (a -> a -> a) -> (Measured -> a) -> a
  combine g sel = sel m1 `g` sel m2

  add : Num a => (Measured -> a) -> a
  add = combine (+)

  m3 : Measured
  m3 = MkMeasured
      { measTime               = add measTime
      , measCpuTime            = add measCpuTime
      , measIters              = add measIters
      }

-- ARGH! We don't have these predicates, do we?
fromDouble : Double -> Maybe Double
-- fromDouble d = d <$ guard (not (isInfinite d || isNaN d))
fromDouble = Just

export
rescale : Measured -> Measured
rescale m = { measTime $= d, measCpuTime $= d } m

  where

    iters : Double
    iters = cast $ measIters m

    d : Double -> Double
    d k = maybe k (/ iters) (fromDouble k)

data Benchmark : Type where
  ABenchmark : String -> Benchmarkable -> Benchmark
  ABenchGroup : String -> List Benchmark -> Benchmark

addPrefix : String -> String -> String
addPrefix "" desc = desc
addPrefix pfx desc = "\{pfx}/\{desc}"


nf : (a -> b) -> a -> Benchmarkable
nf f x = toBenchmarkable $ go Nothing where

  %noinline
  go : Maybe b -> Int64 -> IO ()
  go _ n
    = ifThenElse (n <= 0) (pure ())
    $ go (Just (f x)) (assert_smaller n (n-1))

%inline
runBenchmarkable :
  Benchmarkable ->
  Int64 ->
  (a -> a -> a) ->
  (Int64 -> IO () -> IO a) ->
  IO a
runBenchmarkable (MkBenchmarkable allocEnv cleanEnv runRepeatedly perRun) i comb f
  = ifThenElse perRun (work >>= go (i - 1)) work where

  %inline
  count : Int64
  count = ifThenElse perRun 1 i

  %inline
  work : IO a
  work = do
    env <- allocEnv count
    let run = runRepeatedly env count
    v <- f count run
    cleanEnv count env
    pure v

  go : Int64 -> a -> IO a
  go 0 res = pure res
  go n res = work >>= go (assert_smaller n (n-1)) . comb res

%inline
runBenchmarkable' :
  Benchmarkable ->
  Int64 ->
  IO ()
runBenchmarkable' bm i = runBenchmarkable bm i (\ (), () => ()) (const id)

-- disgusting hack
toDouble : Clock type -> Double
toDouble (MkClock seconds nanoseconds)
  = cast "\{show seconds}.\{let str = show nanoseconds in replicate (minus 9 $ length str) '0' ++ str}"

%inline
getTime : IO Double
getTime = toDouble <$> clockTime UTC

%inline
getCpuTime : IO Double
getCpuTime = toDouble <$> clockTime Monotonic


%inline
measure :
  Benchmarkable -> -- Operation to benchmark
  Int64 -> -- Number of iterations
  IO (Measured, Double)
measure bm i = runBenchmarkable bm i combineResults $ \ n, act => do
  -- initializeTime
  -- We don't have this but criterion claims it's crucial with some OSs
  -- https://hackage.haskell.org/package/criterion-measurement-0.2.1.0/docs/Criterion-Measurement.html#v:initializeTime

  startTime <- getTime
  startCpuTime <- getCpuTime
  act
  endTime <- getTime
  endCpuTime <- getCpuTime

  let m = MkMeasured
        { measTime = max 0 (endTime - startTime)
        , measCpuTime = max 0 (endCpuTime - startCpuTime)
        , measIters = n
        }
  pure (m, endTime)

%inline
threshold : Double
threshold = 0.03

series : Stream Int64
series = squish $ unfoldr step 1 where

  step : Double -> (Int64, Double)
  step d = let d = d * 1.05 in (cast d, d)

  squish : Stream Int64 -> Stream Int64
  squish (i :: j :: is)
    = assert_total $ ifThenElse (i == j)
       (squish (i :: is))
       (i :: squish (j :: is))

runBenchmark :
  Benchmarkable ->
  Double ->
  IO (List Measured, Double)
runBenchmark bm timeLimit = do
  -- initializeTime
  -- We don't have this but criterion claims it's crucial with some OSs
  runBenchmarkable' bm 1
  startTime <- getTime
  let loop : Stream Int64 -> Double -> Int64 -> SnocList Measured -> IO (List Measured, Double)
      loop (i :: is) prev count acc = do
        (m, endTime) <- measure bm i
        let overThresh = max 0 (measTime m - threshold) + prev
        let totalTime = endTime - startTime
        ifThenElse
          (totalTime >= timeLimit &&
           overThresh > threshold * 10 &&
           count >= 4)
          (pure (acc <>> [], totalTime))
          (assert_total $ loop is overThresh (count+1) (acc :< m))
  loop series 0 0 [<]


------------------------------------------------------------------------
-- Necessary dependencies ported from the statistics package
-- https://hackage.haskell.org/package/statistics
-- NB: this is way less efficient than that package.
-- TODO: fix that

oops : String -> a
oops str = assert_total (idris_crash str)

weightedAvg :
  Int -> -- desired quantile
  Int -> -- number of quantiles
  List Double -> -- sample data
  Double
weightedAvg k q [] = oops "Sample is empty"
weightedAvg k q [v] = v
weightedAvg k q x@(hd :: tl)
  = ifThenElse (q < 2) (oops "At least 2 quantiles needed")
  $ ifThenElse (k == q) (foldl max hd tl)
  $ ifThenElse (not (k >= 0 || k < q)) (oops "Wrong quantile number")
  $ xj + g * (xj1 - xj)

  where

    n : Nat
    n = length x

    idx : Double
    idx = (cast n - 1) * cast k / cast q

    j : Nat
    j = cast idx

    g : Double
    g = idx  - cast j

    sx : List Double
    sx = sort x

    xj : Double
    xj = fromMaybe (oops "The IMPOSSIBLE has happened") (getAt j sx)

    xj1 : Double
    xj1 = fromMaybe (oops "The IMPOSSIBLE has happened") (getAt (S j) sx)


square : Double -> Double
square x = x * x

-- Columns first
Matrix : (m, n : Nat) -> Type -> Type
Matrix m n a = Vect n (Vect m a)

index : Matrix m n a -> Fin m -> Fin n -> a
index m k l = index k (index l m)

replaceAt : Matrix m n a -> Fin m -> Fin n -> a -> Matrix m n a
replaceAt m k l v = updateAt l (replaceAt k v) m

updateAt : Matrix m n a -> Fin m -> Fin n -> (a -> a) -> Matrix m n a
updateAt m k l f = updateAt l (updateAt k f) m

{-
multiplyV : Semigroup a =>  Matrix m n a -> Vect n a -> Vect m a
multiplyV = ?A
-}

-- tmultiplyV m v = transpose m `multiplyV` v
tmultiplyV : Matrix n m Double -> Vect n Double -> Vect m Double
tmultiplyV m v = (sum . zipWith (*) v) <$> m
  -- todo: less error accumulating sum


{-
-- Compute /R&#0178;/, the coefficient of determination that
-- indicates goodness-of-fit of a regression.
--
-- This value will be 1 if the predictors fit perfectly, dropping to 0
-- if they have no explanatory power.
rSquare :: Matrix m n Double               -- ^ Predictors (regressors).
        -> Vector m Double               -- ^ Responders.
        -> Vector               -- ^ Regression coefficients.
        -> Double
rSquare pred resp coeff = 1 - r / t
  where
    r   = sum $ flip U.imap resp $ \i x -> square (x - p i)
    t   = sum $ flip U.map resp $ \x -> square (x - mean resp)
    p i = sum . flip U.imap coeff $ \j -> (* unsafeIndex pred i j)

-}

allFins : (n : Nat) -> Vect n (Fin n)
allFins n = go n id where

  go : (k : Nat) -> (Fin k -> Fin n) -> Vect k (Fin n)
  go 0 f = []
  go (S n) f = f 0 :: go n (f . FS)

imap : (Fin n -> a -> a) -> Vect n a -> Vect n a
imap f [] = []
imap f (x :: xs) = f 0 x :: imap (f . FS) xs

imapUpTo : Fin n -> (Fin n -> a -> a) -> Vect n a -> Vect n a
imapUpTo _ f [] = []
imapUpTo 0 f (x :: xs) = f 0 x :: xs
imapUpTo (FS i) f (x :: xs) = f 0 x :: imapUpTo i (f . FS) xs

imapUpFrom : Fin n -> (Fin n -> a -> a) -> Vect n a -> Vect n a
imapUpFrom i f [] = []
imapUpFrom 0 f (x :: xs) = x :: imap (f . FS) xs
imapUpFrom (FS i) f (x :: xs) = x :: imapUpFrom i (f . FS) xs

mean : {n : Nat} -> Vect n Double -> Double
mean xs = sum xs / cast n

rSquare : {m : Nat} ->
          Matrix m n Double ->
          Vect m Double ->
          Vect n Double ->
          Double
rSquare pred resp coeff = 1 - r / t where

  p : Fin m -> Double
  p i = sum $ flip imap coeff $ \ j, x => x * index pred i j

  r, t : Double
  r = sum $ flip imap resp $ \ i, x => square (x - p i)
  t = sum $ flip map  resp $ \ x => square (x - mean resp)

-- Solve the equation (a * x = b for x)
solve :
  {m : Nat} ->
  (a : Matrix m m Double) -> -- upper triangular
  (b : Vect m Double) ->
  Vect m Double
solve a b = loop b (reverse (allFins m)) where

  loop : Vect m Double -> Vect k (Fin m) -> Vect m Double
  loop b [] = b
  loop b (i :: is)
    = let bi = index i b in
      let k  = index a i i in
      let si = bi / k in
      loop (imapUpTo i (\ j, x => x - (index a j i * si)) $ replaceAt i si b) is

norm : Vect m Double -> Double
norm = sqrt . sum . map (\ x => x * x)

innerProduct : Matrix m n Double -> Fin n -> Fin n -> Double
innerProduct m j k = sum $ zipWith (*) (index j m) (index k m)

qrDecomposition :
  {m, n : Nat} ->
  (a : Matrix m n Double) ->
  (Matrix m n Double, Matrix n n Double)
qrDecomposition a = loop a (replicate n (replicate n 0)) (allFins n) where

  loop3 : Matrix m n Double -> Double ->
          Fin n -> Fin n -> Vect k (Fin m) -> Matrix m n Double
  loop3 q p j jj [] = q
  loop3 q p j jj (i :: is)
    = let qij = index q i j in
      loop3 (updateAt q i jj (\ x => x - p * qij)) p j jj is

  loop2 : Matrix m n Double ->
          Matrix n n Double ->
          Fin n -> Vect k (Fin n) -> (Matrix m n Double, Matrix n n Double)
  loop2 q r j [] = (q, r)
  loop2 q r j (jj :: jjs)
    = let p = innerProduct q j jj in
      let r = replaceAt r j jj p in
      (loop3 q p j jj (allFins m), r)

  loop : Matrix m n Double ->
         Matrix n n Double ->
         Vect k (Fin n) -> (Matrix m n Double, Matrix n n Double)
  loop q r [] = (q, r)
  loop q r (j :: js)
    = let cn = norm (index j q) in
      let r  = replaceAt r j j cn in
      let q  = updateAt j (map (/ cn)) q in
      let (q, r) = loop2 q r j (fromList $ drop (cast j) $ toList $ allFins n) in
      loop q r js

-- Compute the ordinary least-squares solution to (a * x = b)
ols : {m, n : Nat} ->
      Matrix m n Double -> -- m >= n
      Vect m Double ->
      Vect n Double
ols a b
  = ifThenElse (m < n) (oops "Fewer rows than columns")
  $ let (q, r) = qrDecomposition a in solve r (q `tmultiplyV` b)

olsRegress : {m, n : Nat} ->
             Vect (S m) (Vect n Double) ->
             Vect n Double ->
             (Vect (S (m + 1)) Double, Double)
olsRegress preds resps
  = let mxpreds = preds ++ [replicate n 1] in
    let coeffs = ols mxpreds resps in
    (coeffs, rSquare mxpreds resps coeffs)
