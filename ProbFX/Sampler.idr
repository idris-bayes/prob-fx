module ProbFX.Sampler

import Control.Monad.Reader
import Statistics.Distribution
import System.Random

||| A Sampler that threads a provided GSL RNG seed through a computation. Warning: only works with local copy of the `distributions.so` file, copied over from the `distributions` Idris package. Need to work out how to avoid requiring a local copy.
export
record Sampler (a : Type) where
  constructor MkSampler
  runSampler' : ReaderT GslRng IO a

export
Functor Sampler where
  map f = MkSampler . map f . runSampler'

export
Applicative Sampler where
  pure = MkSampler . pure
  mf <*> mx = MkSampler $ runSampler' mf <*> runSampler' mx

export
Monad Sampler where
  (>>=) mx k = MkSampler $ do
    x <- runSampler' mx
    runSampler' (k x)

||| Constructing and running a Sampler
export
mkSampler : (GslRng -> IO a) -> Sampler a
mkSampler f = MkSampler $ MkReaderT  f

export
runSampler : Sampler a -> IO a
runSampler m = do
  let rng_seed = init_gsl_rng
  runReaderT rng_seed (runSampler' m)

-- ||| Raw sampling functions
export
uniform : Double -> Double -> Sampler Double
uniform min max = mkSampler (\seed =>  (gsl_uniform min max seed))

export
random : Sampler Double
random = uniform 0 1

export
bernoulli : Double -> Sampler Bool
bernoulli p     = mkSampler (\seed => gsl_binomial 1 p seed >>= (pure . (1 == )))

export
binomial : Nat -> Double -> Sampler Nat
binomial n p    = mkSampler (\seed =>  (cast $ gsl_binomial n p seed))

export
normal : Double -> Double -> Sampler Double
normal m s      = mkSampler (\seed =>  (gsl_normal m s seed))

export
beta : Double -> Double -> Sampler Double
beta a b        = mkSampler (\seed =>  (gsl_beta a b seed))

export
gamma : Double -> Double -> Sampler Double
gamma a b       = mkSampler (\seed =>  (gsl_gamma a b seed))

export
poisson : Double -> Sampler Nat
poisson p       = mkSampler (\seed =>  (gsl_poisson p seed))

export
dirichlet : {n : Nat} -> Vect (S n) Double -> Sampler (Vect (S n) Double)
dirichlet ps = mkSampler (\seed =>  (gsl_dirichlet ps seed))

-- ||| Inverse CDF sampling functions
namespace Inv
  uniform_inv
    :  (min, max : Double)
    -> (r : Double)
    -> Double
  uniform_inv min max r = gsl_uniform_cdf_inv min max r

  bernoulli_inv
    :  (p : Double)
    -> (r : Double)
    -> Bool
  bernoulli_inv p r = r < p

  -- binomial_inv
  --   :  (n)

private
testSeed : IO ()
testSeed = do
  let seed = init_gsl_rng
  (gsl_normal 17 0.5 seed) >>= print
  (gsl_binomial 17 0.5 seed) >>= print
  (gsl_uniform 0.5 17 seed) >>= print