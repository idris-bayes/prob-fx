module Wasabaye.Sampler

import Control.Monad.Reader
import Statistics.Distribution.GSL
import Statistics.Distribution.Uniform
import Statistics.Distribution.Binomial
import Statistics.Distribution.Normal
import Statistics.Distribution.Beta
import Statistics.Distribution.Gamma
import Statistics.Distribution.Poisson
import Statistics.Distribution.Test
import System.Random

||| WARNING: Only works with local copy of the `distributions.so` file, copied over from the `distributions` Idris package. Need to work out how to avoid requiring a local copy. 
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

export
mkSampler : (GslRng -> IO a) -> Sampler a
mkSampler f = MkSampler $ MkReaderT  f

export
runSampler : Sampler a -> IO a
runSampler m = do
  let rng_seed = init_rng
  runReaderT rng_seed (runSampler' m)

export
uniform : Double -> Double -> Sampler Double
uniform min max = mkSampler (\seed => pure (uniform_gsl min max seed))

export
bernoulli : Double -> Sampler Bool
bernoulli p     = mkSampler (\seed => pure (1 == binomial_gsl 1 p seed))

export
binomial : Nat -> Double -> Sampler Nat
binomial n p    = mkSampler (\seed => pure (cast $ binomial_gsl n p seed))

export
normal : Double -> Double -> Sampler Double
normal m s      = mkSampler (\seed => pure (normal_gsl m s seed))

export
beta : Double -> Double -> Sampler Double
beta a b        = mkSampler (\seed => pure (beta_gsl a b seed))

export
gamma : Double -> Double -> Sampler Double
gamma a b       = mkSampler (\seed => pure (gamma_gsl a b seed))

export
poisson : Double -> Sampler Nat
poisson p       = mkSampler (\seed => pure (poisson_gsl p seed))


private
testSeed : IO () 
testSeed = print $ let seed = GSL.init_rng
                   in  (normal_gsl 17 0.5 seed, binomial_gsl 17 0.5 seed, uniform_gsl 0.5 17 seed)