module ProbFX.Sampler

import Data.List
import Control.Monad.Reader
import Statistics.Distribution
import System.Random
import ProbFX.Util

public export
Sampler : Type -> Type
Sampler = IO

export
random : Sampler Double
random = System.Random.randomIO

-- ||| Inverse CDF sampling functions
export
uniform_inv
  :  (min, max : Double)
  -> (r : Double)
  -> Sampler Double
uniform_inv min max r = pure $ gsl_uniform_cdf_inv min max r

export
bernoulli_inv
  :  (p : Double)
  -> (r : Double)
  -> Sampler Bool
bernoulli_inv p r = pure (r < p)

export
binomial_inv
  :  (n : Nat)
  -> (p : Double)
  -> (r : Double)
  -> Sampler Nat
binomial_inv n p r = do
  srand (toSeed r)
  rs <- sequence (List.replicate n random)
  (pure . length . List.filter (== True)) !(sequence $ map (bernoulli_inv p) rs)

export
normal_inv
  :  (mu, std : Double)
  -> (r : Double)
  -> Sampler Double
normal_inv mu std r = pure $ gsl_normal_cdf_inv mu std r

export
gamma_inv
  :   (a, b : Double)
  ->  (r : Double)
  ->  Sampler Double
gamma_inv a b r = pure $ gsl_gamma_cdf_inv a b r

export
beta_inv
  :   (a, b : Double)
  ->  (r : Double)
  ->  Sampler Double
beta_inv a b r = pure $ gsl_beta_cdf_inv a b r

export
dirichlet_inv : {n : Nat} -> Vect n Double -> (r : Double) -> Sampler (Vect n Double)
dirichlet_inv as r = do
  srand (toSeed r)
  rs <- sequence $ Vect.replicate n random
  xs <- sequence $ map (\(a, r) => gamma_inv a 1 r) (zip as rs)
  let s  = sum xs
      ys = map (/ s) xs
  pure ys

fromPMF
  :   (pmf : Nat -> Double)
  ->  (r : Double)
  ->  Sampler Nat
fromPMF pmf r = f 0 1
  where
    f : Nat -> Double -> Sampler Nat
    f n marginal with (marginal < 0)
     _ | False = do
              let prob = pmf n
              b <- bernoulli_inv (prob / marginal) r
              if b then pure n else assert_total f (n + 1) (marginal - prob)
     _ | True = assert_total $ idris_crash "fromPMF: total PMF above 1"

export
poisson_inv
  :  (p : Double)
  -> (r : Double)
  -> Sampler Nat
poisson_inv p r = fromPMF (gsl_poisson_pdf p) r