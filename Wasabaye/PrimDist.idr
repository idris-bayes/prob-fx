module Wasabaye.PrimDist

import Data.List
import Wasabaye.Sampler
import System.Random

||| Primitive distribution
public export
data PrimDist : a -> Type where
  Normal      : Double -> Double -> PrimDist Double
  Uniform     : Double -> Double -> PrimDist Double
  Beta        : Double -> Double -> PrimDist Double
  Gamma       : Double -> Double -> PrimDist Double
  Bernoulli   : Double -> PrimDist Bool
  UniformD    : Nat -> Nat -> PrimDist Nat  
  Discrete    : List Double -> PrimDist Nat
  Binomial    : Nat -> Double -> PrimDist Nat
  Poisson     : Double -> PrimDist Nat
  Categorical : List (Double, a) -> PrimDist a

||| Density functions
prob : PrimDist a -> a -> Double
prob (Bernoulli p) y      = if y then p else (1 - p)
prob (Normal mu std) y    = normal_pdf mu std y
prob (Uniform min max) y  = uniform_pdf min max y
prob (Binomial n p) y     = binomial_pdf n p y
prob (Beta a b) y         = beta_pdf a b y
prob (Gamma a b) y        = gamma_pdf a b y
prob (UniformD min max) _ = 1/(cast max - cast min)
prob (Discrete ps) y with (inBounds y ps)
  _ | Yes prf = index y ps
  _ | No ctr  = 0
prob (Poisson p) y        = poisson_pdf p y
prob (Categorical _) _ = ?prob_missing_case_7

public export
log_prob : PrimDist a -> a -> Double
log_prob d = log . prob d

||| Temporary sampling functions
uniform : Double -> Double -> IO Double
uniform min max = do
  let randomDouble : IO Double 
      randomDouble = randomIO
  x <- randomDouble
  pure (x * (max - min) + min)

normal : Double -> Double -> IO Double
normal mu std  = do
  u1 <- uniform 0 1 
  u2 <- uniform 0 1
  pure $ mu + (sqrt (-2 * log u1) * cos (2 * pi * u2)) * std

binomial : (n : Nat) -> (p : Double) -> IO Nat
binomial n p = (sequence $ replicate n (uniform 0 1)) >>= (pure . length . List.filter (< p))

public export
sample : PrimDist a -> Sampler a
sample (Normal mu std)    = Sampler.normal mu std
sample (Bernoulli p)      = Sampler.bernoulli p
sample (Binomial n p)     = Sampler.binomial n p
sample (Uniform min max)  = Sampler.uniform min max
sample (Beta a b)         = Sampler.beta a b
sample (Gamma a b)        = Sampler.gamma a b
sample (UniformD min max) = (cast . floor) <$> Sampler.uniform (cast min) (cast max)
sample (Discrete _)       = ?sample_missing_case_4
sample (Poisson _)        = ?sample_missing_case_5
sample (Categorical _)    = ?sample_missing_case_6

public export
sampleBayes : MonadSample m => PrimDist b -> m b
sampleBayes (Normal mu std)     = Monad.Bayes.Interface.normal mu std
sampleBayes (Bernoulli p)       = Monad.Bayes.Interface.bernoulli p
sampleBayes (Binomial n p)      = Monad.Bayes.Interface.binomial n p
sampleBayes (Uniform min max)   = Monad.Bayes.Interface.uniform min max
