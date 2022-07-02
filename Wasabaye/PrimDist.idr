module Wasabaye.PrimDist

import Data.List
import Statistics.Distribution.Binomial 
import Statistics.Distribution.Beta 
import Statistics.Distribution.Gamma 
import Statistics.Distribution.Normal 
import Statistics.Distribution.Uniform 
import Statistics.Distribution.Poisson 
import Control.Monad.Bayes.Interface
import Wasabaye.Sampler

||| Primitive distribution
public export
data PrimDist : a -> Type where
  Normal      : Double -> Double -> PrimDist Double
  Uniform     : Double -> Double -> PrimDist Double
  Beta        : Double -> Double -> PrimDist Double
  Gamma       : Double -> Double -> PrimDist Double
  Bernoulli   : Double -> PrimDist Bool
  Categorical : {n : Nat} -> Vect n Double -> PrimDist (Fin n)
  Binomial    : Nat -> Double -> PrimDist Nat
  Poisson     : Double -> PrimDist Nat
  Discrete    : Eq a => {n : Nat} -> Vect n (Double, a) -> PrimDist a

||| Density functions
export
prob : PrimDist a -> a -> Double
prob (Uniform min max) y  = uniform_pdf min max y
prob (Bernoulli p) y      = if y then p else (1 - p)
prob (Binomial n p) y     = binomial_pdf n p y
prob (Normal mu std) y    = normal_pdf mu std y
prob (Beta a b) y         = beta_pdf a b y
prob (Gamma a b) y        = gamma_pdf a b y
prob (Poisson p) y        = poisson_pdf p y
prob (Categorical ps) y   = index y ps
prob (Discrete yps) y     = case (find ((== y) . snd) yps)
                            of  Just (p, _) => p
                                Nothing     => 0.0

export
log_prob : PrimDist a -> a -> Double
log_prob d = log . prob d

||| Sampling functions
export
sample : PrimDist a -> Sampler a
sample (Uniform min max)    = Sampler.uniform min max
sample (Bernoulli p)        = Sampler.bernoulli p
sample (Binomial n p)       = Sampler.binomial n p
sample (Normal mu std)      = Sampler.normal mu std
sample (Beta a b)           = Sampler.beta a b
sample (Gamma a b)          = Sampler.gamma a b
sample (Poisson p)          = Sampler.poisson p
sample (Categorical {n} ps) = do
  r <- Sampler.uniform 0 1
  let normalised_ps = map (/(sum ps)) ps 

      cmf : Double -> Nat -> List Double -> Maybe (Fin n)
      cmf acc idx (x :: xs) = let acc' = acc + x 
                              in  if acc' > r then natToFin idx n else cmf acc' (S idx) xs
      cmf acc idx []        = Nothing

  case cmf 0 0 (toList normalised_ps) of
    Just i  => pure i
    Nothing => assert_total $ idris_crash $ "categorical: bad weights!" ++ show ps
sample (Discrete pxs) = do 
  let (ps, xs) = unzip pxs
  sample (Categorical ps) >>= pure . flip index xs

export
sampleBayes : MonadSample m => PrimDist b -> m b
sampleBayes (Normal mu std)   = Monad.Bayes.Interface.normal mu std
sampleBayes (Bernoulli p)     = Monad.Bayes.Interface.bernoulli p
sampleBayes (Binomial n p)    = Monad.Bayes.Interface.binomial n p
sampleBayes (Uniform min max) = Monad.Bayes.Interface.uniform min max
sampleBayes (Beta a b)        = Monad.Bayes.Interface.beta a b
sampleBayes (Gamma a b)       = Monad.Bayes.Interface.gamma a b
sampleBayes (Poisson p)       = Monad.Bayes.Interface.poisson p
sampleBayes (Categorical ps)  = Monad.Bayes.Interface.categorical ps
sampleBayes (Discrete pxs)    = do
  let (ps, xs) = unzip pxs
  Monad.Bayes.Interface.categorical ps >>=  pure . flip index xs
