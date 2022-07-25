module ProbFX.PrimDist

import Data.List
import Decidable.Equality
import Statistics.Distribution
import Control.Monad.Bayes.Interface
import ProbFX.Sampler

||| Primitive distribution
public export
data PrimDist : a -> Type where
  Normal      : Double -> Double -> PrimDist Double
  Uniform     : Double -> Double -> PrimDist Double
  Beta        : Double -> Double -> PrimDist Double
  Gamma       : Double -> Double -> PrimDist Double
  Bernoulli   : Double -> PrimDist Bool
  Binomial    : Nat -> Double -> PrimDist Nat
  Poisson     : Double -> PrimDist Nat
  Categorical : {n : Nat} -> Vect (S n) Double -> PrimDist (Fin (S n))
  Discrete    : {n : Nat} -> Vect (S n) (a, Double) -> (eq : Eq a) => PrimDist a
  Dirichlet   : {n : Nat} -> Vect (S n) Double -> PrimDist (Vect (S n) Double)

public export
primDistEq : PrimDist a -> PrimDist b -> Bool
primDistEq (Normal m s) (Normal m' s')        = m == m' && s == s'
primDistEq (Bernoulli p) (Bernoulli p')       = p == p'
primDistEq (Binomial n p) (Binomial n' p')    = n == n' && p == p'
primDistEq (Categorical ps) (Categorical ps') = toList ps == toList ps'
primDistEq (Beta a b) (Beta a' b')            = a == a' && b == b'
primDistEq (Gamma a b) (Gamma a' b')          = a == a' && b == b'
primDistEq (Uniform a b) (Uniform a' b')      = a == a' && b == b'
primDistEq (Poisson l) (Poisson l')           = l == l'
primDistEq (Discrete xs ) (Discrete xs')      = xs == believe_me xs'
primDistEq (Dirichlet xs) (Dirichlet xs')     = toList xs == toList xs'
primDistEq _ _ = False

||| Erased primitive distribution
public export
data Erased : (f : Type -> Type) -> Type where
  Erase : f a -> Erased f

-- hetEq : PrimDist a -> PrimDist b ->

||| Density functions
export
prob : PrimDist a -> a -> Double
prob (Uniform min max) y  = gsl_uniform_pdf min max y
prob (Bernoulli p) y      = if y then p else (1 - p)
prob (Binomial n p) y     = gsl_binomial_pdf n p y
prob (Normal mu std) y    = gsl_normal_pdf mu std y
prob (Beta a b) y         = gsl_beta_pdf a b y
prob (Gamma a b) y        = gsl_gamma_pdf a b y
prob (Poisson p) y        = gsl_poisson_pdf p y
prob (Categorical ps) y   = index y ps
prob (Discrete yps) y     = case (find ((== y) . fst) yps)
                            of  Just (_, p) => p
                                Nothing     => 0.0
prob (Dirichlet ps) ys    = gsl_dirichlet_pdf ps ys

export
logProb : PrimDist a -> a -> Double
logProb d = log . prob d

||| Sampling functions
export
sample : PrimDist a -> (r : Double) -> Sampler a
sample (Uniform min max) r   = Sampler.uniform_inv min max r
sample (Bernoulli p) r       = Sampler.bernoulli_inv p r
sample (Binomial n p) r      = Sampler.binomial_inv n p r
sample (Normal mu std) r     = Sampler.normal_inv mu std r
sample (Beta a b) r          = Sampler.beta_inv a b r
sample (Gamma a b) r         = Sampler.gamma_inv a b r
sample (Poisson p) r         = Sampler.poisson_inv p r
sample (Categorical {n} ps) r = do
  let normalised_ps = map (/(sum ps)) ps

      cmf : Double -> Nat -> List Double -> Maybe (Fin (S n))
      cmf acc idx (x :: xs) = let acc' = acc + x
                              in  if acc' > r then natToFin idx (S n) else cmf acc' (S idx) xs
      cmf acc idx []        = Nothing

  case cmf 0 0 (toList normalised_ps) of
    Just i  => pure i
    Nothing => assert_total $ idris_crash $ "categorical: bad weights!" ++ show ps
sample (Discrete pxs) r = do
  let (xs, ps) = unzip pxs
  sample (Categorical ps) r >>= pure . flip index xs
sample (Dirichlet ps) r = Sampler.dirichlet_inv ps r

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
  let (xs, ps) = unzip pxs
  Monad.Bayes.Interface.categorical ps >>=  pure . flip index xs
sampleBayes (Dirichlet ps)    = Monad.Bayes.Interface.dirichlet ps