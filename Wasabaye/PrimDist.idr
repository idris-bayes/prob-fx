module Wasabaye.PrimDist

import Data.List
import Statistics.Distribution.Binomial 
import Statistics.Distribution.Normal 
import Statistics.Distribution.Uniform 
import Control.Monad.Bayes.Interface
import System.Random

||| Primitive distribution
public export
data PrimDist : a -> Type where
  Normal    : Double -> Double -> PrimDist Double
  Bernoulli : Double -> PrimDist Bool
  Binomial  : Nat -> Double -> PrimDist Nat
  Uniform   : Double -> Double -> PrimDist Double

||| Density functions
prob : PrimDist a -> a -> Double
prob (Bernoulli p) y     = if y then p else (1 - p)
prob (Normal mu std) y   = normal_pdf mu std y
prob (Uniform min max) y = uniform_pdf min max y
prob (Binomial n p) y    = binomial_pdf n p y

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
sample : PrimDist a -> IO a
sample (Normal mu std)   = PrimDist.normal mu std
sample (Bernoulli p)     = PrimDist.binomial 1 p >>= pure . (== 1)
sample (Binomial n p)    = PrimDist.binomial n p
sample (Uniform min max) = PrimDist.uniform min max

public export
sampleBayes : MonadSample m => PrimDist b -> m b
sampleBayes (Normal mu std)     = Monad.Bayes.Interface.normal mu std
sampleBayes (Bernoulli p)       = Monad.Bayes.Interface.bernoulli p
sampleBayes (Binomial n p)      = Monad.Bayes.Interface.binomial n p
sampleBayes (Uniform min max)   = Monad.Bayes.Interface.uniform min max
