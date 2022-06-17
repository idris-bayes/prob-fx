module Wasabaye.Effects.Dist

import Data.List
import Statistics.Distribution.Binomial 
import Statistics.Distribution.Normal 
import Statistics.Distribution.Uniform 
import Wasabaye.Prog
import System.Random

public export
data PrimDist : a -> Type where
  Normal    : Double -> Double -> PrimDist Double
  Bernoulli : Double -> PrimDist Bool
  Binomial  : Nat -> Double -> PrimDist Nat
  Uniform   : Double -> Double -> PrimDist Double

public export
record Dist (a : Type) where
  constructor MkDist
  dist : PrimDist a
  obs  : Maybe a

public export
data Observe : Effect where 
  MkObserve : PrimDist a -> a -> Observe a

public export
data Sample : Effect where
  MkSample  : PrimDist a -> Sample a

public export
partial
handleDist : (prf : Elem Dist es) => Prog es a -> Prog (Observe :: Sample :: es - Dist) a
handleDist (Val x) = pure x 
handleDist (Op op k) = case discharge op {prf} of
  Right d => case d.obs of Just y  => do x <- send (MkObserve d.dist y) 
                                         (handleDist . k) x
                           Nothing => send (MkSample d.dist) >>= (handleDist . k)
  Left op' => Op (weaken1 $ weaken1 op') (handleDist . k)

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
binomial n p = (sequence $ replicate n (uniform 0 1)) >>= (pure . length . filter (< p))

public export
sample : PrimDist a -> IO a
sample (Normal mu std)   = normal mu std
sample (Bernoulli p)     = binomial 1 p >>= pure . (== 1)
sample (Binomial n p)    = binomial n p
sample (Uniform min max) = uniform min max
