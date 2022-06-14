module Wasabaye.Inference.Sim

import System.Random
import Data.List
import Control.Eff
import Wasabaye.Effects.Dist
import Wasabaye.Env
import Wasabaye.Model

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
binomial n p = replicateM n (uniform 0 1) >>= (pure . length . filter (< p))

sample : PrimDist a -> IO a
sample (Normal mu std)   = normal mu std
sample (Bernoulli p)     = binomial 1 p >>= pure . (== 1)
sample (Binomial n p)    = binomial n p
sample (Uniform min max) = uniform min max

||| Handlers for simulation
handleObserve : (Has Observe es) => Eff es a -> Eff (es - Observe) a
handleObserve prog = case toView prog of
  Pure x    => pure x
  Bind op k => case decomp op of
    Left op'              => fromView $ Bind op' (handleObserve . k)
    Right (MkObserve d y) => handleObserve (k y)

handleSample : Eff [Sample] a -> IO a
handleSample prog = case toView prog of
  Pure x    => pure x
  Bind op k => case prj1 op of
    (MkSample d) => sample d >>= (handleSample . k)

simulate : Env env -> Model env [Dist, ObsReader env] a -> IO a
simulate env = handleSample . handleObserve . handleCore env 
