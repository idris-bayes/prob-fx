module Wasabaye.Inference.Sim

import System.Random
import Control.Eff
import Wasabaye.Effects.Dist

handleObserve : (Has Observe es) => Eff es a -> Eff (es - Observe) a
handleObserve prog = case toView prog of
  Pure x    => pure x
  Bind op k => case decomp op of
    Left op'              => fromView $ Bind op' (handleObserve . k)
    Right (MkObserve d y) => handleObserve (k y)


-- handleSample : Eff [Sample] a -> 


-- Temporary sampling functions

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
