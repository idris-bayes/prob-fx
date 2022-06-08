module Dist.Uniform

import System.Random

randomDouble : IO Double
randomDouble = randomIO

uniform : Double -> Double -> IO Double
uniform min max = do
  y <- randomDouble
  pure (y * (max - min) + min)