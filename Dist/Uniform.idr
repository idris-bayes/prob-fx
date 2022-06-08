module Dist.Uniform

import System.Random
import System.FFI

randomDouble : IO Double
randomDouble = randomIO

public export
uniform : Double -> Double -> IO Double
uniform min max = do
  x <- randomDouble
  pure (x * (max - min) + min)

public export
uniform_pdf : Double -> Double -> Double -> Double
uniform_pdf min max y with (y < max && y > min)
 _ | True = 1/(max - min)
 _ | _    = 0
