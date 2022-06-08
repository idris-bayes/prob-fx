module Dist.Normal

import Dist.Uniform

||| Box muller transform to sample from standard normal distribution of mean 0 and std 1.
normal_std : IO Double
normal_std = do
  u1 <- uniform 0 1
  u2 <- uniform 0 1
  pure $ sqrt (-2 * log u1) * cos (2 * pi * u2)

||| Normal distribution with specified mean and std.
normal : Double -> Double -> IO Double
normal mu std = normal_std >>= \x => pure (x * std + mu)
