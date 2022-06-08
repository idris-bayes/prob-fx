module Dist.Normal

import Dist.Uniform
import System.FFI

||| Box muller transform to sample from standard normal distribution of mean 0 and standard deviation 1.
box_muller : IO Double
box_muller = do
  u1 <- uniform 0 1
  u2 <- uniform 0 1
  pure $ sqrt (-2 * log u1) * cos (2 * pi * u2)

||| Normal distribution with specified mean and std.
normal : (mean : Double) -> (std : Double)                --     -> {auto _ : (std > 0) === True} 
      -> IO Double
normal mu std = box_muller >>= \x => pure (x * std + mu)

%foreign "C:gsl_ran_gaussian_pdf,libgsl"
normal_pdf : Double -> Double -> Double 
