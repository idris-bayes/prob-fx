module Dist.Normal

import Dist.Uniform
import Numeric.Constants
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

normal_pdf : (mean : Double) -> (std : Double) -> (y : Double) -> Double
normal_pdf mu std y = ((-xm) * xm / (2 * std * std)) - log (m_sqrt_2_pi * std)
  where xm : Double
        xm = y - mu

%foreign "C:gsl_ran_gaussian"
gsl_ran_gaussian : Double -> Double -> PrimIO Double 

%foreign "C:add,libsmall"
addp : Int -> Int -> Int

gauss : IO Double
gauss = primIO $ gsl_ran_gaussian 0 1