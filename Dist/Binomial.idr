module Dist.Binomial

import Data.List
import Dist.Uniform

binomial : (n : Nat) -> (p : Double) -> IO Nat
binomial n p = replicateM n (uniform 0 1) >>= (pure . length . filter (< p))

%foreign "C:gsl_ran_binomial_pdf,libgsl"
binomial_pdf' : Int -> Double -> Int -> Double

binomial_pdf : Nat -> Double -> Nat -> Double
binomial_pdf n p y = binomial_pdf' (cast n) p (cast y) 