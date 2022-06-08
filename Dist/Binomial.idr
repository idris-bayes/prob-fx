module Dist.Binomial

import Data.List
import Dist.Uniform

binomial : (n : Nat) -> (p : Double) -> IO Nat
binomial n p = replicateM n (uniform 0 1) >>= (pure . length . filter (< p))

