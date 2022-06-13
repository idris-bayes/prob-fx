module Wasabaye.Examples.LinRegr

import Data.List
import Wasabaye.Model 

linRegr : (prf : Observables env ["y", "m", "c", "std"] Double) => List Double -> Model env es (List Double)
linRegr xs = do
  m   <- normal 0 3 "m"
  c   <- normal 0 5 "c"
  std <- uniform 1 3 "std"
  ys <- mapM (\x => do
                    y <- normal (m * x + c) std "y"
                    pure y) xs
  pure ys

LinRegrEnv = map ((, Double)) ["m", "c", "std", "y"]

env_instance : Env LinRegrEnv
env_instance = ("m" ::= []) <:> ("c" ::= []) <:> ("std" ::=  []) <:> ("y" ::=  []) <:> ENil

hdlLinRegr : Eff (Observe :: Sample :: []) (List Double)
hdlLinRegr = 
  handleCore env_instance (linRegr {env = LinRegrEnv} [])