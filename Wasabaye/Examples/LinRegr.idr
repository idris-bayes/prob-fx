module Wasabaye.Examples.LinRegr

import Data.List
import Data.List.Elem
import Wasabaye.Model 
import Wasabaye.Inference.Sim

linRegr : (prf : Observables env ["y", "m", "c", "std"] Double) => List Double -> Model env es (List Double)
linRegr xs = do
  m   <- normal 0 3 "m"
  c   <- normal 0 5 "c"
  std <- uniform 1 3 "std"
  ys  <- sequence $ map (\x => do
                    y <- normal (m * x + c) std "y"
                    pure y) xs
  pure ys

LinRegrEnv = map ((, Double)) ["m", "c", "std", "y"]

envExample : Env LinRegrEnv
envExample = ("m" ::= [3]) <:> ("c" ::= [0]) <:> ("std" ::=  [1]) <:> ("y" ::=  [0, 2, 5]) <:> ENil

hdlLinRegr : Eff (Observe :: Sample :: []) (List Double)
hdlLinRegr = 
  handleCore envExample (linRegr {env = LinRegrEnv} [])

simLinRegr : IO ()
simLinRegr = do
  let xs = map cast [0 .. 10]
  ys <- simulate envExample (linRegr {env = LinRegrEnv} xs) 
  print ys

{- We can omit specifying the 'env' type via {env = LinRegrEnv} if we make clear that the provided environment should unify with the `env` at a specific position in the effect signature:

    linRegr : (prf : Observables env ["y", "m", "c", "std"] Double) => List Double -> Model env (Dist :: ObsReader env :: es) (List Double)
    linRegr xs = do
      m   <- normal 0 3 "m"
      c   <- normal 0 5 "c"
      std <- uniform 1 3 "std"
      ys <- mapM (\x => do
                        y <- normal (m * x + c) std "y"
                        pure y) xs
      pure ys

    handleCore : Env env -> Model env (Dist :: ObsReader env ::  es) a -> Eff (Observe :: Sample :: es) a
    handleCore env' = handleDist . handleObsRead env' . runModel

    LinRegrEnv = map ((, Double)) ["m", "c", "std", "y"]

    env_instance : Env LinRegrEnv
    env_instance = ("m" ::= []) <:> ("c" ::= []) <:> ("std" ::=  []) <:> ("y" ::=  []) <:> ENil

    hdlLinRegr : Eff (Observe :: Sample :: []) (List Double)
    hdlLinRegr =   handleCore env_instance (linRegr [])

Without this, the env_instance provided could be referring to a different ObsReader env effect.

-}
