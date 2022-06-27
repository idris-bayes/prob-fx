module Wasabaye.Examples.LinRegr

import Data.List
import Data.List.Elem
import Wasabaye.Model 
import Wasabaye.Inference.Sim
import Wasabaye.Inference.MBayes
import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Control.Monad.Bayes.Weighted
import Wasabaye.Effects.Lift

-- | Linear regression model

linRegr : (prf : Observables env ["y", "m", "c", "std"] Double) => List Double -> Model env es (List Double)
linRegr xs = do
  m   <- normal 0 3 "m"
  c   <- normal 0 5 "c"
  std <- uniform 1 3 "std"
  ys  <- sequence $ map (\x => do
                    y <- normal (m * x + c) std "y"
                    pure y) xs
  pure ys

-- | Linear regression environment
LinRegrEnv : List (String, Type)
LinRegrEnv = map ((, Double)) ["m", "c", "std", "y"]

envExample : Env LinRegrEnv
envExample = ("m" ::= [3]) <:> ("c" ::= [0]) <:> ("std" ::=  [1]) <:> ("y" ::=  [0, 2, 5]) <:> ENil

-- | Linear regression as a probabilistic program
hdlLinRegr : Prog (Observe :: Sample :: []) (List Double)
hdlLinRegr = 
  handleCore envExample (linRegr {env = LinRegrEnv} [])

-- | Simulating linear regression, using effect handlers
simLinRegr : IO (List Double)
simLinRegr = do
  let xs = map cast [0 .. (the Int 10)]
  ys <- simulate envExample (linRegr {env = LinRegrEnv} xs) 
  print ys >> pure ys

-- | Simulating linear regression, using monad bayes
simLinRegrMB : IO (List Double)
simLinRegrMB = do 
  let xs = map cast [0 .. (the Int 10)]
      linRegrMB = toMBayes envExample (linRegr {env = LinRegrEnv} xs) 
  ys <- sampleIO $ prior linRegrMB
  print ys >> pure ys

-- | MH inference on linear regression, using monad bayes


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
