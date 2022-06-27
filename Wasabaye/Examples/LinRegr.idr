module Wasabaye.Examples.LinRegr

import Data.Vect
import Data.List
import Data.List.Elem
import Wasabaye.Model 
import Wasabaye.Inference.Sim
import Wasabaye.Inference.MBayes
import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Control.Monad.Bayes.Weighted
import Control.Monad.Bayes.Traced.Static
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

envExampleSim : Env LinRegrEnv
envExampleSim = ("m" ::= [3]) <:> ("c" ::= [0]) <:> ("std" ::=  [1]) <:> ("y" ::=  []) <:> ENil

envExampleInf : List Double -> Env LinRegrEnv
envExampleInf xs = 
  let ys = map (*3) xs
  in  ("m" ::= []) <:> ("c" ::= []) <:> ("std" ::=  []) <:> ("y" ::=  ys) <:> ENil

-- | Linear regression as a probabilistic program
hdlLinRegr : Prog (Observe :: Sample :: []) (List Double)
hdlLinRegr = 
  handleCore envExampleSim (linRegr {env = LinRegrEnv} [])

-- | Simulating linear regression, using effect handlers
simLinRegr : (n_datapoints : Nat) -> IO (List Double)
simLinRegr n_datapoints = do
  let xs = map cast [0 .. n_datapoints]
  ys <- simulate envExampleSim (linRegr {env = LinRegrEnv} xs) 
  print ys >> pure ys

-- | Simulating linear regression, using monad bayes
simLinRegrMB : (n_datapoints : Nat) -> IO (List Double)
simLinRegrMB n_datapoints = do 
  let xs        = map cast [0 .. n_datapoints]
      linRegrMB = toMBayes envExampleSim (linRegr {env = LinRegrEnv} xs) 
  ys <- sampleIO $ prior linRegrMB
  print ys >> pure ys

-- | MH inference on linear regression, using monad bayes
mhLinRegrMB : (n_datapoints : Nat) -> (n_samples : Nat) -> IO (Vect (S n_samples) (List Double))
mhLinRegrMB n_datapoints n_samples = do 
  let xs        = map cast [0 .. n_datapoints]
      ys        = envExampleInf xs
      linRegrMB = toMBayes ys (linRegr {env = LinRegrEnv} xs) 
  ys <- the (IO (Vect (S n_samples) (List Double))) (sampleIO $ prior $ mh n_samples linRegrMB )
  print ys >> pure ys

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
