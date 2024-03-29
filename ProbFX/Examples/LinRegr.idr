module ProbFX.Examples.LinRegr

import Data.Vect
import Data.List
import Data.List.Elem
import ProbFX.Env
import ProbFX.Sampler
import ProbFX.Inference.SIM
import ProbFX.Inference.LW
import ProbFX.Inference.MH
import ProbFX.Inference.MBAYES
import ProbFX.Effects.Lift
import ProbFX.Model as PFX
import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Control.Monad.Bayes.Weighted
import Control.Monad.Bayes.Traced.Static
import Control.Monad.Bayes.Inference.SMC
import Control.Monad.Bayes.Inference.RMSMC

||| Linear regression model
linRegr : (prf : Observables env ["y", "m", "c", "std"] Double) => List Double -> Model env es (List Double)
linRegr xs = do
  m   <- PFX.normal 0 3 "m"
  c   <- PFX.normal 0 5 "c"
  std <- PFX.uniform 1 3 "std"
  ys  <- sequence $ map (\x => do
                    y <- PFX.normal (m * x + c) std "y"
                    pure y) xs
  pure ys

||| Linear regression environment
LinRegrEnv : List (String, Type)
LinRegrEnv = map ((, Double)) ["m", "c", "std", "y"]

||| An environment that sets the gradient m = 3, intercept c = 0, and noise std = 1
envExampleSim : Env LinRegrEnv
envExampleSim = ("m" ::= [3]) <:> ("c" ::= [0]) <:> ("std" ::=  [1]) <:> ("y" ::=  []) <:> ENil

||| An environment for inference whose data represents the gradient m = 3 and intercept c = 0
envExampleInf : List Double -> Env LinRegrEnv
envExampleInf xs =
  let ys = map (*3) xs
  in  ("m" ::= []) <:> ("c" ::= []) <:> ("std" ::=  []) <:> ("y" ::=  ys) <:> ENil

||| Linear regression as a probabilistic program
hdlLinRegr : Prog (Observe :: Sample :: []) (List Double, Env LinRegrEnv)
hdlLinRegr =
  handleCore envExampleSim (linRegr [])

||| Simulating linear regression, using effect handlers
export
simLinRegr : (n_datapoints : Nat) -> IO (List (Double, Double))
simLinRegr n_datapoints = do
  let xs = map cast [0 .. n_datapoints]
  (ys, env_out) <- simulate (linRegr xs) envExampleSim
  pure (zip xs ys)

||| LW inference on linear regression, using effect handlers
export
lwLinRegr : (n_lwiterations : Nat) -> (n_datapoints : Nat) -> IO (List (Double, Double))
lwLinRegr n_lwiterations n_datapoints = do
  let xs = map cast [0 .. n_datapoints]
  (envs_out, ws) <- unzip <$> (lw n_lwiterations (linRegr xs) (envExampleInf xs))
  let mus : List Double = gets "m" envs_out
  pure (zip mus ws)

||| MH inference on linear regression, using effect handlers
export
mhLinRegr : (n_mhsteps : Nat) -> (n_datapoints : Nat) -> IO (List Double, List Double)
mhLinRegr n_mhsteps n_datapoints = do
  let xs = map cast [0 .. n_datapoints]
  envs_out <- mh n_mhsteps (linRegr xs) (envExampleInf xs)
  let mus : List Double = gets "m" envs_out
      cs  : List Double = gets "c" envs_out
  pure (mus, cs)

||| Simulating linear regression, using monad bayes
export
simLinRegrMB : (n_datapoints : Nat) -> IO (List (Double, Double))
simLinRegrMB n_datapoints = do
  let xs        = map cast [0 .. n_datapoints]
      linRegrMB = toMBayes envExampleSim (linRegr xs)
  (ys, env_out) <- sampleIO $ prior linRegrMB
  pure (zip xs ys)

||| MH inference on linear regression, using monad bayes
export
mhLinRegrMB : (n_mhsteps : Nat) -> (n_datapoints : Nat) -> IO (List Double, List Double)
mhLinRegrMB n_mhsteps n_datapoints  = do
  let xs        = map cast [0 .. n_datapoints]
      linRegrMB = toMBayes (envExampleInf xs) (linRegr xs)

  output <- the (IO (Vect (S n_mhsteps) (List Double, Env LinRegrEnv)))
                   (sampleIO $ prior $ mh n_mhsteps linRegrMB )
  let env_outs : List (Env LinRegrEnv) = map snd (toList output)
      mus : List Double                   = gets "m" env_outs
      cs  : List Double                   = gets "c" env_outs
  pure (mus, cs)

||| SMC inference on linear regression, using monad bayes
export
smcLinRegrMB : (n_timesteps : Nat) -> (n_particles : Nat) -> (n_datapoints : Nat) -> IO (List Double, List Double)
smcLinRegrMB n_timesteps n_particles n_datapoints = do
  let xs        = map cast [0 .. n_datapoints]
      linRegrMB = toMBayes (envExampleInf xs) (linRegr xs)

  output <- the (IO (List (Log Double, (List Double, Env LinRegrEnv))))
                   (sampleIO $ runPopulation $ smc n_timesteps n_particles linRegrMB )
  let env_outs : List (Env LinRegrEnv) = map (snd . snd) (toList output)
      mus : List Double                   = gets "m" env_outs
      cs  : List Double                   = gets "c" env_outs
  pure (mus, cs)


||| SMC inference on linear regression, using monad bayes
export
rmsmcLinRegrMB : (n_timesteps : Nat) -> (n_particles : Nat) -> (n_mhsteps : Nat) -> (n_datapoints : Nat) -> IO (List Double, List Double)
rmsmcLinRegrMB  n_timesteps n_particles n_mhsteps n_datapoints = do
  let xs        = map cast [0 .. n_datapoints]
      linRegrMB = toMBayes (envExampleInf xs) (linRegr xs)

  output <- the (IO (List (Log Double, (List Double, Env LinRegrEnv))))
                   (sampleIO $ runPopulation $ rmsmc n_timesteps n_particles n_mhsteps linRegrMB )
  let env_outs : List (Env LinRegrEnv) = map (snd . snd) (toList output)
      mus : List Double                   = gets "m" env_outs
      cs  : List Double                   = gets "c" env_outs
  pure (mus, cs)


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