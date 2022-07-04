module ProbFX.Examples.LinRegrWriter

import Data.Vect
import Data.List
import Data.List.Elem
import ProbFX.Model 
import ProbFX.Sampler 
import ProbFX.Inference.Sim
import ProbFX.Inference.MBayes
import ProbFX.Effects.Lift
import ProbFX.Effects.Writer
import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Control.Monad.Bayes.Weighted
import Control.Monad.Bayes.Traced.Static

-- | Parameters
record LinRegrParams where
  constructor MkLinRegrParams
  mean : Double   -- mean
  c : Double      -- intercept
  s : Double      -- standard deviation

Show LinRegrParams where
  show (MkLinRegrParams mv cv sv) = "(m : " ++ show mv ++ ", c : " ++ show cv ++ ", std : " ++ show sv ++ ")" 

-- | Model
linRegr : (prf : Observables env ["y", "m", "c", "std"] Double) => 
          (prf_writer : Elem (Writer (List LinRegrParams)) es) => List Double -> Model env es (List Double)
linRegr xs = do
  m   <- normal 0 3 "m"
  c   <- normal 0 5 "c"
  std <- uniform 1 3 "std"
  tell (the (List LinRegrParams) $ MkLinRegrParams m c std :: Nil)
  ys  <- sequence $ map (\x => do
                    y <- normal (m * x + c) std "y"
                    pure y) xs
  pure ys

-- | Environment
LinRegrEnv : List (String, Type)
LinRegrEnv = map ((, Double)) ["m", "c", "std", "y"]

envExampleSim : Env LinRegrEnv
envExampleSim = ("m" ::= [3]) <:> ("c" ::= [0]) <:> ("std" ::=  [1]) <:> ("y" ::=  []) <:> ENil

envExampleInf : List Double -> Env LinRegrEnv
envExampleInf xs = 
  let ys = map (*3) xs
  in  ("m" ::= []) <:> ("c" ::= []) <:> ("std" ::=  []) <:> ("y" ::=  ys) <:> ENil

-- | Linear regression as a probabilistic program
hdlLinRegr : Prog (Observe :: Sample :: []) ((List Double, List LinRegrParams), Env LinRegrEnv)
hdlLinRegr = do
  let linRegrInstance = linRegr {env = LinRegrEnv} 
                                {es = [Writer (List LinRegrParams), ObsRW LinRegrEnv, Dist]} 
                                []
  handleCore envExampleSim (handleWriter $ linRegrInstance)

-- | Simulating linear regression, using effect handlers
simLinRegr : (n_datapoints : Nat) -> IO (List Double)
simLinRegr n_datapoints = do
  let xs              = map cast [0 .. n_datapoints]
      linRegrInstance = linRegr {env = LinRegrEnv} 
                                {es = [Writer (List LinRegrParams), ObsRW LinRegrEnv, Dist]} 
                                xs
  ((ys, params), _) <- the (IO ((List Double, List LinRegrParams), _)) 
                           (runSampler $ simulate envExampleSim (handleWriter $ linRegrInstance))
  print ys >> pure ys

-- | Simulating linear regression, using monad bayes
simLinRegrMB : (n_datapoints : Nat) -> IO (List Double)
simLinRegrMB n_datapoints = do 
  let xs              = map cast [0 .. n_datapoints]
      linRegrInstance = linRegr {env = LinRegrEnv} 
                                {es = [Writer (List LinRegrParams), ObsRW LinRegrEnv, Dist, Lift (Weighted SamplerIO)]} 
                                xs
      linRegrMB = toMBayes envExampleSim (handleWriter $ linRegrInstance) 
  ((ys, params), _) <- the (IO ((List Double, List LinRegrParams), Env LinRegrEnv)) 
                      (sampleIO $ prior linRegrMB)
  print ys >> pure ys
  
-- | MH inference on linear regression, using monad bayes
mhLinRegrMB : (n_datapoints : Nat) -> (n_mhsteps : Nat) -> IO (List LinRegrParams)
mhLinRegrMB n_datapoints n_samples = do 
  let xs        = map cast [0 .. n_datapoints]
      linRegrInstance = linRegr {env = LinRegrEnv} 
                                {es = [Writer (List LinRegrParams), ObsRW LinRegrEnv, Dist, Lift (Traced $ Weighted SamplerIO)]} 
                                xs
      linRegrMB = toMBayes (envExampleInf xs) (handleWriter $ linRegrInstance) 
  vect_ys_params <- the (IO (Vect (S n_samples) ((List Double, List LinRegrParams), Env LinRegrEnv))) 
                        (sampleIO $ prior $ mh n_samples linRegrMB )
  let params = (join . toList . map (snd . fst))  vect_ys_params
  print params >> pure params