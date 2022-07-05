module ProbFX.Examples.HMM

import Data.List
import ProbFX.Model

||| A generic transition model
TransModel : List (String, Type) -> List (Type -> Type) -> Type -> Type -> Type
TransModel env es params lat   = params -> lat -> Model env es lat
||| A generic observation model
ObsModel   : List (String, Type) -> List (Type -> Type) -> Type -> Type -> Type -> Type
ObsModel env es params lat obsv = params -> lat -> Model env es obsv

||| A generic chain of HMM nodes
hmmChain : 
     (transPrior : Model env es ps1)
  -> (obsPrior   : Model env es ps2)
  -> (transModel : TransModel env es ps1 lat) 
  -> (obsModel   : ObsModel env es ps2 lat obsv)
  -> (hmm_length : Nat) 
  -> (input_lat  : lat) 
  -> Model env es lat
hmmChain transPrior obsPrior transModel obsModel n x_0 = do
  ps1    <- transPrior
  ps2    <- obsPrior
  let hmmNode : lat -> Model env es lat
      hmmNode x = do
            x' <- transModel ps1 x
            y' <- obsModel ps2 x'
            pure x'
  foldl (>=>) pure (replicate n hmmNode) x_0

||| Example hidden Markov model
boolToNat : Bool -> Nat
boolToNat True  = 1
boolToNat False = 0

transPrior : Observable env "trans_p" Double => Model env es Double
transPrior = uniform 0 1 "trans_p" 

obsPrior : Observable env "obs_p" Double => Model env es Double
obsPrior = uniform 0 1 "obs_p" 

transModel :  Double -> Nat -> Model env es Nat
transModel transition_p x_prev = do
  dX <- boolToNat <$> bernoulli' transition_p
  pure (dX + x_prev)
  
obsModel : (Observable env "y" Nat)
  => Double -> Nat -> Model env es Nat
obsModel observation_p x = do
  binomial x observation_p "y"

hmmModel : (Observables env ["trans_p", "obs_p"] Double, Observable env "y" Nat) 
  => (len : Nat) -> (input : Nat) -> Model env es Nat 
hmmModel = hmmChain transPrior obsPrior transModel obsModel