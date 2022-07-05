module ProbFX.Examples.HMM

import Data.List
import ProbFX.Model

||| A generic transition model
TransModel : List (String, Type) -> List (Type -> Type) -> Type -> Type -> Type
TransModel env es params lat   = params -> lat -> Model env es lat
||| A generic observation model
ObsModel   : List (String, Type) -> List (Type -> Type) -> Type -> Type -> Type -> Type
ObsModel env es params lat obs = params -> lat -> Model env es obs

||| A generic chain of HMM nodes
hmmChain : 
     (transPrior : Model env es ps1)
  -> (obsPrior   : Model env es ps2)
  -> (transModel : TransModel env es ps1 lat) 
  -> (obsModel   : ObsModel env es ps2 lat obs)
  -> (hmm_length : Nat) 
  -> (initial_input : lat) 
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

-- ||| Example transition and observation models
