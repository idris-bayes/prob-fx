||| Simulation
module ProbFX.Inference.SIM

import ProbFX.Effects.Dist
import ProbFX.Env
import ProbFX.Model
import ProbFX.Sampler
import Control.Arrow

||| Handle Observe by simply passing forward the observed value, performing no side-effects
export
handleObserve : Elem Observe es => Prog es a -> Prog (es - Observe) a
handleObserve (Val x)    = pure x
handleObserve (Op op k) = case discharge op of
  Left op'              => Op op' (handleObserve . k)
  Right (MkObserve d y _) => handleObserve (k y)

||| Handle Sample by drawing a random value between 0 and 1 and applying the inverse CDF of a primitive distribution
export
handleSample : Prog [Sample] a -> Sampler a
handleSample (Val x)   = pure x
handleSample (Op op k) = case prj1 op of
  (MkSample d _) => sample d !random >>= (handleSample . k)

||| Simulate from a model under a given model environment
export
simulate : Model env [] a -> Env env -> Sampler (a, Env env)
simulate model env_in = (handleSample . handleObserve . handleCore env_in) model
