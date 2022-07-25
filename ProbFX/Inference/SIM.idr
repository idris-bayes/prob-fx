module ProbFX.Inference.SIM

import ProbFX.Effects.Dist
import ProbFX.Effects.Trace
import ProbFX.Env
import ProbFX.Model
import ProbFX.Sampler
import Control.Arrow

||| Handlers for simulation
export
handleObserve : (Elem Observe es) => Prog es a -> Prog (es - Observe) a
handleObserve (Val x)    = pure x
handleObserve (Op op k) = case discharge op of
  Left op'              => Op op' (handleObserve . k)
  Right (MkObserve d y _) => handleObserve (k y)

export
handleSample : Prog [Sample] a -> Sampler a
handleSample (Val x)   = pure x
handleSample (Op op k) = case prj1 op of
  (MkSample d _) => sample d !random >>= (handleSample . k)

||| Simulate from a model
public export
simulate : Env env -> Model env [] a -> Sampler (a, Env env)
simulate env_instance = handleSample . handleObserve . handleCore env_instance
