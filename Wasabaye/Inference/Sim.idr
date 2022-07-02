module Wasabaye.Inference.Sim

import Wasabaye.Effects.Dist
import Wasabaye.Effects.Trace
import Wasabaye.Env
import Wasabaye.Model
import Wasabaye.Sampler
import Control.Arrow

||| Handlers for simulation
handleObserve : (Elem Observe es) => Prog es a -> Prog (es - Observe) a
handleObserve (Val x)    = pure x
handleObserve (Op op k) = case discharge op of
  Left op'              => Op op' (handleObserve . k)
  Right (MkObserve d y _) => handleObserve (k y)

handleSample : Prog [Sample] a -> Sampler a
handleSample (Val x)   = pure x
handleSample (Op op k) = case prj1 op of
  (MkSample d _) => sample d >>= (handleSample . k)

||| Top-level simulation
public export
simulate : {env : _} -> Env env -> Model env [Dist, ObsRW env] a -> Sampler (a, Env env)
simulate env_instance = handleSample . handleObserve . handleCore env_instance
