module Wasabaye.Inference.Sim

import Wasabaye.Effects.Dist
import Wasabaye.Env
import Wasabaye.Model

||| Handlers for simulation
handleObserve : (Elem Observe es) => Prog es a -> Prog (es - Observe) a
handleObserve (Val x)    = pure x
handleObserve (Op op k) = case discharge op of
  Left op'              => Op op' (handleObserve . k)
  Right (MkObserve d y) => handleObserve (k y)

handleSample : Prog [Sample] a -> IO a
handleSample (Val x)   = pure x
handleSample (Op op k) = case prj1 op of
  (MkSample d) => sample d >>= (handleSample . k)

public export
simulate : Env env -> Model env [Dist, ObsReader env] a -> IO a
simulate env = handleSample . handleObserve . handleCore env 
