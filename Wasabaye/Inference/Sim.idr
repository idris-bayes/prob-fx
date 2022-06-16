module Wasabaye.Inference.Sim


import Control.Eff
import Wasabaye.Effects.Dist
import Wasabaye.Env
import Wasabaye.Model

||| Handlers for simulation
handleObserve : (Has Observe es) => Eff es a -> Eff (es - Observe) a
handleObserve prog = case toView prog of
  Pure x    => pure x
  Bind op k => case decomp op of
    Left op'              => fromView $ Bind op' (handleObserve . k)
    Right (MkObserve d y) => handleObserve (k y)

handleSample : Eff [Sample] a -> IO a
handleSample prog = case toView prog of
  Pure x    => pure x
  Bind op k => case prj1 op of
    (MkSample d) => sample d >>= (handleSample . k)

public export
simulate : Env env -> Model env [Dist, ObsReader env] a -> IO a
simulate env = handleSample . handleObserve . handleCore env 
