module Wasabaye.Inference.Sim

import Wasabaye.Effects.Dist
import Wasabaye.Trace
import Wasabaye.Env
import Wasabaye.Model
import Control.Arrow

||| Handler for recording samples 
traceSamples' : (prf : Elem Sample es) => Trace -> Prog es a -> Prog es (a, Trace)
traceSamples' strace (Val x) = pure (x, strace) 
traceSamples' strace (Op op k) with (prj op {prf})
  _ | Just (MkSample d maybe_tag) with (maybe_tag)
    _ | Just tag = do y <- send (MkSample d maybe_tag) 
                      let p = toPrimVal d y
                          strace' = insertTrace (tag, p) strace 
                      (traceSamples' strace' . k) y
    _ | Nothing  = do y <- send (MkSample d maybe_tag)
                      (traceSamples' strace . k) y
  _ | Nothing = Op op (traceSamples' strace . k)

public export
traceSamples : (prf : Elem Sample es) => Prog es a -> Prog es (a, Trace)
traceSamples = traceSamples' []

||| Handlers for simulation
handleObserve : (Elem Observe es) => Prog es a -> Prog (es - Observe) a
handleObserve (Val x)    = pure x
handleObserve (Op op k) = case discharge op of
  Left op'              => Op op' (handleObserve . k)
  Right (MkObserve d y _) => handleObserve (k y)

handleSample : Prog [Sample] a -> IO a
handleSample (Val x)   = pure x
handleSample (Op op k) = case prj1 op of
  (MkSample d _) => sample d >>= (handleSample . k)

public export
simulate : {env : _} -> Env env -> Model env [Dist, ObsReader env] a -> IO (a, Env env)
simulate env_instance = (map (map (fromTrace env))) . handleSample . handleObserve . traceSamples . handleCore env_instance
