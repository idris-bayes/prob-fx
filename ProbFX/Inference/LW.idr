module ProbFX.Inference.LW

import ProbFX.Effects.Dist
import ProbFX.Effects.Trace
import ProbFX.Effects.ObsRW
import ProbFX.Effects.Lift
import ProbFX.Inference.SIM
import ProbFX.Env
import ProbFX.PrimDist
import ProbFX.Model
import ProbFX.Sampler
import Data.List

||| Handlers for Likelihood weighting
handleObserve : (Elem Observe es) => Double -> Prog es a -> Prog (es - Observe) (a, Double)
handleObserve logp (Val x)   = pure (x, logp)
handleObserve logp (Op op k) = case discharge op of
  Left op'                => Op op' (handleObserve logp . k)
  Right (MkObserve d y _) => handleObserve (logp + logProb d y) (k y)

export
handleLW : Prog [Observe, Sample] a -> Sampler (a, Double)
handleLW = SIM.handleSample . handleObserve 0

||| Likelihood weighting on a probabilistic program
export
lwInternal : (lw_iterations : Nat) -> Prog [Observe, Sample] a -> Sampler (List (a, Double))
lwInternal n = sequence . replicate n . handleLW

||| Likelihood weighting on a model
export
lw : (lw_iterations : Nat) -> Env env -> Model env [] a -> Sampler (List (Env env, Double))
lw n env_in = (map (\(out, w) => (snd out, w)) <$>) . lwInternal n . handleCore env_in
