||| Likelihood-Weighting (LW) inference
module ProbFX.Inference.LW

import ProbFX.Effects.Dist
import ProbFX.Effects.ObsRW
import ProbFX.Effects.Lift
import ProbFX.Inference.SIM
import ProbFX.Env
import ProbFX.PrimDist
import ProbFX.Model
import ProbFX.Sampler
import Data.List

||| Handle Observe by computing and accumulating a log-probability
handleObserve : (Elem Observe es) => Double -> Prog es a -> Prog (es - Observe) (a, Double)
handleObserve logp (Val x)   = pure (x, logp)
handleObserve logp (Op op k) = case discharge op of
  Left op'                => Op op' (handleObserve logp . k)
  Right (MkObserve d y _) => handleObserve (logp + logProb d y) (k y)

||| Handle one iteration of LW
export
handleLW : Prog [Observe, Sample] a -> Sampler (a, Double)
handleLW = SIM.handleSample . handleObserve 0

||| Handle many iterations of LW
export
lwInternal : (lw_iterations : Nat) -> Prog [Observe, Sample] a -> Sampler (List (a, Double))
lwInternal n = sequence . replicate n . handleLW

||| Top-level wrapper for LW inference on a model
export
lw : (lw_iterations : Nat) -> Model env [] a -> Env env -> Sampler (List (Env env, Double))
lw n model env_in = do
  lw_trace <- (lwInternal n . handleCore env_in) model
  pure (map (\(out, w) => (snd out, w)) lw_trace)