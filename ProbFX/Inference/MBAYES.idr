module ProbFX.Inference.MBAYES

import Data.List
import Control.Monad.Bayes.Interface
import Numeric.Log
import ProbFX.Env
import ProbFX.PrimDist
import ProbFX.Model
import ProbFX.Effects.Trace
import ProbFX.Effects.Lift
import ProbFX.Effects.Dist
import ProbFX.Inference.SIM

||| Handlers for monad-bayes
handleObserve : MonadCond m => (Elem Observe es) => (prf : Elem (Lift m) (es - Observe)) =>
            Prog es a -> Prog (es - Observe) a
handleObserve (Val x)   = pure x
handleObserve (Op op k) = case discharge op of
    Left op'              => Op op' (handleObserve {prf} . k)
    Right (MkObserve d y _) => do let log_p = logProb d y
                                  liftM {prf} (score (Exp log_p))
                                  handleObserve {prf} (k y)

handleSample : MonadSample m => (Elem Sample es) => (prf : Elem (Lift m) (es - Sample)) =>
             Prog es a -> Prog (es - Sample) a
handleSample (Val x)   = pure x
handleSample (Op op k) = case discharge op of
    Left op'              => Op op' (handleSample {prf} . k)
    Right (MkSample d _)  => do y <- liftM {prf} (sampleBayes d)
                                handleSample {prf} (k y)

||| Translate a model into a monad-bayes program
public export
toMBayes : MonadInfer m => Env env -> Model env [Lift m] a -> m (a, Env env)
toMBayes env_instance = handleLift . handleSample {m} . handleObserve {m} . handleCore env_instance