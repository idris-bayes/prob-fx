module Wasabaye.Inference.MBayes

import Data.List
import Control.Monad.Bayes.Interface
import Numeric.Log
import Wasabaye.Env
import Wasabaye.PrimDist
import Wasabaye.Model
import Wasabaye.Effects.Trace
import Wasabaye.Effects.Lift
import Wasabaye.Effects.Dist
import Wasabaye.Inference.Sim


handleObserve : MonadCond m => (Elem Observe es) => (prf : Elem (Lift m) (es - Observe)) => 
            Prog es a -> Prog (es - Observe) a
handleObserve (Val x)   = pure x
handleObserve (Op op k) = case discharge op of
    Left op'              => Op op' (handleObserve {prf} . k)
    Right (MkObserve d y _) => do let log_p = log_prob d y
                                  liftM {prf} (score (Exp log_p))
                                  handleObserve {prf} (k y)

handleSample : MonadSample m => (Elem Sample es) => (prf : Elem (Lift m) (es - Sample)) =>
             Prog es a -> Prog (es - Sample) a
handleSample (Val x)   = pure x  
handleSample (Op op k) = case discharge op of
    Left op'              => Op op' (handleSample {prf} . k) 
    Right (MkSample d _)  => do y <- liftM {prf} (sampleBayes d)
                                handleSample {prf} (k y)

public export
toMBayes : MonadInfer m => {env : _} 
        -> Env env -> Model env (Dist :: ObsReader env :: Lift m :: []) a -> m (a, Env env)
toMBayes env_instance = (map (map (fromTrace env))) . handleLift . handleSample {m} 
                                    . handleObserve {m} . traceSamples . handleCore env_instance