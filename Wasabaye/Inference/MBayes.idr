module Wasabaye.Inference.MBayes

import Data.List
import Control.Monad.Bayes.Interface
import Wasabaye.Env
import Wasabaye.Model
import Wasabaye.Effects.Lift
import Wasabaye.Effects.Dist

handleObs : MonadCond m => (Elem Observe es) => (prf : Elem (Lift m) (es - Observe)) => 
            Prog es a -> Prog (es - Observe) a
handleObs (Val x)   = pure x
handleObs (Op op k) = case discharge op of
    Left op'              => Op op' (handleObs {prf} . k)
    Right (MkObserve d y) => do let log_p = log_prob d y
                                liftM {prf} (score log_p)
                                handleObs {prf} (k y)

handleSamp : MonadSample m => (Elem Sample es) => (prf : Elem (Lift m) (es - Sample)) =>
             Prog es a -> Prog (es - Sample) a
handleSamp (Val x)   = pure x  
handleSamp (Op op k) = case discharge op of
    Left op'              => Op op' (handleSamp {prf} . k) 
    Right (MkSample d)    => do y <- liftM {prf} (sampleBayes d)
                                handleSamp {prf} (k y)
  where sampleBayes : PrimDist b -> m b
        sampleBayes (Normal mu std)     = Monad.Bayes.Interface.normal mu std
        sampleBayes (Bernoulli p)       = Monad.Bayes.Interface.bernoulli p
        sampleBayes (Binomial n p)      = Monad.Bayes.Interface.binomial n p
        sampleBayes (Uniform min max)   = Monad.Bayes.Interface.uniform min max

public export
toMBayes : MonadInfer m => Env env -> Model env (Dist :: ObsReader env :: Lift m :: []) a -> m a
toMBayes env = handleLift . handleSamp {m} . handleObs {m} . handleCore env