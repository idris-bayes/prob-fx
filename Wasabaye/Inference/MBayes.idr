module Wasabaye.Inference.MBayes

import Data.List
import Control.Eff
import Control.Monad.Bayes.Interface
import Wasabaye.Env
import Wasabaye.Model
import Wasabaye.Effects.Lift
import Wasabaye.Effects.Dist

handleObs : MonadCond m => (Has Observe es) => (prf : Has (Lift m) (es - Observe)) => 
            Eff es a -> Eff (es - Observe) a
handleObs prog = case toView prog of
  Pure x    => pure x
  Bind op k => case decomp op of
    Left op'              => fromView $ Bind op' (handleObs {prf} . k)
    Right (MkObserve d y) => do let log_p = log_prob d y
                                liftM {prf} (score log_p)
                                handleObs {prf} (k y)

handleSamp : MonadSample m => (Has Sample es) => (prf : Has (Lift m) (es - Sample)) =>
             Eff es a -> Eff (es - Sample) a
handleSamp prog = case toView prog of
  Pure x  => pure x
  Bind op k => case decomp op of
    Left op'              => fromView $ Bind op' (handleSamp {prf} . k) 
    Right (MkSample d)    => do y <- liftM {prf} (sampleBayes d)
                                handleSamp {prf} (k y)
  where sampleBayes : PrimDist b -> m b
        sampleBayes (Normal mu std) = Monad.Bayes.Interface.normal mu std
        sampleBayes (Bernoulli p)   = Monad.Bayes.Interface.bernoulli p
        sampleBayes (Binomial n p)  = do
          xs <- sequence $ replicate n (Monad.Bayes.Interface.bernoulli p)
          pure $ length $ filter (== True) xs
        sampleBayes (Uniform min max)   = Monad.Bayes.Interface.uniform min max

toMBayes : MonadInfer m => Env env -> Model env (Dist :: ObsReader env :: Lift m :: []) a -> m a
toMBayes env = handleLift . handleSamp {m} . handleObs {m} . handleCore env