module Wasabaye.Inference.MBayes

import Control.Eff
import Control.Monad.Bayes.Interface
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
