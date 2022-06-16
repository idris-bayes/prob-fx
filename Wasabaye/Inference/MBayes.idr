module Wasabaye.Inference.MBayes

import Control.Eff
import Control.Monad.Bayes.Interface
import Wasabaye.Effects.Lift
import Wasabaye.Effects.Dist

handleObs : MonadCond m => (Has (Lift m) es, Has Observe es) => 
            Eff es a -> Eff (es - Observe) a
handleObs prog = case toView prog of
  Pure x    => pure x
  Bind op k => case decomp op of
    Left op'              => fromView $ Bind op' (handleObs . k)
    Right (MkObserve d y) => ?t
    -- Right (Observe d y) => case d.obs of Just y  => do x <- send (MkObserve d.dist y) 
    --                                        (handleDist . k) x
    --                          Nothing => send (MkSample d.dist) >>= (handleDist . k)