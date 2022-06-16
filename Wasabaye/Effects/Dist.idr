module Wasabaye.Effects.Dist

import Control.Eff
import Statistics.Distribution.Normal 
import Statistics.Distribution.Uniform 

public export
data PrimDist : a -> Type where
  Normal    : Double -> Double -> PrimDist Double
  Bernoulli : Double -> PrimDist Bool
  Binomial  : Nat -> Double -> PrimDist Nat
  Uniform   : Double -> Double -> PrimDist Double

public export
record Dist (a : Type) where
  constructor MkDist
  dist : PrimDist a
  obs  : Maybe a

public export
data Observe : a -> Type where 
  MkObserve : PrimDist a -> a -> Observe a

public export
data Sample : a -> Type where
  MkSample  : PrimDist a -> Sample a

-- Eff version
public export
handleDist : (prf : Has Dist es) => Eff es a -> Eff (Observe :: Sample :: es - Dist) a
handleDist prog = case toView prog of
  Pure x    => pure x
  Bind op k => case decomp op {prf} of
    Right d => case d.obs of Just y  => do x <- send (MkObserve d.dist y) 
                                           (handleDist . k) x
                             Nothing => send (MkSample d.dist) >>= (handleDist . k)
    Left op' => fromView $ Bind (weaken1 $ weaken1 op') (handleDist . k)

partial
prob : PrimDist a -> a -> Double
prob (Normal mu std) y = normal_pdf mu std y