module ProbFX2.MonadIx

interface Monoid w => MonadIx w (0 m : w -> Type -> Type) | m where
  (>>=) : {0 i : w} -> {0 j : w} -> m i a -> (a -> m j b) -> m (Prelude.(<+>) i j) a
  pure  : a -> m Prelude.neutral a

data PrimDist : a -> Type where
  Normal    : (mu : Double) -> (std : Double) -> PrimDist Double
  Bernoulli : (p : Double) -> PrimDist Bool
  Uniform   : (min : Double) -> (max : Double) -> PrimDist Double
