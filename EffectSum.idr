module EffectSum 

data EffectSum : (es : List (Type -> Type)) -> Type where
  MkEffectSum : {e : Type -> Type} -> Nat -> e a -> EffectSum es 

