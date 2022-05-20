module EffectSum 

data EffectSum : (es : List (Type -> Type)) -> Type where
  MkEffectSum : EffectSum es 
