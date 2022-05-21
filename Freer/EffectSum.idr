module Freer.EffectSum 

-- | Witnesses that a natural number encodes a membership proof
data AtIndex : a -> List a -> (k : Nat) -> Type where
  Z : AtIndex a (a :: as) 0
  S : AtIndex a as n -> AtIndex a as (S n)

data Elem : (e : a) -> (es : List a) -> Type where
  MkElem : (k : Nat) -> (AtIndex e es k) -> Elem e es

interface FindElem (0 e : a) (0 es : List a) where
  findElem : Elem e es 

FindElem a (a :: as) where
  findElem = MkElem Z Z 

-- FindElem a as => FindElem a (b :: as) where
--   findElem = MkElem S findElem {e = a} {es = (as)}

data EffectSum : (es : List (Type -> Type)) -> Type -> Type where
  MkEffectSum : {e : Type -> Type} ->  AtIndex e es k -> e a -> EffectSum es a

interface Member (e : Type -> Type) (es : List (Type -> Type)) where
  inj : e x -> EffectSum es x
  prj : EffectSum es x