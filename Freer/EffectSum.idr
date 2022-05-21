module Freer.EffectSum 

-- | Witnesses that a natural number encodes a membership proof
data AtIndex : a -> List a -> (k : Nat) -> Type where
  Z : AtIndex a (a :: as) 0
  S : AtIndex a as n -> AtIndex a (b :: as) (S n)

partial
sameAtIndex : (a : AtIndex e1 es k1) -> (b : AtIndex e2 es k2) -> Maybe (k1 = k2)
sameAtIndex Z Z = Just Refl
sameAtIndex (S k) Z = Nothing
sameAtIndex Z (S k) = Nothing
sameAtIndex (S k1) (S k2) = case sameAtIndex k1 k2 of 
  Just p => Just $ cong S p

-- | Natural number and proof of membership
data Elem : (e : a) -> (es : List a) -> Type where
  MkElem : (k : Nat) -> (AtIndex e es k) -> Elem e es

-- | Establish an element is in a list
interface FindElem (0 x : a) (0 xs : List a) where
  findElem : Elem x xs 

FindElem a (a :: as) where
  findElem = MkElem Z Z 

FindElem a as => FindElem a (b :: as) where
  findElem = let MkElem n p = findElem {x = a} {xs = as}
             in  MkElem (S n) (S p) 

-- | Effect sums
data EffectSum : (es : List (Type -> Type)) -> Type -> Type where
  MkEffectSum : {e : Type -> Type} ->  AtIndex e es k -> e a -> EffectSum es a


prj' : FindElem e es => {e : Type -> Type} -> (AtIndex e' es k) -> (e' a) -> Maybe (e a)
prj' {e} p = let MkElem n p' = findElem {x = e} {xs = es}
 in  ?x

interface FindElem e es => Member (e : Type -> Type) (es : List (Type -> Type)) where
  inj : e x -> EffectSum es x
  inj op = let MkElem n p = findElem {x = e} {xs = es} in MkEffectSum p op
  prj : EffectSum es x -> Maybe (e x)
  prj (MkEffectSum p op) = ?y

-- FindElem e es => Member e es where
--   prj = ?y