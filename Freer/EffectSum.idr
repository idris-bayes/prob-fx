module Freer.EffectSum 

import Decidable.Equality
import Decidable.Equality.Core
import Data.List.AtIndex
import Data.List.NonEmpty

-- | Natural number and proof of memberships
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

-- | EffectSum
export
data EffectSum : (es : List (Type -> Type)) -> Type -> Type where
  MkEffectSum : {auto ok : NonEmpty es} -> (k : Nat) -> (AtIndex e es k) -> e x -> EffectSum es x

-- | Inject and project out of EffectSum
export
interface FindElem e es 
       => Member (e : Type -> Type) (es : List (Type -> Type)) where
  inj : {auto ok : NonEmpty es} -> e x -> EffectSum es x
  inj op = let MkElem n p = findElem {x = e} {xs = es} in MkEffectSum n p op

  prj : EffectSum es x -> Maybe (e x)
  prj op = let MkElem n p = findElem {x = e} {xs = es} in prj' n p op
    where prj' : (k : Nat) -> (AtIndex e es k) -> EffectSum es a -> Maybe (e a)
          prj' k p (MkEffectSum k' q op) = case (decEq k k')  of
            Yes Refl => rewrite atIndexUnique p q in Just op
            No neq   => Nothing

Members : List (Type -> Type) -> List (Type -> Type) -> Type
Members [] _ = ()
Members (e :: es) ess = Member e ess

-- | Discharge effect from front of signature
discharge : {auto ok : NonEmpty es} -> EffectSum (e :: es) x -> Either (EffectSum es x) (e x)
discharge (MkEffectSum Z Z t)         = Right t
discharge (MkEffectSum (S n) (S k) t) = Left (MkEffectSum n k t)

-- | Prepend effect to front of signature
export
weaken : {auto ok : NonEmpty es} -> EffectSum es x -> EffectSum (e :: es) x
weaken {ok = IsNonEmpty} (MkEffectSum n m e) = (MkEffectSum (S n) (S m) e) 