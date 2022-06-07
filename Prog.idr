module Prog 

import Decidable.Equality
import Decidable.Equality.Core
import Data.List.AtIndex
import Data.List.NonEmpty

------------------------------------------
-- Infrastructure for Algebraic Effects --
------------------------------------------

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
public export
data EffectSum : (es : List (Type -> Type)) -> Type -> Type where
  MkEffectSum : (k : Nat) -> (AtIndex e es k) -> e x -> EffectSum es x

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

export implementation Member e (e :: es)
export implementation Member e es => Member e (e' :: es)

export
Members : List (Type -> Type) -> List (Type -> Type) -> Type
Members [] _ = ()
Members (e :: es) ess = Member e ess

-- | Discharge effect from front of signature
export
discharge :  EffectSum (e :: es) x    -- if Left, then 'es' must be non-empty. If Right, then 'es' is not necessarily non-empty.
          -> Either (EffectSum es x) (e x)
discharge (MkEffectSum Z Z t)         = Right t
discharge (MkEffectSum (S n) (S k) t) = Left (MkEffectSum n k t)

-- | Prepend effect to front of signature
export
weaken_op : EffectSum es x -> EffectSum (e :: es) x
weaken_op  (MkEffectSum n m e) = (MkEffectSum (S n) (S m) e) 

-- | Program with effect signature
public export
data Prog : (es : List (Type -> Type)) -> (a : Type) -> Type where
  Op  : {auto ok : NonEmpty es} -> (op : EffectSum es x) -> (k : x -> Prog es a) -> Prog es a
  Val : a -> Prog es a

export
implementation Functor (Prog es) where
  map f (Op op k) = Op op (map f . k)
  map f (Val a)   = Val (f a)

export
implementation Applicative (Prog es) where
  pure = Val
  Op op k <*> p = Op op (\x => k x <*> p) 
  Val f   <*> p = map f p

export
implementation Monad (Prog es) where
  Op op k >>= f = Op op (assert_total (>>= f) . k)
  Val x   >>= f = f x

weaken : Prog es a -> Prog (e :: es) a
weaken (Op op k) = Op (weaken_op op) (weaken . k)
weaken (Val x)   = Val x

export
call : {e : Type -> Type} -> {es : List (Type -> Type)} -> {auto ok : NonEmpty es} -> Member e es 
    => e x -> Prog es x
call op = Op (inj op) Val

run : Prog [] a -> a
run (Val x) = x

data Id : a -> Type where
  MkId : a -> Id a

data IdB : a -> Type where
  MkIdB : a -> IdB a

partial
handleId : {es : _} -> Prog (Id :: es) a -> Prog (IdB :: es) a
handleId (Val a)   = Val a
handleId (Op op k) with (discharge op)
  _ | Right (MkId x) = do y <- call (MkIdB x)
                          (handleId . k) y
