module ProbFX.Prog

import public Data.List.Elem 

||| Effect sums 
public export
Effect : Type
Effect = Type -> Type 

public export 
data EffectSum : (es : List Effect) -> (a : Type) -> Type where
  Sum : (prf : Elem e es) -> (op : e a) -> EffectSum es a

public export
Uninhabited (EffectSum [] a) where
  uninhabited (Sum prf op) impossible

public export
inj : {auto prf : Elem e es} -> e a -> EffectSum es a
inj = Sum prf

public export
prj : {auto prf : Elem e es} -> EffectSum es a -> Maybe (e a)
prj {prf = Here}       (Sum Here op)         = Just op
prj {prf = Here}       (Sum (There _) _)     = Nothing
prj {prf = There _}    (Sum Here _)          = Nothing
prj {prf = There prf1} (Sum (There prf2) op) = prj {prf=prf1} (Sum prf2 op)

public export
prj1 : EffectSum [e] a -> e a
prj1 (Sum Here op) = op
prj1 (Sum (There later) op) impossible

public export
(-) : (es : List a) -> (e : a) -> {auto prf : Elem e es} -> List a
(-) (e :: es)  e {prf=Here}       = es
(-) (e' :: es) e {prf=There prf'} = e' :: ((-) es e {prf=prf'})

public export
weaken1 : EffectSum es a -> EffectSum (e :: es) a
weaken1 (Sum prf op) = Sum (There prf) op

public export 
discharge : {auto prf : Elem e es} -> EffectSum es a -> Either (EffectSum (es - e) a) (e a)
discharge {prf = Here} (Sum Here op)               = Right op
discharge {prf = Here} (Sum (There later) op)      = Left (Sum later op)
discharge {prf = There later} (Sum Here op)        = Left (Sum Here op) 
discharge {prf = There later1} {es = e' :: es'} (Sum (There later2) op) = 
  let res : Either (EffectSum ((-) es' e) a) (e a) = discharge {prf=later1} (Sum later2 op)
  in  mapFst weaken1 res

||| Subset
public export
data Subset : {0 a: Type} -> (xs, ys : List a) -> Type where
  Nil : Subset [] ys
  (::) : {auto 0 x: a} -> (e : Elem x ys) -> Subset xs ys -> Subset (x::xs) ys

public export
lemma_subset : Subset fs fs' -> Elem f fs -> Elem f fs'
lemma_subset Nil has0 impossible
lemma_subset (e :: _     ) Here = e
lemma_subset (_ :: subset) (There has) = lemma_subset subset has

public export
weaken : (subset : Subset fs fs') => EffectSum fs a -> EffectSum fs' a
weaken (Sum ix val) = Sum (lemma_subset subset ix) val

||| Prog
public export
data Prog : (es : List Effect) -> (a : Type) -> Type where
  Op  : (op : EffectSum es x) -> (k : x -> Prog es a) -> Prog es a
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

public export
call : Elem f fs => f t -> Prog fs t
call op = Op (inj op) Val