module Wasabaye.Prog

import Data.List.Elem 

-- ||| Re-implementation of Stefan's Eff, for experimenting and learning purposes.

{- Effect sums -}
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
(-) : (es : List Effect) -> (e : Effect) -> {auto prf : Elem e es} -> List Effect
(-) (e :: es)  e {prf=Here}       = es
(-) (e' :: es) e {prf=There prf'} = e' :: (Prog.(-) es e {prf=prf'})

public export
weaken1 : EffectSum es a -> EffectSum (e :: es) a
weaken1 (Sum prf op) = Sum (There prf) op

public export 
discharge : {auto prf : Elem e es} -> EffectSum es a -> Either (EffectSum (Prog.(-) es e) a) (e a)
discharge {prf = Here} (Sum Here op)                = Right op
discharge {prf = Here} (Sum (There later) op)       = Left (Sum later op)
discharge {prf = There later} (Sum Here op)        = Left (Sum Here op) 
discharge {prf = There later1} {es = e' :: es'} (Sum (There later2) op) = 
  let res : Either (EffectSum (Prog.(-) es' e) a) (e a) = discharge {prf=later1} (Sum later2 op)
  in  mapFst weaken1 res

{- Prog -}
-- data Prog : (es : List Effect) -> (a : Type) -> Type where
--   Op : EffectSum es 