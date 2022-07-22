module ProbFX.OpenSum

import Data.List.Elem

public export
data OpenSum : List Type -> Type where
  Sum : (prf : Elem a as) -> a -> OpenSum as

public export
Uninhabited (OpenSum []) where
  uninhabited (Sum prf a) impossible

public export
inj : {auto prf : Elem a as} -> a -> OpenSum as
inj = Sum prf

public export
prj : {auto prf : Elem a as} -> OpenSum as -> Maybe a
prj {prf = Here}       (Sum Here op)         = Just op
prj {prf = Here}       (Sum (There _) _)     = Nothing
prj {prf = There _}    (Sum Here _)          = Nothing
prj {prf = There prf1} (Sum (There prf2) op) = prj {prf=prf1} (Sum prf2 op)
