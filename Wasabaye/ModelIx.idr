module Wasabaye.ModelIx

data ModelIx : (omega : List (String, Type)) -> (x : Type) -> Type where
  Pure  : a -> ModelIx [] a
  (>>=) : ModelIx omega1 a -> (a -> ModelIx omega2 b) -> ModelIx (omega1 ++ omega2) b

-- normal 
f : ModelIx [] Int
f = do
  x <- Pure 5
  Pure x
