module Experiments.ModelIxExperiment


fstOrSnd : Bool -> (a, a) -> a
fstOrSnd True (x, y) = x
fstOrSnd False (x, y) = y 

data ModelIx : (env : List String) -> (x : Type) -> Type where
  Pure      : a -> ModelIx [] a
  (>>=)     : ModelIx xs a -> (a -> ModelIx ys b) -> ModelIx (xs ++ ys) b  
  If        : (b : Bool) -> (ModelIx omega1 a) -> (ModelIx omega2 a) 
            -> ModelIx (fstOrSnd b (omega1, omega2)) a

partial
iF : (b : Bool) -> (m1 : ModelIx omega1 a) -> (m2 : ModelIx omega2 a) -> (b ** ModelIx (fstOrSnd b (omega1, omega2)) a)
iF True m1 m2 = (True ** m1)

exampleModelIx : Bool -> ModelIx [] Double
exampleModelIx b = do
  iF b  (Pure 6)  (Pure 5)

