module Wasabaye2.ModelIx

import Data.Subset

namespace ModelIxA
  data ModelIx : (omega : List (String, Type)) -> (x : Type) -> Type where
    Pure      : a -> ModelIx [] a
    (>>=)     : {omega1 : _ } -> {omega2 : _ } -> ModelIx omega1 a -> (a -> ModelIx omega2 b) -> ModelIx (omega1 ++ omega2) b
    Normal    : Double -> Double -> (y : String) -> ModelIx [(y, Double)] Double
    Uniform   : Double -> Double -> (y : String) -> ModelIx [(y, Double)] Double
    Bernoulli : Double -> (y : String) -> ModelIx [(y, Bool)] Bool
  -- "If" concatenates environments from each branch
    If        : Bool   -> ModelIx omega1 a -> ModelIx omega2 a -> ModelIx (omega1 ++ omega2) a

  normal    = Normal
  uniform   = Uniform
  bernoulli = Bernoulli

  -- Example 1
  exampleModelIx : ModelIx [("x", Double)] Double
  exampleModelIx = do
    x <- normal 0 2 "x"
    Pure x

  exampleModelIxImpl : ModelIx [("x", Double)] Double
  exampleModelIxImpl = do
    ((>>=) {omega1 = [("x", Double)]}) (normal 0 2 "x")  (\x => Pure x)

  -- Example 2 
  exampleModelIx2 : ModelIx [("p", Bool), ("y", Double)] Double
  exampleModelIx2 = do
    b <- bernoulli 0.5 "p"
    y <- If b (Pure 6) (Normal 0 1 "y")
    Pure y

  -- Example 3: Need to clarify why a normal `if` statement doesn't work
  -- exampleModelIx3 : ModelIx [("p", Bool), ("a", Double), ("b", Double)] Double
  -- exampleModelIx3 = do
  --   b <- bernoulli 0.5 "p"
  --   y <- if b then (normal 0 2 "a") else (normal 0 2 "b") 
  --   Pure y

namespace ModelIxB
  data ModelIx : (env : List (String, Type)) -> (x : Type) -> Type where
    Pure      : a -> ModelIx [] a
    (>>=)     : ModelIx xs a -> (a -> ModelIx ys b) -> ModelIx (xs ++ ys) b  
    Bernoulli : Double -> (y : String) -> ModelIx [(y, Bool)] Bool
    Normal    : Double -> Double -> (y : String) -> ModelIx [(y, Double)] Double

  -- "iF" returns a model from one of the two branches.
  iF : Bool -> (ModelIx omega1 a) -> (ModelIx omega2 a) -> (b ** ModelIx (if b then omega1 else omega2) a)
  iF True m1 m2  = (True ** m1)
  iF False m1 m2 = (False ** m2)

  -- Example 1
  exampleModelIx1 : ModelIx [("b", Bool)] (b ** ModelIx (if b then [] else [("y", Double)]) Double)
  exampleModelIx1 = do
    b <- Bernoulli 0.5 "b"
    let m = iF b (Pure 6) (Normal 0 1 "y")
    case m of (True ** m1)  => Pure (True ** m1)
              (False ** m2) => Pure (False ** m2)

  -- Not possible to define
  flattenModelIx : {ys, zs : List (String, Type) } 
    -> ModelIx xs (b ** ModelIx (if b then ys else zs) a)
    -> (b ** ModelIx (if b then (xs ++ ys) else (xs ++ zs)) a)


-- || Model with accumulating Subset constraints?
namespace ModelIxC

  (++) : Subset sub1 sup -> Subset sub2 sup -> Subset (sub1 ++ sub2) sup
  (++) [] [] =  Nil
  (++) [] (x :: xs) = (x :: xs)
  (++) (x :: xs) ys = (x :: (xs ++ ys))

  data ModelIx : (prf : Subset sub sup) -> Type -> Type where
    Pure  : {auto prf : Subset [] sup} -> a -> ModelIx prf a
    (>>=) : {prf1 : Subset sub1 sup} -> {prf2: Subset sub2 sup} -> ModelIx prf1 a -> (a -> ModelIx prf2 b) -> ModelIx (prf1 ++ prf2) b
    -- Normal    : Double -> Double -> (y : String) -> ModelIx [(y, Double)] Double