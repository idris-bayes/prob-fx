module Wasabaye.Effects.TraceDep

import Data.List
import Decidable.Equality
import Control.Function
import Data.Vect

data Elem : a -> List (a, Type) -> Type where
  ||| A proof that the element is at the head of the list
  Here : Elem x ((x, a) :: xs)
  ||| A proof that the element is in the tail of the list
  There : Elem x xs -> Elem x ((y, a) :: xs)

export
Uninhabited (Here = There e) where
  uninhabited Refl impossible

export
Uninhabited (There e = Here) where
  uninhabited Refl impossible

export
Injective (There {x} {y} {xs}) where
  injective Refl = Refl

export
DecEq (Elem x xs) where
  decEq Here Here = Yes Refl
  decEq (There this) (There that) = decEqCong $ decEq this that
  decEq Here (There later) = No absurd
  decEq (There later) Here = No absurd

export
Uninhabited (Elem {a} x []) where
  uninhabited Here impossible
  uninhabited (There p) impossible

export
Uninhabited (x = z) => Uninhabited (Elem z xs) => Uninhabited (Elem z $ (x, _)::xs) where
  uninhabited Here @{xz} = uninhabited Refl @{xz}
  uninhabited (There y) = uninhabited y

||| An item not in the head and not in the tail is not in the list at all.
export
neitherHereNorThere : Not (x = y) -> Not (Elem x xs) -> Not (Elem x ((y, _) :: xs))
neitherHereNorThere xny _     Here        = xny Refl
neitherHereNorThere _   xnxs  (There xxs) = xnxs xxs

isElem : DecEq a => (x : a) -> (xs : List (a, Type)) -> Dec (Elem x xs)
isElem x [] = No absurd
isElem x ((y, _) :: xs) with (decEq x y)
  isElem x ((x, _) :: xs) | Yes Refl = Yes Here
  isElem x ((y, _) :: xs) | No xny with (isElem x xs)
    isElem x ((y, _) :: xs) | No xny | Yes xxs = Yes (There xxs)
    isElem x ((y, _) :: xs) | No xny | No xnxs = No (neitherHereNorThere xny xnxs)

lookupType : (x : _) -> (env : _) -> (prf : Elem x env) => Type
lookupType x ((x, ty) :: rest) {prf=Here}        = ty
lookupType x ((y, ty) :: rest) {prf=There later} = lookupType x rest {prf = later}

lookupEnv : (env : List (String, Type)) -> (x : String) -> Elem x env => (lookupType x env)

Trace : Type
Trace = List (DPair String (\x => List Type))

-- lookupTrace : Trace ->