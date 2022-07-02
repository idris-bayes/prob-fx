module Wasabaye.Effects.TraceDep

import Data.List
import Decidable.Equality
import Control.Function
import Data.Vect

||| Lookup
data Lookup : a -> List (a, Type) -> Type where
  Here : Lookup x ((x, a) :: xs)
  There : Lookup x xs -> Lookup x ((y, a) :: xs)

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
DecEq (Lookup x xs) where
  decEq Here Here = Yes Refl
  decEq (There this) (There that) = decEqCong $ decEq this that
  decEq Here (There later) = No absurd
  decEq (There later) Here = No absurd

export
Uninhabited (Lookup {a} x []) where
  uninhabited Here impossible
  uninhabited (There p) impossible

export
Uninhabited (x = z) => Uninhabited (Lookup z xs) => Uninhabited (Lookup z $ (x, _)::xs) where
  uninhabited Here @{xz} = uninhabited Refl @{xz}
  uninhabited (There y) = uninhabited y

export
neitherHereNorThere : Not (x = y) -> Not (Lookup x xs) -> Not (Lookup x ((y, _) :: xs))
neitherHereNorThere xny _     Here        = xny Refl
neitherHereNorThere _   xnxs  (There xxs) = xnxs xxs

isElem : DecEq a => (x : a) -> (xs : List (a, Type)) -> Dec (Lookup x xs)
isElem x [] = No absurd
isElem x ((y, _) :: xs) with (decEq x y)
  isElem x ((x, _) :: xs) | Yes Refl = Yes Here
  isElem x ((y, _) :: xs) | No xny with (isElem x xs)
    isElem x ((y, _) :: xs) | No xny | Yes xxs = Yes (There xxs)
    isElem x ((y, _) :: xs) | No xny | No xnxs = No (neitherHereNorThere xny xnxs)

lookupType : (x : _) -> (env : _) -> (prf : Lookup x env) => Type
lookupType x ((x, ty) :: rest) {prf=Here}        = ty
lookupType x ((y, ty) :: rest) {prf=There later} = lookupType x rest {prf = later}

||| s
lookupVal : (x : String) -> (env : List (String, Type)) -> Lookup x env => (lookupType x env)
lookupVal 

Trace : Type
Trace = List (DPair String (\x => List Type))

-- lookupTrace : Trace ->