module Decidables.Nat

import Data.Nat
import Decidables.Equality.Core


succInjective : (left, right : Nat) -> S left = S right -> left = right
succInjective _ _ Refl = Refl

total ZnotS : Z = S n -> Void
ZnotS Refl impossible

DecEq Nat where
  decEq Z     Z     = Yes Refl
  decEq (S n) (S m) = decEqCong $ decEq n m
  decEq Z     (S _) = No absurd
  decEq (S _) Z     = No absurd
