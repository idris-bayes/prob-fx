module Decidable.Equality

-- | Equality type
infixr 8 :~:
data (:~:) : a -> b -> Type where
  Refl : x :~: x

cong : {f : t -> u} -> (p : a :~: b) -> (f a :~: f b)
cong Refl = Refl

checkEqNat : (n : Nat) -> (m : Nat) -> Maybe (n :~: m)
checkEqNat 0 0 = Just Refl
checkEqNat 0 (S k) = Nothing
checkEqNat (S k) 0 = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of 
                            Nothing => Nothing
                            Just p  => Just (cong {f = S} p)
