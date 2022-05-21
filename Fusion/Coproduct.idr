module Fusion.Coproduct


-- | Higher-order effect sum
data (:+:) : (f : (Type -> Type) -> Type -> Type) 
          -> (g : (Type -> Type) -> Type -> Type) 
          -> (n : Type -> Type)                     -- continuation k is split into 'n' and 'a', underlying computation type of signature (f :+: g)
          -> (a : Type)
          -> Type where 
  L : f n a -> (:+:) f g n a
  R : g n a -> (:+:) f g n a

infixr 8 :+:

interface Member (0 sub : (Type -> Type) -> (Type -> Type))
                 (0 sup : (Type -> Type) -> (Type -> Type)) where
  inj : sub n a -> sup n a


Member sub sub where
  inj = id