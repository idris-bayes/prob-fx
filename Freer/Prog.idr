module Freer.Prog 


member : Eq a => a -> List a -> Bool
member e (e' :: es) = e == e' || member e' es
member e Nil        = False

interface Member (e : a) (es : List a) where


data Prog : (es : List (Type -> Type)) -> Type -> Type where
  -- Op : x == Int => Member e es => (op : e x) -> (k : x -> Prog es a) -> Prog es a