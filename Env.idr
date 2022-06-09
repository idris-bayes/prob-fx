module Env

import Data.List.Elem
import Data.List

infixr 10 ::=
data Assign : String -> Type -> Type where
  MkAssign : (x : String) -> (trace : List a) -> Assign x a

infixr 10 ::=
(::=) : (x : String) -> (trace : List a) -> Assign x a
(::=) x vs = MkAssign x vs

data Env : List (String, Type) -> Type where
  ENil  : Env []
  ECons : Assign x a -> Env env -> Env ((x, a) :: env)

infixr 10 <:>
(<:>) : Assign x a -> Env env -> Env ((x, a) :: env)
(<:>) xv env = ECons xv env

get : (x : String) -> Env env -> {auto prf : Elem (x, a) env} -> Maybe a
get x (ECons (MkAssign x v) xvs) {prf = Here}        = head' v
get x (ECons (MkAssign y v) xvs) {prf = There later} = get x xvs {prf = later} 