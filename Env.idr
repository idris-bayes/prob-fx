module Env

data Env : List (String, Type) -> Type where
  ENil  : Env []
  ECons : List a -> Env env -> Env ((x, a) :: env)