||| Implementation of model environments
module ProbFX.Env

import public Data.So
import Data.List
import Data.List.Elem
import Decidable.Equality

||| Assign an observable variable name to a trace of values
public export
data Assign : String -> Type -> Type where
  MkAssign : (x : String) -> (trace : List a) -> Assign x a

infix 10 ::=
export
(::=) : (x : String) -> (trace : List a) -> Assign x a
(::=) x vs = MkAssign x vs

||| A Boolean check that a variable name is not present in an environment
public export
UniqueVar : (var : String) -> (env : List (String, Type)) -> Bool
UniqueVar x env = find x (map fst env) == False
  where find : Eq a => a -> List a -> Bool
        find x []        = False
        find x (y :: xs) = (x == y) || (find x xs)

||| Model environment
public export
data Env : List (String, Type)  -> Type where
  ENil  : Env []
  ECons : Assign x a -> Env env -> (prf : So (UniqueVar x env)) => Env ((x, a) :: env)

infixr 10 <:>
export
(<:>) : Assign x a -> Env env -> (prf : So (UniqueVar x env)) => Env ((x, a) :: env)
(<:>) xv env = ECons xv env

export
emptyEnv : {auto prf : Env env} -> Env env
emptyEnv {prf = ENil}                      = ENil
emptyEnv {prf = ECons (MkAssign x _) rest} = ECons (MkAssign x []) (emptyEnv {prf = rest})

||| Specifies that an environment `env` has an observable variable `x` whose observed values are of type `a`
public export
Observable : (env : List (String, Type)) -> (x : String) -> (a : Type) -> Type
Observable env x a = Elem (x, a) env

||| For constructing multiple `Observable` constraints
public export
Observables : (env : List (String, Type)) -> (var : List String) -> (var_type : Type) -> Type
Observables env (x :: xs) a = (Elem (x, a) env, Observables env xs a)
Observables env [] a        = ()

||| Get the trace of an observable variable
export
get : (x : String) -> Env env -> {auto prf : Elem (x, a) env} -> List a
get x (ECons (MkAssign x v) xvs) {prf = Here}   = v
get x (ECons other xvs) {prf = There later}     = get x xvs {prf = later}

export
gets : (x : String) -> List (Env env) -> {auto prf : Elem (x, a) env} -> List a
gets x envs = (join . map (\env => Env.get x env)) envs

||| Set the trace of an observable variable
export
set : (x : String) -> (trace : List a) -> Env env -> {auto prf : Elem (x, a) env} -> Env env
set x v (ECons (MkAssign x _) xvs) {prf = Here}   = ECons (x ::= v) xvs
set x v (ECons other xvs) {prf = There later}     = ECons other (set x v xvs {prf = later})

||| Apply a function to the trace of an observable variable
export
modify : (x : String) -> (List a -> List a) -> Env env -> {auto prf : Elem (x, a) env} -> Env env
modify x f (ECons (MkAssign x v) xvs) {prf = Here}   = ECons (x ::= f v) xvs
modify x f (ECons other xvs) {prf = There later}     = ECons other (modify x f xvs {prf = later})

||| Get the size of an environment as the sum of its trace lengths
export
length : Env env -> Nat
length ENil                       = Z
length (ECons (MkAssign x v) xvs) = length v + length xvs