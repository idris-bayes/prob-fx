module ProbFX.Env

import public Data.So
import Data.List
import Data.List.Elem
import Decidable.Equality
import ProbFX.PropEq

||| Assign an observable variable name to a trace of values
public export
data Assign : String -> Type -> Type where
  MkAssign : (x : String) -> (trace : List a) -> Assign x a

infixr 10 ::=
public export
(::=) : (x : String) -> (trace : List a) -> Assign x a
(::=) x vs = MkAssign x vs

||| Model environment
public export
UniqueVar : (var : String) -> (env : List (String, Type)) -> Bool
UniqueVar x env = find x (map fst env) == False
  where find : Eq a => a -> List a -> Bool
        find x []        = False
        find x (y :: xs) = (x == y) || (find x xs)

public export
data Env : List (String, Type)  -> Type where
  ENil  : Env []
  ECons : Assign x a -> Env env -> (prf : So (UniqueVar x env)) => Env ((x, a) :: env)

||| Environment constraints
public export
Observable : (env : List (String, Type)) -> (var : String) -> (var_type : Type) -> Type
Observable env x a = Elem (x, a) env

public export
Observables : (env : List (String, Type)) -> (var : List String) -> (var_type : Type) -> Type
Observables env (x :: xs) a = (Elem (x, a) env, Observables env xs a)
Observables env [] a        = ()

||| Environment constructors
export
(<:>) : Assign x a -> Env env -> (prf : So (UniqueVar x env)) => Env ((x, a) :: env)
(<:>) xv env = ECons xv env
infixr 10 <:>

export
emptyEnv : {auto prf : Env env} -> Env env
emptyEnv {prf = ENil}                      = ENil
emptyEnv {prf = ECons (MkAssign x _) rest} = ECons (MkAssign x []) (emptyEnv {prf = rest})

export
maybeEmptyEnv : {env : _} -> Maybe (Env env)
maybeEmptyEnv {env = Nil}            = pure ENil
maybeEmptyEnv {env = (x, _) :: rest} {} = do
  v <- maybeEmptyEnv {env = rest}
  case choose (UniqueVar x rest) of 
    Left   p => pure $ ECons (x ::= []) v {prf = p}
    Right  _ => Nothing

||| Get the trace of an observable variable
export
get : (x : String) -> Env env -> {auto prf : Elem (x, a) env} -> List a
get x (ECons (MkAssign x v) xvs) {prf = Here}   = v
get x (ECons other xvs) {prf = There later}     = get x xvs {prf = later} 

||| Set the trace of an observable variable
export
set : (x : String) -> (trace : List a) -> Env env -> {auto prf : Elem (x, a) env} -> Env env
set x v (ECons (MkAssign x _) xvs) {prf = Here}   = ECons (x ::= v) xvs
set x v (ECons other xvs) {prf = There later}     = ECons other (set x v xvs {prf = later})

||| Apply a function to the trace of an observable variable
export
update : (x : String) -> (List a -> List a) -> Env env -> {auto prf : Elem (x, a) env} -> Env env
update x f (ECons (MkAssign x v) xvs) {prf = Here}   = ECons (x ::= f v) xvs
update x f (ECons other xvs) {prf = There later}     = ECons other (update x f xvs {prf = later})

||| Get the size of an environment as the sum of its trace lengths
export
length : Env env -> Nat
length ENil                       = Z
length (ECons (MkAssign x v) xvs) = length v + length xvs

exampleEnv : Env [("x", Int), ("y", Int)]
exampleEnv = ("x" ::= []) <:> ("y" ::= []) <:> ENil