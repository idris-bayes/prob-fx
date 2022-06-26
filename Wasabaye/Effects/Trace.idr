module Wasabaye.Effects.Trace

import Data.List
import Data.List.Elem
import Decidable.Equality
import Wasabaye.Env
import Wasabaye.Prog
import Wasabaye.Effects.ObsReader
import Wasabaye.Effects.Dist



-- traceSamples : {env : List (String, Type)} -> (prf : Elem Dist es) => Env env -> Prog es a -> Prog es a
-- traceSamples trace (Val x)  = pure x
-- traceSamples trace (Op op k) = case prj op {prf} of
--   Nothing                     => (Op op (traceSamples trace . k))
--   Just (MkDist d maybe_y tag) => case tag of
--     Just var => do y <- Op op k
--                   --  let y' : b = y
--                    let env' = case isElem ("var", Int) env of
--                                 Yes prf => ?hole -- update var (y ::) trace 
--                    ?hole1
--     Nothing  => ?hole2

    -- Left op' => Op op' (handleObsRead env . k)
    -- Right (Ask x) => do
    --     let vs      = get x env 
    --         maybe_v = head' vs 
    --         env'    = set x (defaultTail vs) env 
    --     handleObsRead env' (k maybe_v)

{-
data Assign : String -> Type -> Type where
  MkAssign : (x : String) -> (trace : List a) -> Assign x a

infixr 10 ::=
public export
(::=) : (x : String) -> (trace : List a) -> Assign x a
(::=) x vs = MkAssign x vs

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

infixr 10 <:>
public export
(<:>) : Assign x a -> Env env -> (prf : So (UniqueVar x env)) => Env ((x, a) :: env)
(<:>) xv env = ECons xv env

public export
get : (x : String) -> Env env -> {auto prf : Elem (x, a) env} -> List a
get x (ECons (MkAssign x v) xvs) {prf = Here}   = v
get x (ECons other xvs) {prf = There later}     = get x xvs {prf = later} 

public export
set : (x : String) -> (trace : List a) -> Env env -> {auto prf : Elem (x, a) env} -> Env env
set x v (ECons (MkAssign x _) xvs) {prf = Here}   = ECons (x ::= v) xvs
set x v (ECons other xvs) {prf = There later}     = ECons other (set x v xvs {prf = later})

public export
update : (x : String) -> (List a -> List a) -> Env env -> {auto prf : Elem (x, a) env} -> Env env
update x f (ECons (MkAssign x v) xvs) {prf = Here}   = ECons (x ::= f v) xvs
update x f (ECons other xvs) {prf = There later}     = ECons other (update x f xvs {prf = later})

exampleEnv : Env [("x", Int), ("y", Int)]
exampleEnv = ("x" ::= []) <:> ("y" ::= []) <:> ENil
-}
