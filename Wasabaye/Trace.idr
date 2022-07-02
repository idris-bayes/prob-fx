module Wasabaye.Trace

import Data.List
import Wasabaye.Env
import Wasabaye.Prog
import Wasabaye.PrimDist
import Wasabaye.Effects.Dist

||| Primitive values
public export
data PrimVal = PrimDouble Double | PrimNat Nat | PrimBool Bool

||| Trace of sampled values
public export
Trace : Type
Trace = List (String, List PrimVal)

export
toPrimVal : PrimDist a -> (a -> PrimVal)
toPrimVal (Normal _ _)   = PrimDouble 
toPrimVal (Uniform _ _)  = PrimDouble 
toPrimVal (Bernoulli _)  = PrimBool 
toPrimVal (Binomial _ _) = PrimNat 
toPrimVal (Beta _ _) = ?toPrimVal_missing_case_1
toPrimVal (Gamma _ _) = ?toPrimVal_missing_case_2
toPrimVal (UniformD _ _) = ?toPrimVal_missing_case_3
toPrimVal (Discrete _) = ?toPrimVal_missing_case_4
toPrimVal (Poisson _) = ?toPrimVal_missing_case_5
toPrimVal (Categorical _) = ?toPrimVal_missing_case_6

export
insertTrace : (String, PrimVal) -> Trace -> Trace
insertTrace (x, val) ((y, vals) :: rest) with (x == y)
    _ | True  = (y, val :: vals) :: rest
    _ | False = (y, vals) :: insertTrace (x, val) rest
insertTrace (x, val) [] = [(x, [val])]

||| A run-time conversion of sample traces to output environments
fromPrimVal : {ty : Type} -> PrimVal -> Maybe ty 
fromPrimVal {ty=Double} (PrimDouble x) = Just x 
fromPrimVal {ty=Nat}    (PrimNat x)    = Just x
fromPrimVal {ty=Bool}   (PrimBool x)   = Just x
fromPrimVal _                          = Nothing 

fromPrimVals : {x : String} -> {ty : Type} -> List PrimVal -> Assign x ty
fromPrimVals pvs with (sequence $ map (fromPrimVal {ty}) pvs) 
  _ | Just vals = x ::= vals 
  _ | Nothing   = x ::= []

public export
fromTrace : (env : List (String, Type)) -> {auto prf : Env env} -> Trace -> Env env
fromTrace Nil               {prf = ENil}      _ = ENil
fromTrace ((x, ty) :: rest) {prf = ECons _ _} strace with (lookup x strace)
  _ | Just prim_vals = ECons (fromPrimVals {x} {ty} prim_vals) (fromTrace rest strace) 
  _ | Nothing        = ECons (x ::= [])                        (fromTrace rest strace) 
