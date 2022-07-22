module ProbFX.Trace

import Data.List
import Data.Vect
import ProbFX.Env
import ProbFX.Prog
import ProbFX.PrimDist
import ProbFX.Effects.Dist

||| Primitive values
public export
data PrimVal = PrimDouble Double | PrimNat Nat | PrimBool Bool | Prim

export
toPrimVal : PrimDist a -> (a -> PrimVal)
toPrimVal (Normal _ _)    = PrimDouble
toPrimVal (Uniform _ _)   = PrimDouble
toPrimVal (Bernoulli _)   = PrimBool
toPrimVal (Binomial _ _)  = PrimNat
toPrimVal (Beta _ _)      = PrimDouble
toPrimVal (Gamma _ _)     = PrimDouble
toPrimVal (Poisson _)     = PrimNat
toPrimVal (Categorical _) = PrimNat . finToNat
toPrimVal (Discrete _)    = ?to_do_toPrimVal_discrete
toPrimVal (Dirichlet _)   = ?to_do_toPrimVal_dirichlet

||| A run-time conversion of sample traces to output environments
fromPrimVal : {ty : Type} -> PrimVal -> Maybe ty
fromPrimVal {ty=Double} (PrimDouble x) = Just x
fromPrimVal {ty=Nat}    (PrimNat x)    = Just x
fromPrimVal {ty=Bool}   (PrimBool x)   = Just x
fromPrimVal _                          = ?to_do_fromPrimVal

fromPrimVals : {x : String} -> {ty : Type} -> List PrimVal -> Assign x ty
fromPrimVals pvs with (sequence $ map (fromPrimVal {ty}) pvs)
  _ | Just vals = x ::= vals
  _ | Nothing   = x ::= []

||| Trace of sampled values
public export
STrace : Type
STrace = List (String, List PrimVal)

export
insertSTrace : (String, PrimVal) -> STrace -> STrace
insertSTrace (x, val) ((y, vals) :: rest) with (x == y)
    _ | True  = (y, val :: vals) :: rest
    _ | False = (y, vals) :: insertSTrace (x, val) rest
insertSTrace (x, val) [] = [(x, [val])]

||| Handler for recording samples
traceSamples' : (prf : Elem Sample es) => STrace -> Prog es a -> Prog es (a, STrace)
traceSamples' strace (Val x) = pure (x, strace)
traceSamples' strace (Op op k) with (prj op {prf})
  _ | Just (MkSample d tag)
        = do  y <- call (MkSample d tag)
              let p = toPrimVal d y
                  strace' = insertSTrace (tag, p) strace
              (traceSamples' strace' . k) y
  _ | Nothing = Op op (traceSamples' strace . k)

public export
traceSamples : (prf : Elem Sample es) => Prog es a -> Prog es (a, STrace)
traceSamples = traceSamples' []

||| Trace of log probabilities
public export
LPTrace : Type
LPTrace = List (String, List Double)

insertLPTrace : (String, Double) -> LPTrace -> LPTrace
insertLPTrace (x, lp) ((y, lps) :: rest) with (x == y)
    _ | True  = (y, lp :: lps) :: rest
    _ | False = (y, lps) :: insertLPTrace (x, lp) rest
insertLPTrace (x, lp) [] = [(x, [lp])]

||| Handler for recording log-probabilities
traceLogProbs' : (prfS : Elem Sample es) => (prfO : Elem Observe es) => LPTrace -> Prog es a -> Prog es (a, LPTrace)
traceLogProbs' lptrace (Val x) = pure (x, lptrace)
traceLogProbs' lptrace (Op op k) with (prj op {prf=prfS})
  _ | Just (MkSample d tag)
        = do  y <- call (MkSample d tag)
              let lptrace' = insertLPTrace (tag, (logProb d y)) lptrace
              (traceLogProbs' lptrace' . k) y
  _ | Nothing with (prj op {prf=prfO})
    _ | Just (MkObserve d y tag)
          = do  y <- call (MkObserve d y tag)
                let lptrace' = insertLPTrace (tag, (logProb d y)) lptrace
                (traceLogProbs' lptrace' . k) y
    _ | _ = Op op (traceLogProbs' lptrace . k)

public export
traceLogProbs : (prfS : Elem Sample es) => (prfO : Elem Observe es) => Prog es a -> Prog es (a, LPTrace)
traceLogProbs = traceLogProbs' []