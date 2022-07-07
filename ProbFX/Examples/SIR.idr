module ProbFX.Examples.SIR

import Data.Vect
import Data.List
import Data.List.Elem
import ProbFX.Env 
import ProbFX.Sampler
import ProbFX.Inference.SIM
import ProbFX.Inference.MBAYES
import ProbFX.Effects.Lift
import ProbFX.Examples.HMM 
import ProbFX.Model as PFX
import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Control.Monad.Bayes.Weighted
import Control.Monad.Bayes.Traced.Static
import Control.Monad.Bayes.Inference.SMC
import Control.Monad.Bayes.Inference.RMSMC

||| Some additional infrastructure (row-polymorphism) for modularity
data Record : List (String, Type) -> Type where
  Empty : Record []
  Cons : (key : String) -> (val : a) -> Record rows -> Record ((key, a) :: rows)

update : (key : String) -> (new : a) -> Record k -> {auto prf : Elem (key, a) k} -> Record k
update key new (Cons key val r) {prf = Here} = Cons key new r
update key new (Cons y val r) {prf = (There later)} = Cons y val $ update key new r

lookup : (key : String) -> Record k -> {auto prf : Elem (key, a) k} -> a
lookup key (Cons key val x) {prf = Here} = val
lookup key (Cons x val y) {prf = (There later)} = lookup key y

||| SIR transition models
transSI : Elem ("s", Nat) popl => Elem ("i", Nat) popl => Elem ("r", Nat) popl => 
  (beta : Double) -> Record popl -> Model env es (Record popl)
transSI beta pop  = do
  let (s_0, i_0, r_0) : (Nat, Nat, Nat) = (lookup "s" pop,  lookup "i" pop, lookup "r" pop)
  dN_SI <- binomial' {env} s_0 (1 - exp ((-beta * cast i_0) / cast (s_0 + i_0 + r_0)))

  pure $ update "s" (minus s_0 dN_SI) (update "i" (i_0 + dN_SI) pop)

transIR : Elem ("i", Nat) popl => Elem ("r", Nat) popl =>
  (gamma : Double) -> Record popl -> Model env es (Record popl)
transIR gamma pop = do
  let (i_0, r_0) =  (lookup "i" pop,  lookup "r" pop)
  dN_IR <- binomial' {env} i_0 (1 - exp (-gamma))
  
  pure $ update "r" (r_0 + dN_IR) (update "i" (minus i_0 dN_IR) pop)

-- transSIR :: (Member (Writer [Record popl]) es, Lookups popl '["s", "i", "r"] Int)
--   => TransModel env es (Double, Double) (Record popl)
-- transSIR (beta, gamma) popl = do
--   popl <- (transSI beta >=> transIR gamma) popl
--   tellM [popl]
--   pure popl