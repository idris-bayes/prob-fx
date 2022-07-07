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
  TransModel env es Double (Record popl)
transSI beta pop  = do
  let (s_0, i_0, r_0) : (Nat, Nat, Nat) = (lookup "s" pop,  lookup "i" pop, lookup "r" pop)
  dN_SI <- binomial' {env} s_0 (1 - exp ((-beta * cast i_0) / cast (s_0 + i_0 + r_0)))

  pure $ update "s" (minus s_0 dN_SI) (update "i" (i_0 + dN_SI) pop)

transIR : Elem ("i", Nat) popl => Elem ("r", Nat) popl =>
  TransModel env es Double (Record popl)
transIR gamma pop = do
  let (i_0, r_0) =  (lookup "i" pop,  lookup "r" pop)
  dN_IR <- binomial' {env} i_0 (1 - exp (-gamma))
  
  pure $ update "r" (r_0 + dN_IR) (update "i" (minus i_0 dN_IR) pop)

transSIR : Elem ("s", Nat) popl => Elem ("i", Nat) popl => Elem ("r", Nat) popl => 
  TransModel env es (Double, Double) (Record popl)
transSIR (beta, gamma) pop = do
  pop' <- (transSI beta >=> transIR gamma) pop
  pure pop'

||| SIR observation model
obsSIR :  Elem ("i", Nat) popl => Observable env "𝜉" Nat =>
  ObsModel env es Double (Record popl) Nat
obsSIR rho pop = do
  let i_0 : Nat = lookup "i" pop
  PFX.poisson {env} (rho * cast i_0) "𝜉"
 
||| SIR transition prior
transPrior : Observables env ["β",  "γ"] Double
  => Model env es (Double, Double)
transPrior = do
  pBeta  <- PFX.gamma 2 1 "β"
  pGamma <- PFX.gamma 1 (1/8) "γ"
  pure (pBeta, pGamma)

||| SIR observation prior
obsPrior : Observable env "ρ" Double
  => Model env es Double
obsPrior = PFX.beta 2 7 "ρ"

||| SIR as HMM
sirModel : Elem ("s", Nat) popl => Elem ("i", Nat) popl => Elem ("r", Nat) popl => 
         Observable env "𝜉" Nat => Observables env ["ρ", "β", "γ"] Double =>
   Nat -> Record popl -> Model env es (List1 (Record popl))
sirModel n pop = hmmChain {env} {es} transPrior obsPrior (transSIR {env} {es}  {popl}) obsSIR n pop

||| Environment
SIREnv : List (String, Type)
SIREnv = [("β", Double), ("γ", Double), ("ρ", Double), ("𝜉", Nat)]

envExampleSim : Env SIREnv
envExampleSim = ("β" ::= [0.7]) <:> ("γ" ::= [0.009]) <:> ("ρ" ::= [0.3]) <:> ("𝜉" ::= []) <:> ENil

examplePopl : Record [("s", Nat), ("i", Nat), ("r", Nat)]
examplePopl = Cons "s" 762 $ Cons "i" 1 $ Cons "r" 0 $ Empty

getSIRs :  Elem ("s", Nat) popl => Elem ("i", Nat) popl => Elem ("r", Nat) popl => Record popl -> (Nat, Nat, Nat)
getSIRs popl = (lookup "s" popl, lookup "i" popl, lookup "r" popl)

||| Simulating the SIR model, via effect handlers
simSIR : (n_days : Nat) -> IO (List (Nat, Nat, Nat), List Nat)
simSIR n_days = do
  let sim_env_in = envExampleSim
  (popls, env_out) <- runSampler (simulate envExampleSim (sirModel n_days examplePopl) )

  let sirs : List (Nat, Nat, Nat)
      sirs = let (sir_final ::: rest) = map getSIRs popls
             in (take (minus n_days 1) (sir_final :: rest))
    
      reported : List Nat 
      reported = Env.get "𝜉" env_out

  pure (sirs, reported)