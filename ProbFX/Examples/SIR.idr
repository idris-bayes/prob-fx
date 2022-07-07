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

envExampleInf : List Nat -> Env SIREnv
envExampleInf reported = ("β" ::= []) <:> ("γ" ::= []) <:> ("ρ" ::= []) <:> ("𝜉" ::= reported) <:> ENil

examplePopl : Record [("s", Nat), ("i", Nat), ("r", Nat)]
examplePopl = Cons "s" 762 $ Cons "i" 1 $ Cons "r" 0 $ Empty

exampleReported : List Nat
exampleReported = [0,1,4,2,1,3,3,5,10,11,30,23,48,50,91,94,129,151,172,173,198,193,214,179,229,172,205,211,191,212,185,184,173,211,185,197,176,169,198,174,163,197,152,198,153,164,154,167,178,174,160,149,140,172,169,144,137,151,166,151,147,149,159,150,151,139,137,182,121,119,133,146,141,136,126,131,124,110,120,113,117,102,120,117,122,121,110,125,127,117,117,98,109,108,108,120,98,103,104,103]

getSIRs :  Elem ("s", Nat) popl => Elem ("i", Nat) popl => Elem ("r", Nat) popl => Record popl -> (Nat, Nat, Nat)
getSIRs popl = (lookup "s" popl, lookup "i" popl, lookup "r" popl)

||| Simulating the SIR model, via effect handlers
export
simSIR : (n_days : Nat) -> IO (List (Nat, Nat, Nat), List Nat)
simSIR n_days = do
  (popls, env_out) <- runSampler (simulate envExampleSim (sirModel n_days examplePopl) )

  let sirs : List (Nat, Nat, Nat)
      sirs = let (sir_final ::: rest) = map getSIRs popls
             in  take n_days (sir_final :: rest)
    
      reported : List Nat 
      reported = Env.get "𝜉" env_out

  pure (reverse sirs, reverse reported)

||| Simulating the SIR model, via monad bayes
export
simSIRMB : (n_days : Nat) -> IO (List (Nat, Nat, Nat), List Nat)
simSIRMB n_days = do
  let sirModelMB = toMBayes envExampleSim (sirModel n_days examplePopl)

  (popls, env_out) <- sampleIO $ prior sirModelMB

  let sirs : List (Nat, Nat, Nat)
      sirs = let (sir_final ::: rest) = map getSIRs popls
             in  take n_days (sir_final :: rest)
    
      reported : List Nat 
      reported = Env.get "𝜉" env_out

  pure (reverse sirs, reverse reported)

||| MH inference on the SIR model, via monad bayes
export
mhSIRMB : (n_mhsteps : Nat) -> (n_days : Nat) -> IO (List Double, List Double, List Double)
mhSIRMB n_mhsteps n_days = do
  let sirModelMB = toMBayes (envExampleInf exampleReported) (sirModel n_days examplePopl)
  -- print "here"

  output <- sampleIO $ prior $ mh n_mhsteps sirModelMB
  -- print "here"
  let env_outs : List (Env SIREnv) = map snd (toList output)
    
      betas   : List Double       = gets "β" env_outs
      gammas  : List Double       = gets "γ" env_outs
      rhos    : List Double       = gets "ρ" env_outs

  pure (betas, gammas, rhos)