module ProbFX.Examples.LDA

import ProbFX.Model as PFX
import ProbFX.Sampler
import ProbFX.Inference.SIM
import ProbFX.Inference.MBAYES
import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Control.Monad.Bayes.Traced.Static
import Control.Monad.Bayes.Inference.SMC
import Control.Monad.Bayes.Inference.RMSMC
import Control.Monad.Bayes.Weighted


||| LDA environment
LDAEnv : Nat -> Nat -> List (String, Type)
LDAEnv n_topics vocab_size =  
  [("θ", Vect n_topics   Double),  -- topic distribution
   ("φ", Vect vocab_size Double),  -- word distribution
   ("w", String)                   -- observed words
  ]

||| Prior distribution over topics in a document
docTopicPrior : 
    (n_topics : Nat) 
  -> Observable env "θ" (Vect (S n_topics) Double)
  => Model env es (Vect (S n_topics) Double)
docTopicPrior n_topics = 
  PFX.dirichlet (replicate (S n_topics) 1) "θ"

||| Prior distribution over words in a topic
topicWordPrior : 
    {auto vocab_size : Nat} 
  -> Observable env "φ" (Vect (S vocab_size) Double)
  => Vect (S vocab_size) String 
  -> Model env es (Vect (S vocab_size) Double)
topicWordPrior {vocab_size} vocab = 
  PFX.dirichlet (replicate (S vocab_size) 1) "φ"

||| Distribution over likely words
wordDist : 
    {auto vocab_size : Nat} 
  -> Observable env "w" String 
  => Vect (S vocab_size) String 
  -> Vect (S vocab_size) Double 
  -> Model env es String
wordDist vocab ps =
  PFX.discrete (zip vocab ps) "w"