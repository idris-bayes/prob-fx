module ProbFX.Examples.LDA

import ProbFX.Model as PFX
import ProbFX.Sampler
import ProbFX.Inference.SIM
import ProbFX.Inference.MBAYES
import ProbFX.Util
import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Control.Monad.Bayes.Traced.Static
import Control.Monad.Bayes.Inference.SMC
import Control.Monad.Bayes.Inference.RMSMC
import Control.Monad.Bayes.Weighted
import public Data.Vect

||| LDA environment
LDAEnv : Nat -> Nat -> List (String, Type)
LDAEnv n_topics vocab_size =
  [("θ", Vect n_topics   Double),  -- topic distribution
   ("φ", Vect vocab_size Double),  -- word distribution
   ("w", String)                   -- observed words
  ]

||| Prior distribution over topics in a document
docTopicPrior :
    (n_topics_pred : Nat)
  -> Observable env "θ" (Vect (S n_topics_pred) Double)
  => Model env es (Vect (S n_topics_pred) Double)
docTopicPrior n_topics_pred =
  PFX.dirichlet (replicate (S n_topics_pred) 1) "θ"

||| Prior distribution over words in a topic
topicWordPrior :
     {vocab_size_pred : Nat}
  -> (vocab : Vect (S vocab_size_pred) String)
  -> Observable env "φ" (Vect (S vocab_size_pred) Double)
  => Model env es (Vect (S vocab_size_pred) Double)
topicWordPrior vocab =
  PFX.dirichlet (replicate (S vocab_size_pred) 1) "φ"

||| Distribution over likely words
wordDist :
     {vocab_size_pred : Nat}
  -> (vocab    : Vect (S vocab_size_pred) String)
  -> (vocab_ps : Vect (S vocab_size_pred) Double)
  -> Observable env "w" String
  => Model env es String
wordDist vocab ps =
  PFX.discrete (zip vocab ps) "w"

||| Distribution over the topics in a document, over the distribution of words in a topic
topicModel :
     {vocab_size_pred : Nat}
  -> (vocab    : Vect (S vocab_size_pred) String)
  -> (n_topics_pred : Nat)
  -> (doc_size : Nat)
  -> (Observable env "φ" (Vect (S vocab_size_pred) Double),
      Observable env "θ" (Vect (S n_topics_pred) Double),
      Observable env "w" String)
  => Model env es (Vect doc_size String)
topicModel vocab n_topics_pred doc_size = do
  -- Generate distribution over words for each topic
  topic_word_ps <- replicateM (S n_topics_pred) (topicWordPrior vocab)
  -- Generate distribution over topics for a given document
  doc_topic_ps  <- docTopicPrior n_topics_pred
  -- Use the above distributions to generate words for a document
  words         <- replicateM doc_size (do z <- categorical' doc_topic_ps
                                           let word_ps = index z topic_word_ps
                                           wordDist vocab word_ps)
  pure words


||| Example vocabulary of four words
exampleVocab : Vect 4 String
exampleVocab = ["DNA", "evolution", "parsing", "phonology"]

||| Assume two topics
n_topics_pred : Nat
n_topics_pred = pred 2

||| Environments for simulation and inference that assume two topics and a vocabulary of four words
envExampleSim : Env (LDAEnv 2 4)
envExampleSim = ("θ" ::= [[0.5, 0.5]])
            <:> ("φ" ::= [[0.12491280814569208,1.9941599739151505e-2,0.5385152817942926,0.3166303103208638],
                         [1.72605174564027e-2,2.9475900240868515e-2,9.906011619752661e-2,0.8542034661052021]] )
            <:> ("w" ::= [])
            <:> ENil

envExampleInf : List String -> Env (LDAEnv 2 4)
envExampleInf ws =  ("θ" ::= [])
                <:> ("φ" ::= [])
                <:> ("w" ::= ws)
                <:> ENil

exampleDocument : List String
exampleDocument = ["DNA","evolution","DNA","evolution","DNA","evolution","DNA","evolution","DNA","evolution", "parsing", "phonology", "DNA","evolution", "DNA", "parsing", "evolution","phonology", "evolution", "DNA","DNA","evolution","DNA","evolution","DNA","evolution","DNA","evolution","DNA","evolution", "parsing", "phonology", "DNA","evolution", "DNA", "parsing", "evolution","phonology", "evolution", "DNA","DNA","evolution","DNA","evolution","DNA","evolution","DNA","evolution","DNA","evolution", "parsing", "phonology", "DNA","evolution", "DNA", "parsing", "evolution","phonology", "evolution", "DNA","DNA","evolution","DNA","evolution","DNA","evolution","DNA","evolution","DNA","evolution", "parsing", "phonology", "DNA","evolution", "DNA", "parsing", "evolution","phonology", "evolution", "DNA","DNA","evolution","DNA","evolution","DNA","evolution","DNA","evolution","DNA","evolution", "parsing", "phonology", "DNA","evolution", "DNA", "parsing", "evolution","phonology", "evolution", "DNA"]

||| Simulate from LDA, using effect handlers
export
simLDA : (doc_size : Nat) -> IO (Vect doc_size String)
simLDA doc_size = do
  (ys, env_out) <- runSampler (simulate envExampleSim (topicModel exampleVocab n_topics_pred doc_size) )
  pure ys

||| Simulate from LDA, using monad bayes
export
simLDAMB : (doc_size : Nat) -> IO (Vect doc_size String)
simLDAMB doc_size = do
  let ldaMB = toMBayes envExampleSim (topicModel exampleVocab n_topics_pred doc_size)
  (ys, env_out) <- sampleIO $ prior ldaMB
  pure ys

||| MH inference on LDA, using monad bayes
export
mhLDAMB : (n_mhsteps : Nat)
       -- | Number of most recent MH trace values to consider, where trace_prefix_length <= n_mhsteps
       -> (trace_prefix_length : Nat)
       -> IO (List (Vect 2 Double), List (Vect 2 (Vect 4 Double)))
mhLDAMB n_mhsteps trace_prefix_length = do
  let ldaMB = toMBayes (envExampleInf exampleDocument) (topicModel exampleVocab n_topics_pred (length exampleDocument))

  output <- sampleIO $ prior $ mh n_mhsteps ldaMB
  let env_outs : List (Env (LDAEnv 2 4)) = take trace_prefix_length (map snd (toList output))
      -- | Get trace of document-topic distributions, where each trace value is of the form:
      --   [prob of topic_1, prob of topic_2]
      doc_topic_ps  : List (Vect 2 Double)
            = gets "θ" env_outs
      -- | Get trace of topic-word distributions, where each trace value is reified into the form:
      --   [word dist for topic 1, word dist for topic 2]
      topic_word_ps : Maybe (List (Vect 2 (Vect 4 Double)))
            = mapM (\env_out => toVect 2 $ Env.get "φ" env_out) env_outs
  pure (doc_topic_ps, case topic_word_ps of Just xs => xs
                                            Nothing => assert_total $ idris_crash "failed to convert 'topic_word_ps : List (List (Vect 4 Double))' into 'List (Vect 2 (Vect 4 Double))' form")

||| RMSMC inference on LDA, using monad bayes
export
rmsmcLDAMB : (n_timesteps : Nat) -> (n_particles : Nat) -> (n_mhsteps : Nat) -> IO (List (Vect 2 Double), List (Vect 2 (Vect 4 Double)))
rmsmcLDAMB n_timesteps n_particles n_mhsteps = do
  let ldaMB = toMBayes (envExampleInf exampleDocument) (topicModel exampleVocab n_topics_pred (length exampleDocument))

  output <- sampleIO $ runPopulation $ rmsmc n_timesteps n_particles n_mhsteps ldaMB

  let env_outs : List (Env (LDAEnv 2 4)) = map (snd . snd) (toList output)
      doc_topic_ps  : List (Vect 2 Double)
          = gets "θ" env_outs
      topic_word_ps : Maybe (List (Vect 2 (Vect 4 Double)))
          = mapM (\env_out => toVect 2 $ Env.get "φ" env_out) env_outs
  pure (doc_topic_ps, case topic_word_ps of Just xs => xs
                                            Nothing => assert_total $ idris_crash "failed to convert 'topic_word_ps : List (List (Vect 4 Double))' into 'List (Vect 2 (Vect 4 Double))' form")