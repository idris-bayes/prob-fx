module Main

import ProbFX.Examples.LinRegr
import ProbFX.Examples.HMM
import ProbFX.Examples.LDA
import ProbFX.Examples.SIR
import System
import System.File.ReadWrite

printThenWrite :  Show a => a -> IO (Either FileError ())
printThenWrite x = putStrLn (show x) >> writeFile "model-output.txt" (show x)

parseArgs : String -> IO (Either FileError ())
parseArgs cmd = case cmd of
  -- | Examples for linear regression
  "simLinRegr"        => LinRegr.simLinRegr   50    >>= printThenWrite
  "simLinRegrMB"      => LinRegr.simLinRegrMB 50    >>= printThenWrite
  "mhLinRegr"         => LinRegr.mhLinRegr 5000 50  >>= printThenWrite
  "mhLinRegrMB"       => LinRegr.mhLinRegrMB 5000 50  >>= printThenWrite
  "smcLinRegrMB"      => LinRegr.smcLinRegrMB 100 100 20  >>= printThenWrite
  "rmsmcLinRegrMB"    => LinRegr.rmsmcLinRegrMB 100 100 10 20  >>= printThenWrite

  -- | Examples for hidden markov model
  "simHMM"          => HMM.simHMM   50    >>= printThenWrite
  "simHMMMB"        => HMM.simHMMMB 50    >>= printThenWrite
  "mhHMMMB"         => HMM.mhHMMMB 5000  50    >>= printThenWrite
  "smcHMMMB"        => HMM.smcHMMMB 100 100 50  >>= printThenWrite
  "rmsmcHMMMB"      => HMM.rmsmcHMMMB 100 100 10 50  >>= printThenWrite

  -- | Examples for latent dirichlet allocation
  "simLDA"          => LDA.simLDA 100   >>= printThenWrite
  "simLDAMB"        => LDA.simLDAMB 100   >>= printThenWrite
  "mhLDAMB"         => LDA.mhLDAMB 5000 2000  >>= printThenWrite
  "rmsmcLDAMB"      => LDA.rmsmcLDAMB 100 50 20  >>= printThenWrite

  -- | Examples for SIR model
  "simSIR"          => SIR.simSIR 100       >>= printThenWrite
  "simSIRMB"        => SIR.simSIRMB 100     >>= printThenWrite
  "mhSIRMB"         => print ("NOTE: Using Monad Bayes inference (MH) for this particular case is *EXTREMELY* slow " ++
                             "for some reason, even in Haskell! (This isn't the case when using MH in ProbFX in Haskell).") >>=
                       \_ => SIR.mhSIRMB 2 100 >>= printThenWrite

  _                 => putStrLn ("unrecognised command: " ++ cmd ++ "\n") >> pure (Right ())

main : IO ()
main = do
  args <- getArgs
  case args of
               (_::a::as) => (parseArgs a) >>= \_ => pure ()
               _          => print "no arguments provided to ProbFX"
  pure ()

{-
    pack --with-ipkg prob-fx.ipkg repl Main.idr

    :exec parseArgs "<arg>"

    python3 graph.py "<arg>"
-}
