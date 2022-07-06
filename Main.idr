module Main

import ProbFX.Examples.LinRegr
import ProbFX.Examples.HMM
import ProbFX.Examples.LDA
import System
import System.File.ReadWrite

printThenWrite :  Show a => a -> IO (Either FileError ())
printThenWrite x = putStrLn (show x) >> writeFile "model-output.txt" (show x)

parseArgs : String -> IO (Either FileError ())
parseArgs cmd = case cmd of
  -- | Examples for linear regression
  "simLinRegr"        => LinRegr.simLinRegr   50    >>= printThenWrite
  "simLinRegrMB"      => LinRegr.simLinRegrMB 50    >>= printThenWrite
  "mhLinRegrMB"       => LinRegr.mhLinRegrMB 5000 50  >>= printThenWrite
  "smcLinRegrMB"      => LinRegr.smcLinRegrMB 100 100 20  >>= printThenWrite
  "rmsmcLinRegrMB"    => LinRegr.rmsmcLinRegrMB 100 100 10 20  >>= printThenWrite

  -- | Examples for hidden markov model
  "simHmm"          => HMM.simHmm   50    >>= printThenWrite
  "simHmmMB"        => HMM.simHmmMB 50    >>= printThenWrite
  "mhHmmMB"         => HMM.mhHmmMB 5000  50    >>= printThenWrite
  "smcHmmMB"        => HMM.smcHmmMB 100 100 50  >>= printThenWrite
  "rmsmcHmmMB"      => HMM.rmsmcHmmMB 100 100 10 50  >>= printThenWrite

  -- | Examples for hidden markov model
  "simLda"          => LDA.simLda 100   >>= printThenWrite
  "simLdaMB"        => LDA.simLdaMB 100   >>= printThenWrite
  "mhLdaMB"         => LDA.mhLdaMB 5000   >>= printThenWrite

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
