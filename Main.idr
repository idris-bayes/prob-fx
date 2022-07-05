module Main

import ProbFX.Examples.LinRegr
import System
import System.File.ReadWrite

printThenWrite :  Show a => a -> IO (Either FileError ())
printThenWrite x = print (show x) >> writeFile "model-output.txt" (show x)

parseArgs : String -> IO (Either FileError ())
parseArgs cmd = case cmd of
  "simLinRegr"        => LinRegr.simLinRegr   50    >>= printThenWrite
  "simLinRegrMB"      => LinRegr.simLinRegrMB 50    >>= printThenWrite
  "mhLinRegrMB"       => LinRegr.mhLinRegrMB 5000 50  >>= printThenWrite
  "smcLinRegrMB"      => LinRegr.smcLinRegrMB 100 100 20  >>= printThenWrite
  "rmsmcLinRegrMB"    => LinRegr.rmsmcLinRegrMB 100 100 10 20  >>= printThenWrite

  _               => putStrLn ("unrecognised command: " ++ cmd ++ "\n") >> pure (Right ())

main : IO ()
main = do
  args <- getArgs
  case args of []       => print "no arguments provided to ProbFX"
               (a::as)  => (parseArgs a) >>= \_ => pure ()
  pure ()

{-
    pack --with-ipkg prob-fx.ipkg repl Main.idr
    
    :exec parseArgs "<arg>"
    
    python3 graph.py "<arg>"
-}
