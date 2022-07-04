module Main

import ProbFX.Examples.LinRegr
import System.File.ReadWrite

printThenWrite :  Show a => a -> IO (Either FileError ())
printThenWrite x = print (show x) >> writeFile "model-output.txt" (show x)

parseArgs : String -> IO (Either FileError ())
parseArgs cmd = case cmd of
  "simLinRegrMB"  => LinRegr.simLinRegrMB 50 >>= printThenWrite

  _               => putStrLn ("unrecognised command: " ++ cmd ++ "\n") >> pure (Right ())

main : String -> IO ()
main arg = do
  _ <- parseArgs arg
  pure ()