import Prelude hiding (log)
import Concurrency.Simulator (Thread, PureThread, createFullVar, get, set, log, fork,
                              runPureMonad, 
                              Stream(..), Interleaving, RunResult, runWithInterleaving,
                              findDeadlock)
import Control.Monad (forever, replicateM, forM_)
import Data.List (intercalate)

phil :: Monad m => Int -> var () -> var () -> Thread m var ()
phil n leftFork rightFork = forever $ do
    log $ show n ++ " is awaiting"
    get leftFork
    log $ show n ++ " took left fork"
    get rightFork
    log $ show n ++ " took right fork"
    set leftFork ()
    set rightFork ()
    log $ show n ++ " put forks"
    
runPhil :: Monad m => Int -> Thread m var ()
runPhil n = do
    forks <- replicateM n $ createFullVar ()
    forM_ [1..n] $ \i -> fork $ phil i (forks !! (i - 1)) (forks !! (i `mod` n))


getResultAndLog :: PureThread a -> Interleaving -> Int -> (RunResult, [String])
getResultAndLog prog interleaving limit = runPureMonad $ 
                                          runWithInterleaving interleaving limit prog

repeatS x = Stream x (repeatS x)

printPhilResult f limit = do
  let (result, logs) = getResultAndLog (runPhil 5) (repeatS f) limit
  putStrLn (intercalate "\n" logs)
  print result


main = do
  printPhilResult (\n -> max (n-2) 0) 1000
  putStrLn ""
  printPhilResult (\n -> max (n-1) 0) 1000
  print $ findDeadlock (runPhil 4) 20
