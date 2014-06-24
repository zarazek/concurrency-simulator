{-# LANGUAGE ExistentialQuantification, TypeFamilies, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

import Prelude hiding (log, lookup, null)
import Control.Monad.Trans.Free
import Control.Monad (when, forever, replicateM, forM_, liftM)
import Control.Monad.IO.Class
import System.Random
import Control.Concurrent (forkIO, myThreadId, threadDelay)
import Control.Concurrent.MVar
import Data.Typeable
import Control.Monad.Trans.Cont
import Data.Sequence (singleton, viewl, ViewL(..), (<|), (|>))
import Data.IORef
import qualified Data.Map.Strict as M
import Control.Monad.Trans.Class
import qualified Control.Monad.State as S
import qualified Control.Monad.Writer as W
import Data.Functor.Identity (Identity, runIdentity)
import Data.Dynamic
import Data.List (intercalate, find)


data ThreadF var next = forall a. Typeable a => CreateEmptyVar (var a -> next)
                      | forall a. Typeable a => CreateFullVar a (var a -> next)
                      | forall a. Typeable a => Get (var a) (a -> next)
                      | forall a. Typeable a => Set (var a) a next
                      | Yield next
                      | Log String next
                      | Fork next next
                      | End

instance Functor (ThreadF var) where
  fmap f (CreateEmptyVar cont) = CreateEmptyVar (f . cont)
  fmap f (CreateFullVar val cont)  = CreateFullVar val (f . cont)
  fmap f (Get var cont) = Get var (f . cont)
  fmap f (Set var val cont) = Set var val (f cont)
  fmap f (Yield cont) = Yield (f cont)
  fmap f (Log str cont) = Log str (f cont)
  fmap f (Fork cont1 cont2) = Fork (f cont1) (f cont2)
  fmap f End = End 

type Thread m var = FreeT (ThreadF var) m

createEmptyVar :: (Monad m, Typeable a) => Thread m var (var a)
createEmptyVar = liftF (CreateEmptyVar id)

createFullVar :: (Monad m, Typeable a) => a -> Thread m var (var a)
createFullVar val = liftF (CreateFullVar val id)

get :: (Monad m, Typeable a) => var a -> Thread m var a
get var = liftF (Get var id)

set :: (Monad m, Typeable a) => var a -> a -> Thread m var ()
set var val = liftF (Set var val ())

yield :: Monad m => Thread m var ()
yield = liftF (Yield ())

log :: Monad m => String -> Thread m var ()
log str = liftF (Log str ())

end :: (Monad m, Typeable a) => Thread m var a
end = liftF End

cFork :: Monad m => Thread m var Bool
cFork = liftF (Fork False True)

fork :: (Monad m, Typeable a) => Thread m var a -> Thread m var ()
fork thread = do
  child <- cFork
  when child $ do
    thread
    end

swap :: (Monad m, Typeable a) => var a -> var a -> Thread m var ()
swap var1 var2 = do
  val1 <- get var1
  val2 <- get var2
  set var1 val2
  set var2 val1

prog :: Monad m => Thread m var ((Int, Int), (String, String))
prog = do
  intVar1 <- createFullVar 1
  intVar2 <- createFullVar 2
  strVar1 <- createFullVar "bejbe"
  strVar2 <- createFullVar "szpadel"
  swap intVar1 intVar2
  fork $ swap intVar1 intVar2
  swap strVar1 strVar2
  fork $ swap strVar1 strVar2
  intVal1 <- get intVar1
  intVal2 <- get intVar2
  strVal1 <- get strVar1
  strVal2 <- get strVar2
  return ((intVal1, intVal2), (strVal1, strVal2))

sleep :: MonadIO m => m ()
sleep = liftIO $ randomRIO (0, 300000) >>= threadDelay
  
phil :: Monad m => Int -> var () -> var () -> Thread m var ()
phil n leftFork rightFork = forever $ do
    log $ show n ++ " is awaiting"
    yield
    get leftFork
    log $ show n ++ " took left fork"
    yield
    get rightFork
    log $ show n ++ " took right fork"
    yield
    set leftFork ()
    set rightFork ()
    log $ show n ++ " put forks"
    yield
    
runPhil :: Monad m => Int -> Thread m var ()
runPhil n = do
    forks <- replicateM n $ createFullVar ()
    forM_ [1..n] $ \i -> fork $ phil i (forks !! (i - 1)) (forks !! (i `mod` n))

atomicPrint :: MVar () -> String -> IO ()
atomicPrint var str = do
  takeMVar var
  putStrLn str
  putMVar var ()
  
runIO :: Thread IO MVar a -> IO ()
runIO action = do
  printLock <- newMVar ()
  runIO' printLock action
  where runIO' printLock action = do
          inst <- runFreeT action
          case inst of
            Free (CreateEmptyVar cont) -> do
              var <- newEmptyMVar
              recurse (cont var)
            Free (CreateFullVar val cont) -> do
              var <- newMVar val
              recurse (cont var)
            Free (Get var cont) -> do
              val <- takeMVar var
              recurse (cont val)
            Free (Set var val cont) -> do
              putMVar var val
              recurse cont
            Free (Yield cont) -> do
              sleep
              recurse cont
            Free (Log str cont) -> do
              ap str
              recurse cont
            Free (Fork cont1 cont2) -> do
              forkIO $ recurse cont2
              recurse cont1
            Free End -> return ()
            Pure _ -> return ()
          where ap = atomicPrint printLock
                recurse = runIO' printLock

showType :: Typeable a => a -> String
showType = show . typeOf

showArgType :: Typeable a => a -> String
showArgType = show . head . typeRepArgs . typeOf

verboseRunIO :: Thread IO MVar a -> IO ()
verboseRunIO action = do
  printLock <- newMVar ()
  verboseRunIO' printLock action
  where verboseRunIO' printLock action = do
          instr <- runFreeT action
          case instr of
            Free (CreateEmptyVar cont) -> do
              var <- newEmptyMVar
              ap ("new empty " ++ showArgType var ++ " var")
              recurse (cont var)
            Free (CreateFullVar val cont) -> do
              var <- newMVar val
              ap ("new full " ++ showArgType var ++ " var")
              recurse (cont var)
            Free (Get var cont) -> do
              val <- takeMVar var
              ap ("taken " ++ showType val ++ " val")
              recurse (cont val)
            Free (Set var val cont) -> do
              putMVar var val
              ap ("put " ++ showType val ++ " val")
              recurse cont
            Free (Yield cont) -> do
              sleep
              recurse cont
            Free (Log str cont) -> do
              ap str
              recurse cont
            Free (Fork cont1 cont2) -> do
              newThreadId <- forkIO $ recurse cont2
              ap ("fork: " ++ show newThreadId)
              recurse cont1
            Free End -> ap "end"
            Pure _ -> ap "return"
          where ap str = do
                  threadId <- myThreadId
                  atomicPrint printLock (show threadId ++ ": " ++ str)
                recurse = verboseRunIO' printLock

class Monad m => MonadSharedState m where
  type SVar m :: * -> *
  newEmptySVar :: Typeable a => m (SVar m a)
  newFullSVar :: Typeable a => a -> m (SVar m a)
  readSVar :: Typeable a => SVar m a -> m (Maybe a)
  writeSVar :: Typeable a => SVar m a -> Maybe a -> m ()
  putLog :: String -> m ()

newtype MaybeRef a = MaybeRef (IORef (Maybe a))

instance MonadSharedState IO where
  type SVar IO = MaybeRef
  newEmptySVar = fmap MaybeRef (newIORef Nothing)
  newFullSVar val = fmap MaybeRef (newIORef (Just val))
  readSVar (MaybeRef var) = readIORef var
  writeSVar (MaybeRef var) val  = writeIORef var val
  putLog = putStrLn

newtype Var a =  Var Int
type BindingsMap = M.Map Int (Maybe Dynamic)
data Bindings = Bindings BindingsMap Int

emptyBindings :: Bindings
emptyBindings = Bindings M.empty 0

getValue :: Typeable a => BindingsMap -> Int -> Maybe a
getValue binds var = case M.lookup var binds of
  Nothing -> error "read of unbound variable"
  Just maybeDyn -> case maybeDyn of
                     Nothing -> Nothing
                     Just dyn -> case fromDynamic dyn of
                                   Nothing -> error "read of variable of invalid type"
                                   Just val -> Just val

setValue :: Typeable a => BindingsMap -> Int -> Maybe a -> BindingsMap
setValue binds var new = case M.lookup var binds of
  Nothing -> error "write of unbound variable"
  Just old -> case (old, new) of
                     (Nothing, Nothing) -> error "clear of empty variable"
                     (Nothing, Just val) -> M.adjust (\_ -> Just (toDyn val)) var binds
                     (Just _, Nothing) -> M.adjust (\_ -> Nothing) var binds
                     (Just _, Just _) -> error "set of set variable"

-- type PureMonadTransformer m = S.StateT Bindings (W.WriterT [String] m)
type PureMonadTransformer m = W.WriterT [String] (S.StateT Bindings m)
type PureMonad = PureMonadTransformer Identity
type PureThread = Thread PureMonad (SVar PureMonad)

runPureMonadT :: Monad m => PureMonadTransformer m a -> m (a, [String])
-- runPureMonadT act = W.runWriterT (S.evalStateT act emptyBindings)
runPureMonadT act = S.evalStateT (W.runWriterT act) emptyBindings

runPureMonad :: PureMonad a -> (a, [String])
runPureMonad = runIdentity . runPureMonadT

instance Monad m => MonadSharedState (PureMonadTransformer m) where
  type SVar (PureMonadTransformer m) = Var
  newEmptySVar = S.get >>= \(Bindings map next) -> do
    S.put (Bindings (M.insert next Nothing map) (next + 1))
    return (Var next)
  newFullSVar val = S.get >>= \(Bindings map next) -> do
    S.put (Bindings (M.insert next (Just (toDyn val)) map) (next + 1))
    return (Var next)
  readSVar (Var var) = S.gets (\(Bindings map _) -> getValue map var)
  writeSVar (Var var) val = S.modify (\(Bindings map next) -> Bindings (setValue map var val) next)
  putLog str = W.tell [str]

roundRobin :: MonadSharedState m => Thread m (SVar m) a -> m ()
roundRobin t = go (singleton t)
  where go ts = case viewl ts of
          EmptyL -> return ()
          t :< ts' -> do
            x <- runFreeT t
            case x of
              Free (CreateEmptyVar cont) -> do
                var <- newEmptySVar
                go (cont var <| ts')
              Free (CreateFullVar val cont) -> do
                var <- newFullSVar val
                go (cont var <| ts')
              Free (Get var cont) -> do
                may <- readSVar var
                case may of
                  Nothing -> go (ts' |> (get var >>= cont))
                  Just val -> do 
                    writeSVar var Nothing
                    go (cont val <| ts')
              Free (Set var val cont) -> do
                may <- readSVar var
                case may of
                  Nothing -> do
                    writeSVar var (Just val)
                    go (cont <| ts')
                  Just _ -> go (ts |> (set var val >> cont))
              Free (Yield cont) -> go (ts' |> cont)
              Free (Log str cont) -> putLog str >> go (cont <| ts')
              Free (Fork cont1 cont2) -> go (cont1 <| ( ts' |> cont2))
              Free End -> go ts'
              Pure _ -> go ts'

data ErasedTypeThread m var = forall a. ErasedTypeThread (Thread m var a)

wrapThread t = ErasedTypeThread t

data ErasedTypeVar var = forall a. ErasedTypeVar (var a)

wrapVar v = ErasedTypeVar v

instance Eq (ErasedTypeVar Var) where
  (ErasedTypeVar (Var lhs)) == (ErasedTypeVar (Var rhs)) = lhs == rhs

instance Ord (ErasedTypeVar Var) where
  compare (ErasedTypeVar (Var lhs)) (ErasedTypeVar (Var rhs)) = compare lhs rhs

type ThreadList m var = [ErasedTypeThread m var]
type BlockedMap m var = M.Map (ErasedTypeVar var) (ThreadList m var)

addToMultimap :: Ord (ErasedTypeVar var) => BlockedMap m var-> var a -> Thread m var b -> BlockedMap m var
addToMultimap map var thr = M.alter f (wrapVar var) map
  where f Nothing = Just [wrapThread thr]
        f (Just thrs) = Just (wrapThread thr : thrs)

removeFromMultimap :: Ord (ErasedTypeVar var) => BlockedMap m var -> var a -> (BlockedMap m var, ThreadList m var)
removeFromMultimap map var = (newMap, thrs)
  where newMap = M.delete wrappedVar map
        thrs = case M.lookup wrappedVar map of
          Nothing -> []
          Just thrs -> thrs
        wrappedVar = wrapVar var
        
singleStep :: (MonadSharedState m, Ord (ErasedTypeVar (SVar m))) =>
              Thread m (SVar m) a ->
              ThreadList m (SVar m) ->
              BlockedMap m (SVar m) ->
              m (ThreadList m (SVar m), BlockedMap m (SVar m))
singleStep t active blocked = do
  x <- runFreeT t
  case x of
    Free (CreateEmptyVar cont) -> do
      var <- newEmptySVar
      -- return (wrapThread (cont var) : active, blocked)
      singleStep (cont var) active blocked
    Free (CreateFullVar val cont) -> do
      var <- newFullSVar val
      -- return (wrapThread (cont var) : active, blocked)
      singleStep (cont var) active blocked
    Free (Get var cont) -> do
      may <- readSVar var
      case may of
        Nothing -> return (active, addToMultimap blocked var (get var >>= cont))
        Just val -> do
          writeSVar var Nothing
          let (newBlocked, newActive) = removeFromMultimap blocked var
          return (wrapThread (cont val) : newActive ++ active, newBlocked)
    Free (Set var val cont) -> do
      may <- readSVar var
      case may of
        Nothing -> do
          writeSVar var (Just val)
          let (newBlocked, newActive) = removeFromMultimap blocked var
          return (wrapThread cont : newActive ++ active, newBlocked)
        Just val -> return (active, addToMultimap blocked var (set var val >> cont))
    Free (Yield cont) -> return (wrapThread cont : active, blocked)
    Free (Log str cont) -> do
      putLog str
      -- return (wrapThread cont : active, blocked)
      singleStep cont active blocked
    Free (Fork cont1 cont2) -> return (wrapThread cont1 : wrapThread cont2 : active, blocked)
    Free End -> return (active, blocked)
    Pure _ -> return (active, blocked)

data Stream a = Stream a (Stream a)

repeatS x = Stream x (repeatS x)

newtype Choice = Choice (Int -> Int)

type Interleaving = Stream Choice

choose n lst = (lst !! n, take n lst ++ drop (n+1) lst)

data RunResult = Deadlock | AllExit | LimitReached deriving (Eq, Show)

runWithInterleaving :: (MonadSharedState m, Ord (ErasedTypeVar (SVar m))) => Interleaving -> Int -> Thread m (SVar m) a -> m RunResult
runWithInterleaving fs maxSteps t = go fs maxSteps t [] M.empty
  where go :: (MonadSharedState m, Ord (ErasedTypeVar (SVar m))) =>
              Interleaving ->
              Int ->
              Thread m (SVar m) a ->
              ThreadList m (SVar m) ->
              BlockedMap m (SVar m) ->
              m RunResult
        go fs maxSteps t ready blocked = do
          case maxSteps of
            0 -> return LimitReached
            _ -> do
              (ready', blocked') <- singleStep t ready blocked
              case ready' of
                [] -> if M.null blocked' then return AllExit else return Deadlock
                _ -> do
                  let (Stream (Choice f) fs') = fs
                  let (wrappedChosen, rest) = choose (f (length ready')) ready'
                  case wrappedChosen of
                    ErasedTypeThread chosen -> go fs' (maxSteps-1) chosen rest blocked'

getResultAndLog :: PureThread a -> Interleaving -> Int -> (RunResult, [String])
getResultAndLog prog interleaving limit = runPureMonad $ 
                                          runWithInterleaving interleaving limit prog


printPhilResult f limit = do
  let (result, logs) = getResultAndLog (runPhil 5) (repeatS (Choice f)) limit
  putStrLn (intercalate "\n" logs)
  print result

choices lst = map (\n -> choose n lst) [0..length lst - 1]

allPermutations []  = [[]]
allPermutations lst = [x:ys | (x, xs) <- choices lst, ys <- allPermutations xs]
        
runAllInterleavings :: (MonadSharedState m, Ord (ErasedTypeVar (SVar m))) =>
                       Thread m (SVar m) a ->
                       Int ->
                       m [RunResult]
runAllInterleavings t maxSteps = go [wrapThread t] M.empty maxSteps
  where go :: (MonadSharedState m, Ord (ErasedTypeVar (SVar m))) =>
              ThreadList m (SVar m) ->
              BlockedMap m (SVar m) ->
              Int ->
              m [RunResult]
        go ready blocked maxSteps = do
          case maxSteps of
            0 -> return [LimitReached]
            _ -> case ready of
              [] -> if M.null blocked then return [AllExit] else return [Deadlock]
              _  -> liftM concat $ flip mapM (choices ready) $ \(wrappedChosen, rest) ->
                case wrappedChosen of
                  ErasedTypeThread chosen -> do
                    (ready', blocked') <- singleStep chosen rest blocked
                    go ready' blocked' (maxSteps-1)

doesntDeadlock :: PureThread a -> Int -> Bool
doesntDeadlock prog maxSteps = all (/= Deadlock) $ 
                               fst $
                               runPureMonad $
                               runAllInterleavings prog maxSteps

type M = PureMonadTransformer []
type T = Thread M (SVar M)
type TL = ThreadList M (SVar M)
type TM = BlockedMap M (SVar M)

allRuns :: T a -> Int -> [(RunResult, [String])]
allRuns t maxSteps = runPureMonadT $ go [wrapThread t] M.empty maxSteps
  where go :: TL -> TM -> Int -> M RunResult
        go ready blocked maxSteps = case maxSteps of
          0 -> return LimitReached
          _ -> case ready of
            [] -> if M.null blocked then return AllExit else return Deadlock
            _ -> do
              (wrapedChosen, rest) <- (lift . lift) (choices ready)
              case wrapedChosen of
                ErasedTypeThread chosen -> do
                  (ready', blocked') <- singleStep chosen rest blocked
                  go ready' blocked' (maxSteps-1)

findDeadlock :: T a -> Int -> Maybe [String]
findDeadlock t maxSteps = fmap snd $ find ((== Deadlock) . fst) $ allRuns t maxSteps 

main = do
  printPhilResult (\n -> max (n-2) 0) 1000
  putStrLn ""
  printPhilResult (\n -> max (n-1) 0) 1000
  print $ findDeadlock (runPhil 4) 20
