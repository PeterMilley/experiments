{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
module ReverseState where

import Control.Arrow (first)
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Identity
import Control.Monad.Trans

newtype RStateT s m a = RStateT { runRStateT :: s -> m (a, s) }

instance Functor m => Functor (RStateT s m) where
  fmap f m = RStateT (\s -> first f <$> runRStateT m s)

instance MonadFix m => Monad (RStateT s m) where
  return x = RStateT (\s -> return (x, s))
  m >>= f  = RStateT (\s -> do
                         rec
                           (x, s'') <- runRStateT m s'
                           (x', s') <- runRStateT (f x) s
                         return (x', s''))

instance MonadFix m => Applicative (RStateT s m) where
  pure  = return
  (<*>) = ap

instance MonadFix m => MonadFix (RStateT s m) where
  mfix f = RStateT (\s -> mfix (\ ~(a, _) -> runRStateT (f a) s))

instance MonadTrans (RStateT s) where
  lift m = RStateT (\s -> fmap (,s) m)

rstate :: Applicative m => (s -> (a, s)) -> RStateT s m a
rstate f = RStateT (pure . f)

rget :: Applicative m => RStateT s m s
rget = rstate (\s -> (s, s))

rput :: Applicative m => s -> RStateT s m ()
rput s = rstate (\_ -> ((), s))

rmodify :: Applicative m => (s -> s) -> RStateT s m ()
rmodify f = rstate (\s -> ((), f s))

type RState s = RStateT s Identity

runRState :: RState s a -> s -> (a, s)
runRState m s = runIdentity $ runRStateT m s

evalRState :: RState s a -> s -> a
evalRState m s = fst $ runRState m s

execRState :: RState s a -> s -> s
execRState m s = snd $ runRState m s
