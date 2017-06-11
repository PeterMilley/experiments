{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
module Control.ReverseState
  ( RStateT(..)
  , rstate, rget, rput, rmodify
  , RState(..)
  , runRState
  , evalRState
  , execRState
  ) where

{-|
Module      : Control.ReverseState
Description : A reverse state monad.

This code is honestly entirely cribbed from the rev-state package on hackage,
but with names that don't collide with the actual State monad because
that's just confusing.

The reverse state monad is nearly identical to the State monad except the
state is propagated in the opposite direction to the non-state value. This
only works due to lazy evaluation.

'RState' is equivalent to the 'fix' function in utility: it can be implemented
in terms of 'fix', and 'fix' can be redefined in terms of 'RState':

@
    fix' f = evalRState (do { x <- rget; rput (f x); return x })
                        (error "unused")
@

Another example: here's a function which pads each element in a list of
strings with spaces on the left until they're all the same length, making only
one pass through the list. The max of the string lengths is computed in
the state variable via 'rmodify' and thus sent back to the beginning of the
computation, then 'rget' retrieves the result and sends it forward as the
first argument to the helper function @go@:

@
    pad :: [String] -> [String]
    pad l = evalRState (rget >>= \n -> mapM (go n) l) 0
      where
        go n s = let l = length s
                 in  replicate (n-l) ' ' ++ s <$ rmodify (max l)
@

-}

import Control.Arrow (first)
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Identity
import Control.Monad.Trans

-- | The reverse state monad `transformer`. Not really a monad transformer
--   as the result is only a monad if the inner monad @m@ is actually a
--   'MonadFix'.
newtype RStateT s m a =
  RStateT { -- | Run the underlying state computation.
            runRStateT :: s -> m (a, s)
          }

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

-- | Construct a monad from a pure state function.
rstate :: Applicative m => (s -> (a, s)) -> RStateT s m a
rstate f = RStateT (pure . f)

-- | Get the current state, which will be the result of the next _subsequent_
--   'rput' or 'rmodify'. Essentially, get the state from the future.
rget :: Applicative m => RStateT s m s
rget = rstate (\s -> (s, s))

-- | Update the current state, sending the new value backwards.
rput :: Applicative m => s -> RStateT s m ()
rput s = rstate (\_ -> ((), s))

-- | Modify the current state, sending the new value backwards.
rmodify :: Applicative m => (s -> s) -> RStateT s m ()
rmodify f = rstate (\s -> ((), f s))

-- | A reverse state monad without an inner monad.
type RState s = RStateT s Identity

-- | Run the underlying state computation.
runRState :: RState s a -> s -> (a, s)
runRState m s = runIdentity $ runRStateT m s

-- | Run the state computation, keeping only the final value.
evalRState :: RState s a -> s -> a
evalRState m s = fst $ runRState m s

-- | Run the state computation, keeping only the final state.
execRState :: RState s a -> s -> s
execRState m s = snd $ runRState m s
