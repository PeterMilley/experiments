{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Control.Iterator
  ( Yieldable(..)
  , YieldT(..)
  , Yield(..)
  , IteratorT(..)
  , Iterator(..)
  , toYield
  , toIterator
  , stepM
  , step
  , runIteratorM
  , runIterator
  ) where

{-|
Module      : Control.Iterator
Description : Co-operative asymmetric co-routines.

This is a co-routine implementation based on Edward Kmett's "Yield Monads for
Less" series of blog posts, specifically the third. 'YieldT' and 'IteratorT'
are both free monad transformers which extend their inner monad with the
'yield' method:
@
    yield :: o -> m i
@
which suspends computation, yielding a value of type @o@ to the controlling
function and waiting to be resumed with a value of type @i@.

The two monads differ in how the controlling function drives the co-routine.
'YieldT' admits 'stepM' which performs a single step of the computation,
stopping at the first 'yield' or when the co-routine completes. 'IteratorT'
admits 'runIteratorM' which runs the co-routine to completion given suitable
continuations. The two types of co-routine can be converted back and forth.

If you read the aforementioned blog posts, you'll note that nested 'YieldT'
co-routines may be inefficient to construct (in pretty much the same way that
repeatedly appending to the right of a list is inefficient). If this is a
concern, construct your co-routines as 'IteratorT' and then convert to
'YieldT' before first use.
-}

import Control.Monad (ap)
import Control.Monad.Identity
import Control.Monad.Trans.Class (MonadTrans(..))

-- | A typeclass for functors which can suspend computation, yielding a value
--   of type @o@, and wait to be resumed with a value of type @i@. Both
--   @YieldT i o m@ and @IteratorT i o m@ are instances.
class Functor y => Yieldable y i o | y -> i o where
   yield :: o -> y i

-- | A monad transformer which makes its inner monad 'Yieldable'.
data YieldF i o a b = Pure a | Yield (i -> b) o
newtype YieldT i o m a = YieldT { runYieldT :: m (YieldF i o a (YieldT i o m a)) }
type Yield i o = YieldT i o Identity

instance Monad m => Functor (YieldT i o m) where
  fmap f (YieldT m) = YieldT (liftM f' m) where
    f' (Pure a)     = Pure (f a)
    f' (Yield ki o) = Yield ((fmap f) . ki) o

instance Monad m => Yieldable (YieldT i o m) i o where
  yield = YieldT . return . Yield return

instance Monad m => Applicative (YieldT i o m) where
  pure a = YieldT (return (Pure a))
  (<*>) = ap

instance Monad m => Monad (YieldT i o m) where
  return = pure
  YieldT m >>= f = YieldT $ m >>= \v -> case v of
    Pure a     -> runYieldT (f a)
    Yield ki o -> return (Yield ((>>= f) . ki) o)

instance MonadTrans (YieldT i o) where
  lift = YieldT . fmap Pure

-- | Perform a single step of a 'YieldT', returning 'Either' the final
--   value of the computation, or an intermediate value and a continuation
--   to resume the computation.
stepM :: Monad m => YieldT i o m a -> m (Either a (o, i -> YieldT i o m a))
stepM y = do
  x <- runYieldT y
  case x of
    Pure a     -> return $ Left a
    Yield ki o -> return $ Right (o, ki)

step :: Yield i o a -> Either a (o, i -> Yield i o a)
step = runIdentity . stepM

-- | Another monad transformer which makes its inner monad 'Yieldable',
--   but using Church-encoded free monads (i.e. continuations, lots of
--   continuations).
newtype IteratorT i o m a =
  IteratorT { runIteratorT
              :: forall r. (a -> m r)
              -> (o -> (i -> m r) -> m r)
              -> m r }
type Iterator i o = IteratorT i o Identity

instance Functor (IteratorT i o m) where
  fmap f (IteratorT k) = IteratorT $ \a fr -> k (a . f) fr

instance Monad m => Yieldable (IteratorT i o m) i o where
  yield o = IteratorT (\kp kf -> kf o kp)

instance Applicative (IteratorT i o m) where
  pure a = IteratorT $ \k _ -> k a
  IteratorT fk <*> IteratorT ak = IteratorT $ \b fr -> fk (\e -> ak (\d -> b (e d)) fr) fr

instance Monad (IteratorT i o m) where
  return = pure
  IteratorT fk >>= f = IteratorT $ \b fr -> fk (\d -> runIteratorT (f d) b fr) fr

instance MonadTrans (YieldT i o) where
  lift m = IteratorT $ \k _ -> m >>= k

-- | Run an 'IteratorT' to completion by giving it two continuations, one
--   for what to do with the final value and one for what to do with both
--   an intermediate value and a `resume` continuation.
runIteratorM :: Monad m => IteratorT i o m a
             -> (a -> m r) -> (o -> (i -> m r) -> m r) -> m r
runIteratorM = runIteratorT

runIterator :: Iterator i o a -> (a -> r) -> (o -> (i -> r) -> r) -> r
runIterator (IteratorT m) =
  \ka kf -> runIdentity $ m (return . ka)
                            (\o ki -> return $ kf o (runIdentity . ki))

-- | Convert a 'YieldT' to an 'IteratorT'.
toIterator :: Monad m => YieldT i o m a -> IteratorT i o m a
toIterator (YieldT f) = IteratorT $ \ka kfr -> do
  freef <- f
  case freef of
    Pure a     -> ka a
    Yield ki o -> kfr o (\i -> runIteratorT (toIterator $ ki i) ka kfr)

-- | Convert an 'IteratorT' to a 'YieldT'.
toYield :: Monad m => IteratorT i o m a -> YieldT i o m a
toYield (IteratorT k) = YieldT $ k (return . Pure)
                                   (\o ki -> return $ Yield (YieldT . ki) o)
