{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
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

This is a co-routine implementation based on Edward Kmett's "Free Monads for
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

import Control.Monad.Identity
import Control.Monad.Trans.Free
import Control.Monad.Trans.Free.Church

data Store i o r = Store (i -> r) o
    deriving (Functor)

-- | A typeclass for functors which can suspend computation, yielding a value
--   of type @o@, and wait to be resumed with a value of type @i@. Both
--   @YieldT i o m@ and @IteratorT i o m@ are instances.
class Functor y => Yieldable y i o | y -> i o where
   yield :: o -> y i

instance Yieldable (Store i o) i o where
  yield = Store id

-- | A monad transformer which makes its inner monad 'Yieldable'.
type YieldT i o m = FreeT (Store i o) m
type Yield i o = YieldT i o Identity

instance (Yieldable y i o, Monad m) => Yieldable (FreeT y m) i o where
  yield = liftF . yield

-- | Another monad transformer which makes its inner monad 'Yieldable',
--   but using Church-encoded free monads (i.e. continuations, lots of
--   continuations).
type IteratorT i o m = FT (Store i o) m
type Iterator i o = IteratorT i o Identity

instance (Yieldable y i o, Monad m) => Yieldable (FT y m) i o where
  yield = liftF . yield

-- | Convert an 'IteratorT' to a 'YieldT'.
toYield :: Monad m => IteratorT i o m a -> YieldT i o m a
toYield = fromFT

-- | Convert a 'YieldT' to an 'IteratorT'.
toIterator :: Monad m => YieldT i o m a -> IteratorT i o m a
toIterator = toFT

-- | Perform a single step of a 'YieldT', returning 'Either' the final
--   value of the computation, or an intermediate value and a continuation
--   to resume the computation.
stepM :: Monad m => YieldT i o m a -> m (Either a (o, i -> YieldT i o m a))
stepM y = do
  x <- runFreeT y
  case x of
    Pure a            -> return $ Left a
    Free (Store ki o) -> return $ Right (o, ki)

step :: Yield i o a -> Either a (o, i -> Yield i o a)
step = runIdentity . stepM

-- | Run an 'IteratorT' to completion by giving it two continuations, one
--   for what to do with the final value and one for what to do with both
--   an intermediate value and a `resume` continuation.
runIteratorM :: Monad m => IteratorT i o m a
             -> (a -> m r) -> (o -> (i -> m r) -> m r) -> m r
runIteratorM (FT m) =
  \ka kf -> m ka (\xg -> (\ (Store ki o) -> kf o ki) . (fmap xg))

runIterator :: Iterator i o a -> (a -> r) -> (o -> (i -> r) -> r) -> r
runIterator (FT m) =
  \ka kf -> runIdentity $ m (return . ka) (\xg -> return . (\ (Store ki o) -> kf o (runIdentity . ki)) . (fmap xg))
