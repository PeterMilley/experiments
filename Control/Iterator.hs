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

import Control.Monad.Identity
import Control.Monad.Trans.Free
import Control.Monad.Trans.Free.Church

data Store i o r = Store (i -> r) o
    deriving (Functor)

class Functor y => Yieldable y i o | y -> i o where
   yield :: o -> y i

instance Yieldable (Store i o) i o where
  yield = Store id

type YieldT i o m = FreeT (Store i o) m
type Yield i o = YieldT i o Identity

instance (Yieldable y i o, Monad m) => Yieldable (FreeT y m) i o where
  yield = liftF . yield

type IteratorT i o m = FT (Store i o) m
type Iterator i o = IteratorT i o Identity

instance (Yieldable y i o, Monad m) => Yieldable (FT y m) i o where
  yield = liftF . yield

toYield :: Monad m => IteratorT i o m a -> YieldT i o m a
toYield = fromFT

toIterator :: Monad m => YieldT i o m a -> IteratorT i o m a
toIterator = toFT

stepM :: Monad m => YieldT i o m a -> m (Either a (o, i -> YieldT i o m a))
stepM y = do
  x <- runFreeT y
  case x of
    Pure a            -> return $ Left a
    Free (Store ki o) -> return $ Right (o, ki)

step :: Yield i o a -> Either a (o, i -> Yield i o a)
step = runIdentity . stepM

runIteratorM :: Monad m => IteratorT i o m a
             -> (a -> m r) -> (o -> (i -> m r) -> m r) -> m r
runIteratorM (FT m) =
  \ka kf -> m ka (\xg -> (\ (Store ki o) -> kf o ki) . (fmap xg))

runIterator :: Iterator i o a -> (a -> r) -> (o -> (i -> r) -> r) -> r
runIterator (FT m) =
  \ka kf -> runIdentity $ m (return . ka) (\xg -> return . (\ (Store ki o) -> kf o (runIdentity . ki)) . (fmap xg))
