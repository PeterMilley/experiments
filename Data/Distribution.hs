{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Data.Distribution
  ( Distribution(..)
  , disjoint
  , independent
  , uniform
  , expectation
  , sample
  ) where

{-|
Module      : Data.Distribution
Description : A free monad to model random variables.

E.g.

>>> let coin = (disjoint 0.5 0 1) :: Distribution Float Int

>>> expectation (fromIntegral <$> (coin + coin + coin))
1.5

>>> fmap (fst . sample (independent $ replicate 10 coin)) getStdGen
[0,0,1,1,1,0,0,1,0,0]

-}

import Control.Monad (liftM2)
import Control.Monad.Free.Church
import Control.Monad.State
import Data.Functor ((<$>))
import System.Random

-- | @Distribution a o@ is a collection of type @o@ which can depend on random
--   variables of type @a@. Typically @a@ will be 'Float' or 'Double'.
--   'Distribution' is defined as a free monad (and hence is a monad).
type Distribution a = F (D a)

data D a o = Disjoint a o o
           | Independent [o]
           | Uniform (a -> o)
           deriving (Functor)

-- | @disjoint p u v@ represents either @u@ with probability @p@ or else
--   @v@ with probability @1-p@.
disjoint :: MonadFree (D a) m => a -> m o -> m o -> m o
disjoint p left right = wrap (Disjoint p left right)

-- | @independent l@ represents each element of @l@ independently of one another.
independent :: MonadFree (D a) m => [m o] -> m o
independent events = wrap (Independent events)

-- | @uniform (\p -> x)@ represents @x@ with @p@ chosen uniformly between 0 and 1.
uniform :: MonadFree (D a) m => (a -> m o) -> m o
uniform f = wrap (Uniform f)

-- | Use the given random number generator @g@ to eliminate all of the random
--   variables in a @Distribution@, flattening the remaining elements into a
--   list.
sample :: (RandomGen g, Random a, Ord a) => Distribution a o -> g -> ([o], g)
sample m = runState $ iterM c $ return <$> m
  where
    c (Disjoint p x y)   = state random >>= \r -> if r <= p then x else y
    c (Independent l)    = concat <$> sequence l
    c (Uniform f)        = state random >>= f

-- | The @Num@ instance for @Distribution@ is kind of dangerous; the binary
--   operators in particular act `freely`, constructing trees of trees and
--   generally making the output enormous. Use with caution.
instance (Num o) => Num (Distribution a o) where
  (+)         = liftM2 (+)
  (*)         = liftM2 (*)
  (-)         = liftM2 (-)
  negate      = fmap negate
  abs         = fmap abs
  signum      = fmap signum
  fromInteger = return . fromInteger
