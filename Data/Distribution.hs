{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
module Distribution where

import Control.Monad.Free
import Control.Monad.State
import System.Random

type Distribution a = Free (D a)
data D a o = Disjoint a o o
           | Independent [o]
           | Uniform (a -> o)
           deriving (Functor)

disjoint :: MonadFree (D a) m => a -> m o -> m o -> m o
disjoint p left right = wrap (Disjoint p left right)

independent :: MonadFree (D a) m => [m o] -> m o
independent events = wrap (Independent events)

uniform :: MonadFree (D a) m => (a -> m o) -> m o
uniform f = wrap (Uniform f)

expectation :: Fractional a => Distribution a a -> a
expectation = iter c
  where
    c (Disjoint p left right) = p * left + (1-p) * right
    c (Independent events)    = sum events
    c (Uniform f)             = f 0.5

sample :: (RandomGen g, Random a, Ord a) => Distribution a o -> g -> ([o], g)
sample m = runState $ iterM c $ return <$> m
  where
    c (Disjoint p x y)   = state random >>= \r -> if r <= p then x else y
    c (Independent l)    = concat <$> sequence l
    c (Uniform f)        = state random >>= f
