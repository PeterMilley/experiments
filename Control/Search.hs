{-# LANGUAGE ScopedTypeVariables #-}
module Control.Search where

{-|
Module      : Control.Search
Description : Helper functions implementing search algorithms.

-}

import Control.Monad.State
import qualified Data.Set as S

breadthFirst :: (Monad m, Ord a) => (a -> m [a]) -> [a] -> m ()
breadthFirst = breadthFirstOn id 

breadthFirstOn :: forall m a b. (Monad m, Ord b) =>
                  (a -> b) -> (a -> m [a]) -> [a] -> m ()
breadthFirstOn on f init = evalStateT (go init) S.empty
  where
    go :: [a] -> StateT (S.Set b) m ()
    go [] = return ()
    go (x:xs) = do
      let y = on x
      visited <- gets (S.member y)
      if visited then (go xs) else do
        modify (S.insert y)
        lift (f x) >>= (\n -> go (xs++n))
