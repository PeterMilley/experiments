{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module ProfunctorOptics where

{-

Based on https://oleg.fi/gists/posts/2017-04-18-glassery.html

-}

import Control.Applicative (Const (..))
import Control.Arrow ((&&&), (+++), (***))
import Data.Foldable (Foldable (..), traverse_)
import Data.Functor.Identity (Identity (..))
import Data.Monoid (First (..), Endo (..))
import Data.Traversable (Traversable (..), traverse)
import Data.Tuple (swap)

-- utility functions

swapE :: Either a b -> Either b a
swapE = either Right Left

-- Optic definition
type Optic p s t a b = p a b -> p s t
type Optic' p s a = Optic p s s a a

-- Optic operations

over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id

set :: Optic (->) s t a b -> b -> s -> t
set o b = o (const b)

newtype Tagged a b = Tagged { unTagged :: b }

review :: Optic Tagged s t a b -> b -> t
review o b = unTagged $ o (Tagged b)

newtype Forget r a b = Forget { runForget :: a -> r }

foldMapOf :: Optic (Forget r) s t a b -> (a -> r) -> s -> r
foldMapOf o p = runForget $ o (Forget p)

view :: Optic (Forget a) s t a b -> s -> a
view o = runForget $ o (Forget id)

toListOf :: Optic (Forget (Endo [a])) s t a b -> s -> [a]
toListOf o s = appEndo (foldMapOf o (Endo . (:)) s) []

newtype ForgetM r a b = ForgetM { runForgetM :: a -> Maybe r }

preview :: Optic (ForgetM a) s t a b -> s -> Maybe a
preview o = runForgetM $ o (ForgetM Just)

newtype ForgetE r a b = ForgetE { runForgetE :: a -> Either b r }

matching :: Optic (ForgetE a) s t a b -> s -> Either t a
matching o = runForgetE $ o (ForgetE Right)

newtype Star f a b = Star { runStar :: a -> f b }

withStar :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
withStar o p = runStar $ o (Star p)

traverseOf :: Applicative f => Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf = withStar

-- Optic types

-- Equality
type Equality s t a b = forall p . Optic p s t a b

eq :: Equality a b a b
eq = id

-- Equality supports all optic operations, trivially.

-- Profunctor and Iso
class Profunctor p where
  dimap :: (s -> a) -> (b -> t) -> p a b -> p s t

type Iso s t a b = forall p . Profunctor p => Optic p s t a b

iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso = dimap

-- Iso supports all operations.
instance Profunctor (->) where
  dimap f g h = g . h . f
instance Profunctor Tagged where
  dimap _ g o = Tagged $ (g . unTagged) o
instance Profunctor (Forget r) where
  dimap f _ o = Forget $ runForget o . f
instance Profunctor (ForgetM r) where
  dimap f _ o = ForgetM $ runForgetM o . f
instance Profunctor (ForgetE r) where
  dimap f g o = ForgetE $ (g +++ id) . runForgetE o . f
instance Functor f => Profunctor (Star f) where
  dimap f g o = Star $ fmap g . runStar o . f

-- Strong and Lens
class Profunctor p => Strong p where
  first' :: p a b -> p (a, c) (b, c)
  first' = dimap swap swap . second'
  second' :: p a b -> p (c, a) (c, b)
  second' = dimap swap swap . first'

type Lens s t a b = forall p . Strong p => Optic p s t a b

elens :: (s -> (a, c)) -> ((b, c) -> t) -> Lens s t a b
elens getter setter = dimap getter setter . first'

lens :: (s -> a) -> (b -> s -> t) -> Lens s t a b
lens getter setter = dimap (getter &&& id) (uncurry setter) . first'

-- Lens supports all operations except review
instance Strong (->) where
  first' f  = f *** id
  second' f = id *** f
instance Strong (Forget r) where
  first' (Forget p)  = Forget $ p . fst
  second' (Forget p) = Forget $ p . snd
instance Strong (ForgetM r) where
  first' (ForgetM p)  = ForgetM $ p . fst
  second' (ForgetM p) = ForgetM $ p . snd
instance Strong (ForgetE r) where
  first' (ForgetE p)  = ForgetE $ \(a, c) -> ((,c) +++ id) (p a)
  second' (ForgetE p) = ForgetE $ \(c, a) -> ((c,) +++ id) (p a)
instance Functor f => Strong (Star f) where
  first' (Star p)  = Star $ \(a, c) -> fmap (,c) (p a)
  second' (Star p) = Star $ \(c, a) -> fmap (c,) (p a)

-- Choice and Prism
class Profunctor p => Choice p where
  right' :: p a b -> p (Either c a) (Either c b)
  right' = dimap swapE swapE . left'
  left' :: p a b -> p (Either a c) (Either b c)
  left' = dimap swapE swapE . right'

type Prism s t a b = forall p . Choice p => Optic p s t a b

eprism :: (s -> Either c a) -> (Either c b -> t) -> Prism s t a b
eprism match build = dimap match build . right'

prism :: (s -> Either t a) -> (b -> t) -> Prism s t a b
prism match build = dimap match (either id build) . right'

prism' :: (s -> Maybe a) -> (b -> s) -> Prism s s a b
prism' match build = prism (\s -> maybe (Left s) Right (match s)) build

just' :: Prism (Maybe a) (Maybe b) a b
just' = prism (maybe (Left Nothing) Right) Just

-- Prism supports all operations except view, but foldMapOf requires 'r'
-- to be a Monoid.
instance Choice (->) where
  right' g = id +++ g
  left' g  = g +++ id
instance Choice Tagged where
  right' (Tagged b) = Tagged $ Right b
  left' (Tagged b)  = Tagged $ Left b
instance Monoid r => Choice (Forget r) where
  right' (Forget p) = Forget $ either (const mempty) p
  left' (Forget p)  = Forget $ either p (const mempty)
instance Choice (ForgetM r) where
  right' (ForgetM p) = ForgetM $ either (const Nothing) p
  left' (ForgetM p)  = ForgetM $ either p (const Nothing)
instance Choice (ForgetE r) where
  right' (ForgetE p) = ForgetE $ either (Left . Left) ((Right +++ id) . p)
  left' (ForgetE p)  = ForgetE $ either ((Left +++ id) . p) (Left . Right)
instance Applicative f => Choice (Star f) where
  right' (Star p) = Star $ either (fmap Left . pure) (fmap Right . p)
  left' (Star p)  = Star $ either (fmap Left . p) (fmap Right . pure)

-- Bifunctor and Review
class Bifunctor p where
  bimap :: (a -> s) -> (b -> t) -> p a b -> p s t

type Review t b = forall p . (Choice p, Bifunctor p) => Optic' p t b

upto :: (b -> t) -> Review t b
upto f = bimap f f

-- Review only supports review.
instance Bifunctor Tagged where
  bimap _ g o = Tagged $ (g . unTagged) o

-- Bicontravariant and Getter
class Bicontravariant p where
  cimap :: (s -> a) -> (t -> b) -> p a b -> p s t

type Getter s a = forall p . (Strong p, Bicontravariant p) => Optic' p s a

to :: (s -> a) -> Getter s a
to f = cimap f f

-- Getter supports view and preview. It feels like it should support matching
-- as well but ForgetE isn't bicontravariant.
instance Bicontravariant (Forget r) where
  cimap f _ o = Forget $ runForget o . f
instance Bicontravariant (ForgetM r) where
  cimap f _ o = ForgetM $ runForgetM o . f

-- Traversing and Traversal
class (Strong p, Choice p) => Traversing p where
  wander :: (forall f . Applicative f => (a -> f b) -> s -> f t)
         -> p a b -> p s t
  traverse' :: Traversable g => p a b -> p (g a) (g b)
  traverse' = wander traverse

type Traversal s t a b = forall p . Traversing p => Optic p s t a b

traversing :: (forall f . Applicative f => (a -> f b) -> s -> f t)
           -> Traversal s t a b
traversing = wander

-- Traversal supports every operation except view and review. If 'r' is a
-- Monoid then foldMapOf is supported.
instance Traversing (->) where
  wander g f = runIdentity . g (Identity . f)
instance Monoid r => Traversing (Forget r) where
  wander g (Forget p) = Forget $ getConst . g (Const . p)
instance Traversing (ForgetM r) where
  wander g (ForgetM p) = ForgetM $ getFirst . getConst . g (Const . First . p)
instance Traversing (ForgetE r) where
  wander g (ForgetE p) = ForgetE $ swapE . g (swapE . p)
instance Applicative f => Traversing (Star f) where
  wander g (Star p) = Star $ g p

-- (Traversing + Bicontravariant) and Fold

type Fold s a = forall p . (Traversing p, Bicontravariant p) => Optic' p s a

folding :: Foldable f => (s -> f a) -> Fold s a
folding g = cimap g (const ()) . wander traverse_

-- Fold supports toListOf, and foldMapOf when 'r' is a Monoid.

-- Mapping and Setter.
class Traversing p => Mapping p where
  map' :: Functor f => p a b -> p (f a) (f b)

type Setter s t a b = forall p . Mapping p => Optic p s t a b

-- Helper functor to implement 'setting'.
data Context s a x = Context (a -> x) s deriving Functor

setting :: ((a -> b) -> s -> t) -> Setter s t a b
setting f = dimap (Context id) (\(Context g s) -> f g s) . map'

mapped :: Functor f => Setter (f a) (f b) a b
mapped = setting fmap

-- Setter only supports over and set on its own.
instance Mapping (->) where
  map' = fmap
