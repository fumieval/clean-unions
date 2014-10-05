{-# LANGUAGE Rank2Types
  , TypeOperators
  , TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , DataKinds
  , KindSignatures
  , PolyKinds
  , GADTs
  , ScopedTypeVariables
  , LambdaCase
  , ConstraintKinds
  , FlexibleContexts
  , FunctionalDependencies
  , UndecidableInstances
  , OverlappingInstances #-}
module Data.OpenUnion1.Clean (Union(..), Nil, List(..), (|>)(..), (||>), exhaust, simply, (∈)(), Member, liftU, (⊆)(..), Include) where
import Data.Proxy

-- | Poly-kinded list
data List a = Empty | a :> List a

infixr 5 :>
infixr 5 |>

-- | Append a new element to a union.
type family (f :: * -> *) |> (s :: * -> *) :: * -> *

type instance f |> Union s = Union (f :> s)

-- | An uninhabited union.
type Nil = Union Empty

data family Union (s :: List (* -> *)) a

data instance Union (f :> s) a = Single (f a) | Union (Union s a)
data instance Union Empty a = Exhausted (Union Empty a)

instance Functor (Union Empty) where
  fmap _ = exhaust

instance (Functor f, Functor (Union s)) => Functor (Union (f :> s)) where
  fmap f (Single m) = Single (fmap f m)
  fmap f (Union u) = Union (fmap f u)

-- | Perform type-safe matching.
(||>) :: (f x -> r) -- ^ first case
  -> (Union s x -> r) -- ^ otherwise
  -> (Union (f :> s) x -> r) -- ^ matching function
(||>) run _ (Single f) = run f
(||>) _ cont (Union r) = cont r
infixr 0 ||>

exhaust :: Nil x -> r
exhaust (Exhausted a) = exhaust a

simply :: (f a -> r) -> ((f |> Nil) a -> r)
simply f = f ||> exhaust

data Position f s where
  Zero :: Position f (f :> s)
  Succ :: Position f s -> Position f (g :> s)

-- | Constraint @f ∈ s@ indicates that @f@ is an element of a type-level list @s@.
class f ∈ s | s -> f where
  query :: Proxy f -> Proxy s -> Position f s

infix 4 ∈
infix 4 ⊆

instance f ∈ (f :> s) where query _ _ = Zero
instance (f ∈ s) => f ∈ (g :> s) where query p q = Succ (query p (Proxy :: Proxy s))

-- | Lift some value into a union.
liftU :: forall s f a. (f ∈ s) => f a -> Union s a
liftU f = go $ query (Proxy :: Proxy f) (Proxy :: Proxy s) where
  go :: forall t. Position f t -> Union t a
  go Zero = Single f
  go (Succ q) = Union (go q)

-- | Type-level inclusion characterized by 'reunion'.
class s ⊆ t where
  -- | Lift a union into equivalent or larger one, permuting elements if necessary.
  reunion :: Union s a -> Union t a

instance (f ∈ t, s ⊆ t) => (f :> s) ⊆ t where
  reunion (Single f) = liftU f
  reunion (Union s) = reunion s

-- | Every set has an empty set as its subset.
instance Empty ⊆ t where
  reunion = exhaust

type Member f s = f ∈ s

type Include s t = s ⊆ t
