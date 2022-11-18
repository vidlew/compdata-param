{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, UndecidableInstances, IncoherentInstances #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Ops
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides operators on difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Ops where

import Data.Comp.Param.Difunctor
import Data.Comp.Param.Ditraversable
import Control.Monad (liftM)

import Data.Comp.SubsumeCommon

-- Sums
infixr 6 :+:

-- |Formal sum of signatures (difunctors).
data (f :+: g) a b = Inl (f a b)
                   | Inr (g a b)

{-| Utility function to case on a difunctor sum, without exposing the internal
  representation of sums. -}
caseD :: (f a b -> c) -> (g a b -> c) -> (f :+: g) a b -> c
caseD f g x = case x of
                Inl x -> f x
                Inr x -> g x

instance (Difunctor f, Difunctor g) => Difunctor (f :+: g) where
    dimap f g (Inl e) = Inl (dimap f g e)
    dimap f g (Inr e) = Inr (dimap f g e)

instance (Ditraversable f, Ditraversable g) => Ditraversable (f :+: g) where
    dimapM f (Inl e) = Inl `liftM` dimapM f e
    dimapM f (Inr e) = Inr `liftM` dimapM f e
    disequence (Inl e) = Inl `liftM` disequence e
    disequence (Inr e) = Inr `liftM` disequence e

infixl 5 :<:
infixl 5 :=:

type family Elem (f :: * -> * -> *) (g :: * -> * -> *) :: Emb where
  Elem f f = Found Here
  Elem (f1 :+: f2) g = Sum' (Elem f1 g) (Elem f2 g)
  Elem f (g1 :+: g2) = Choose (Elem f g1) (Elem f g2)
  Elem f g = NotFound

class Subsume (e :: Emb) (f :: * -> * -> *) (g :: * -> * -> *) where
  inj' :: Proxy e -> f a b -> g a b
  prj' :: Proxy e -> g a b -> Maybe (f a b)

instance Subsume (Found Here) f f where
    inj' _ = id

    prj' _ = Just

instance Subsume (Found p) f g => Subsume (Found (Le p)) f (g :+: g') where
    inj' _ = Inl . inj' (P :: Proxy (Found p))

    prj' _ (Inl x) = prj' (P :: Proxy (Found p)) x
    prj' _ _       = Nothing

instance Subsume (Found p) f g => Subsume (Found (Ri p)) f (g' :+: g) where
    inj' _ = Inr . inj' (P :: Proxy (Found p))

    prj' _ (Inr x) = prj' (P :: Proxy (Found p)) x
    prj' _ _       = Nothing

instance (Subsume (Found p1) f1 g, Subsume (Found p2) f2 g)
    => Subsume (Found (Sum p1 p2)) (f1 :+: f2) g where
    inj' _ (Inl x) = inj' (P :: Proxy (Found p1)) x
    inj' _ (Inr x) = inj' (P :: Proxy (Found p2)) x

    prj' _ x = case prj' (P :: Proxy (Found p1)) x of
                 Just y -> Just (Inl y)
                 _      -> case prj' (P :: Proxy (Found p2)) x of
                             Just y -> Just (Inr y)
                             _      -> Nothing

-- | A constraint @f :<: g@ expresses that the signature @f@ is
-- subsumed by @g@, i.e. @f@ can be used to construct elements in @g@.
type f :<: g = (Subsume (ComprEmb (Elem f g)) f g)

inj :: forall f g a b . (f :<: g) => f a b -> g a b
inj = inj' (P :: Proxy (ComprEmb (Elem f g)))

proj :: forall f g a b . (f :<: g) => g a b -> Maybe (f a b)
proj = prj' (P :: Proxy (ComprEmb (Elem f g)))

type f :=: g = (f :<: g, g :<: f)



spl :: (f :=: f1 :+: f2) => (f1 a b -> c) -> (f2 a b -> c) -> f a b -> c
spl f1 f2 x = case inj x of
            Inl y -> f1 y
            Inr y -> f2 y


------------------------------------------------------------------------------


-- Products
infixr 8 :*:

-- |Formal product of signatures (difunctors).
data (f :*: g) a b = f a b :*: g a b

ffst :: (f :*: g) a b -> f a b
ffst (x :*: _) = x

fsnd :: (f :*: g) a b -> g a b
fsnd (_ :*: x) = x


-- Constant Products
infixr 7 :&:

{-| This data type adds a constant product to a signature. -}
data (f :&: p) a b = f a b :&: p

instance Difunctor f => Difunctor (f :&: p) where
    dimap f g (v :&: c) = dimap f g v :&: c

instance Ditraversable f => Ditraversable (f :&: p) where
    dimapM f (v :&: c) = liftM (:&: c) (dimapM f v)
    disequence (v :&: c) = liftM (:&: c) (disequence v)

{-| This class defines how to distribute an annotation over a sum of
  signatures. -}
class DistAnn s p s' | s' -> s, s' -> p where
    {-| Inject an annotation over a signature. -}
    injectA :: p -> s a b -> s' a b
    {-| Project an annotation from a signature. -}
    projectA :: s' a b -> (s a b, p)

class RemA s s' | s -> s'  where
    {-| Remove annotations from a signature. -}
    remA :: s a b -> s' a b

instance (RemA s s') => RemA (f :&: p :+: s) (f :+: s') where
    remA (Inl (v :&: _)) = Inl v
    remA (Inr v) = Inr $ remA v

instance RemA (f :&: p) f where
    remA (v :&: _) = v

instance DistAnn f p (f :&: p) where
    injectA c v = v :&: c

    projectA (v :&: p) = (v,p)

instance (DistAnn s p s') => DistAnn (f :+: s) p ((f :&: p) :+: s') where
    injectA c (Inl v) = Inl (v :&: c)
    injectA c (Inr v) = Inr $ injectA c v

    projectA (Inl (v :&: p)) = (Inl v,p)
    projectA (Inr v) = let (v',p) = projectA v
                       in  (Inr v',p)
