{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Ops
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides operators on higher-order difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Ops where

import Data.Comp.Param.Multi.HDifunctor
import Data.Comp.Param.Multi.HDitraversable
import qualified Data.Comp.Ops as O
import Control.Monad (liftM)

import Data.Comp.SubsumeCommon


-- Sums
infixr 6 :+:

-- |Formal sum of signatures (difunctors).
data (f :+: g) (a :: * -> *) (b :: * -> *) i = Inl (f a b i)
                                             | Inr (g a b i)

{-| Utility function to case on a higher-order difunctor sum, without exposing
  the internal representation of sums. -}
caseHD :: (f a b i -> c) -> (g a b i -> c) -> (f :+: g) a b i -> c
caseHD f g x = case x of
                 Inl x -> f x
                 Inr x -> g x

instance (HDifunctor f, HDifunctor g) => HDifunctor (f :+: g) where
    hdimap f g (Inl e) = Inl (hdimap f g e)
    hdimap f g (Inr e) = Inr (hdimap f g e)

instance (HDitraversable f, HDitraversable g) => HDitraversable (f :+: g) where
    hdimapM f (Inl e) = Inl `liftM` hdimapM f e
    hdimapM f (Inr e) = Inr `liftM` hdimapM f e

-- The subsumption relation.

infixl 5 :<:
infixl 5 :=:


type family Elem (f :: (* -> *) -> (* -> *) -> * -> *)
                 (g :: (* -> *) -> (* -> *) -> * -> *) :: Emb where
    Elem f f = Found Here
    Elem (f1 :+: f2) g =  Sum' (Elem f1 g) (Elem f2 g)
    Elem f (g1 :+: g2) = Choose (Elem f g1) (Elem f g2)
    Elem f g = NotFound

class Subsume (e :: Emb) (f :: (* -> *) -> (* -> *) -> * -> *)
                         (g :: (* -> *) -> (* -> *) -> * -> *) where
  inj'  :: Proxy e -> f a b :-> g a b
  prj'  :: Proxy e -> NatM Maybe (g a b) (f a b)

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

type f :<: g = (Subsume (ComprEmb (Elem f g)) f g)


inj :: forall f g a b . (f :<: g) => f a b :-> g a b
inj = inj' (P :: Proxy (ComprEmb (Elem f g)))

proj :: forall f g a b . (f :<: g) => NatM Maybe (g a b) (f a b)
proj = prj' (P :: Proxy (ComprEmb (Elem f g)))

type f :=: g = (f :<: g, g :<: f)

--------------------------------------------------------------------------------------------------------------------------------------------------------


-- Products
infixr 8 :*:

-- |Formal product of signatures (higher-order difunctors).
data (f :*: g) a b i = f a b i :*: g a b i

ffst :: (f :*: g) a b :-> f a b
ffst (x :*: _) = x

fsnd :: (f :*: g) a b :-> g a b
fsnd (_ :*: x) = x


-- Constant Products
infixr 7 :&:

{-| This data type adds a constant product to a signature. -}
data (f :&: p) (a :: * -> *) (b :: * -> *) i = f a b i :&: p

instance HDifunctor f => HDifunctor (f :&: p) where
    hdimap f g (v :&: c) = hdimap f g v :&: c

instance HDitraversable f => HDitraversable (f :&: p) where
    hdimapM f (v :&: c) = liftM (:&: c) (hdimapM f v)

{-| This class defines how to distribute an annotation over a sum of
  signatures. -}
class DistAnn (s :: (* -> *) -> (* -> *) -> * -> *) p s' | s' -> s, s' -> p where
    {-| Inject an annotation over a signature. -}
    injectA :: p -> s a b :-> s' a b
    {-| Project an annotation from a signature. -}
    projectA :: s' a b :-> (s a b O.:&: p)

class RemA (s :: (* -> *) -> (* -> *) -> * -> *) s' | s -> s' where
    {-| Remove annotations from a signature. -}
    remA :: s a b :-> s' a b

instance (RemA s s') => RemA (f :&: p :+: s) (f :+: s') where
    remA (Inl (v :&: _)) = Inl v
    remA (Inr v) = Inr $ remA v

instance RemA (f :&: p) f where
    remA (v :&: _) = v

instance DistAnn f p (f :&: p) where
    injectA c v = v :&: c

    projectA (v :&: p) = v O.:&: p

instance (DistAnn s p s') => DistAnn (f :+: s) p ((f :&: p) :+: s') where
    injectA c (Inl v) = Inl (v :&: c)
    injectA c (Inr v) = Inr $ injectA c v

    projectA (Inl (v :&: p)) = Inl v O.:&: p
    projectA (Inr v) = let (v' O.:&: p) = projectA v
                       in Inr v' O.:&: p
