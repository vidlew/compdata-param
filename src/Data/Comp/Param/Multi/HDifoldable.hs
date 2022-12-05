{-# LANGUAGE Rank2Types, FlexibleInstances, MultiParamTypeClasses,
  FlexibleContexts, TypeOperators, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.HDitraversable
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines traversable higher-order difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.HDifoldable
    (
     HDifoldable (..),
     HFoldable (..)
    ) where

import Prelude hiding (mapM, sequence, foldr)
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.HFoldable
import Data.Comp.Param.Multi.Ops
import Data.Comp.Param.Multi.HDifunctor
import Data.Comp.Param.Multi.Algebra
--import Data.Coerce
import Data.Monoid

--instance Semigroup m => Semigroup (K m i) where
--    (K a) <> (K b) = K $ a<>b

--instance Monoid m => Monoid (K m i) where
--    mempty = K mempty

{-| HDifunctors representing data structures that can be folded. -}
class HDifunctor f => HDifoldable f where
    hdifold :: Monoid m => Alg f (K m)
    hdifold = K . hdifoldMap unK

    hdifoldMap :: Monoid m => (a :=> m) -> f a a :=> m
    hdifoldMap f = hdifoldr (mappend . f) mempty
    
    hdifoldr :: (a :=> (b -> b)) -> b -> f a a :=> b
    hdifoldr f z t = appEndo (hdifoldMap (Endo . f) t) z

    hdifoldl :: (b -> (a :=> b)) -> b -> f a a :=> b
    hdifoldl f z t = appEndo (getDual (hdifoldMap (Dual . Endo . flip f) t)) z

instance (HDifoldable f, HDifoldable g) => HDifoldable (f :+: g) where
    hdifold = caseHD hdifold hdifold
