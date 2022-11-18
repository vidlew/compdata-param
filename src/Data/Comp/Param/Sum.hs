
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Sum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides the infrastructure to extend signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Sum
    (
     (:<:),
     (:+:),
     caseD,

     -- * Projections for Signatures and Terms
     proj,
     project,
     deepProject,

     -- * Injections for Signatures and Terms
     inj,
     inject,
     inject',
     deepInject,

     injectCxt,
     liftCxt
    ) where

import Prelude hiding (sequence)
import Data.Comp.Param.Term
import Data.Comp.Param.Algebra
import Data.Comp.Param.Ops
import Data.Comp.Param.Difunctor
import Data.Comp.Param.Ditraversable


-- |Project a term to a sub signature.
project :: (g :<: f) => Cxt h f a b -> Maybe (g a (Cxt h f a b))
project = project_ proj


-- |Project a term to a sub signature.
project_ :: SigFunM Maybe f g -> Cxt h f a b -> Maybe (g a (Cxt h f a b))
project_ _ (Hole _) = Nothing
project_ f (In t) = f t
project_ _ (Var _) = Nothing

-- | Tries to coerce a term/context to a term/context over a sub-signature.
deepProject :: (Ditraversable g, g :<: f) => CxtFunM Maybe f g
{-# INLINE deepProject #-}
deepProject = appSigFunM' proj

-- |Inject a term where the outermost layer is a sub signature.
inject :: (g :<: f) => g a (Cxt h f a b) -> Cxt h f a b
inject = In . inj

-- |Inject a term over a sub signature to a term over larger signature.
deepInject :: (Difunctor g, g :<: f) => CxtFun g f
{-# INLINE deepInject #-}
deepInject = deepInject_ inj

-- |Inject a term over a sub signature to a term over larger signature.
deepInject_ :: (Difunctor g) => SigFun g f -> CxtFun g f
{-# INLINE deepInject_ #-}
deepInject_ = appSigFun

-- |Inject a term where the outermost layer is a sub signature.
inject' :: (Difunctor g, g :<: f) => g (Cxt h f a b) (Cxt h f a b) -> Cxt h f a b
inject' = inject . dimap Var id

--split :: (f :=: f1 :+: f2) => (f1 a (Term f) -> b) -> (f2 a (Term f) -> b) -> Term f -> b
--split f1 f2 (In t) = spl f1 f2 t

{-| This function injects a whole context into another context. -}
injectCxt :: (Difunctor g, g :<: f) => Cxt h g a (Cxt h f a b) -> Cxt h f a b
injectCxt (In t) = inject $ difmap injectCxt t
injectCxt (Hole x) = x
injectCxt (Var p) = Var p

{-| This function lifts the given functor to a context. -}
liftCxt :: (Difunctor f, g :<: f) => g a b -> Cxt Hole f a b
liftCxt g = simpCxt $ inj g

instance (Show (f a b), Show (g a b)) => Show ((f :+: g) a b) where
    show (Inl v) = show v
    show (Inr v) = show v

instance (Ord (f a b), Ord (g a b)) => Ord ((f :+: g) a b) where
    compare (Inl _) (Inr _) = LT
    compare (Inr _) (Inl _) = GT
    compare (Inl x) (Inl y) = compare x y
    compare (Inr x) (Inr y) = compare x y

instance (Eq (f a b), Eq (g a b)) => Eq ((f :+: g) a b) where
    (Inl x) == (Inl y) = x == y
    (Inr x) == (Inr y) = x == y                   
    _ == _ = False
