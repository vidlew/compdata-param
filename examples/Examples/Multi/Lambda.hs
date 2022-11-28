{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, Rank2Types, GADTs, ScopedTypeVariables, TypeFamilies #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.MultiParam.Lambda
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Tagless (monadic) interpretation of extended lambda calculus
--
--------------------------------------------------------------------------------




module Examples.Multi.Lambda where

import Data.Comp.Param.Multi
import Data.Comp.Param.Multi.Show ()
import Data.Comp.Param.Multi.Equality ()
import Data.Comp.Param.Multi.Derive
import Control.Monad (liftM2)
import Control.Monad.Except (MonadError, throwError)

data Lam :: (* -> *) -> (* -> *) -> * -> * where
  Lam :: (a i -> b j) -> Lam a b (i -> j)
data App :: (* -> *) -> (* -> *) -> * -> * where
  App :: b (i -> j) -> b i -> App a b j
data Const :: (* -> *) -> (* -> *) -> * -> * where
  Const :: Int -> Const a b Int
data Plus :: (* -> *) -> (* -> *) -> * -> * where
  Plus :: b Int -> b Int -> Plus a b Int
data Err :: (* -> *) -> (* -> *) -> * -> * where
  Err :: Err a b i
type Sig = Lam :+: App :+: Const :+: Plus :+: Err

data Let :: (* -> *) -> (* -> *) -> * -> * where
  Let :: b i -> (a i -> b j) -> Let a b j

$(derive [smartConstructors, makeHDifunctor, makeEqHD]
         [''Lam, ''Let, ''App, ''Const, ''Plus, ''Err])

-- * Pretty printing
data Stream a = Cons a (Stream a)

class Pretty f where
  prettyAlg :: Alg f (K (Stream String -> String))

$(derive [liftSum] [''Pretty])

pretty :: (HDifunctor f, Pretty f) => Term f i -> String
pretty t = (unK $ cata prettyAlg t) (nominals 1)
    where nominals n = Cons ('x' : show n) (nominals (n + 1))

instance Pretty Lam where
  prettyAlg (Lam f) = K $ \(Cons x xs) -> "(\\" ++ x ++ ". " ++ unK (f (K $ const x)) xs ++ ")"

instance Pretty App where
  prettyAlg (App e1 e2) = K $ \xs -> "(" ++ unK e1 xs ++ " " ++ unK e2 xs ++ ")"

instance Pretty Const where
  prettyAlg (Const n) = K . const $ show n

instance Pretty Plus where
  prettyAlg (Plus e1 e2) = K $ \xs -> "(" ++ unK e1 xs ++ " + " ++ unK e2 xs ++ ")"

instance Pretty Err where
  prettyAlg Err = K $ const "error"

instance Pretty Let where
  prettyAlg (Let e1 e2) = K $ \(Cons x xs) -> "let " ++ x ++ " = " ++ unK e1 xs ++ " in " ++ unK (e2 (K $ const x)) xs

-- * Tagless interpretation
class Eval f where
  evalAlg :: f I I i -> i -- I . evalAlg :: Alg f I is the actual algebra

$(derive [liftSum] [''Eval])

eval :: (HDifunctor f, Eval f) => Term f i -> i
eval = unI . cata (I . evalAlg)

instance Eval Lam where
  evalAlg (Lam f) = unI . f . I

instance Eval Let where
  evalAlg (Let x f) = unI $ f x

instance Eval App where
  evalAlg (App (I f) (I x)) = f x

instance Eval Const where
  evalAlg (Const n) = n

instance Eval Plus where
  evalAlg (Plus (I x) (I y)) = x + y

instance Eval Err where
  evalAlg Err = error "error"

-- * Tagless monadic interpretation
type family Sem (m :: * -> *) i
type instance Sem m (i -> j) = Sem m i -> m (Sem m j)
type instance Sem m Int = Int

newtype M m i = M {unM :: m (Sem m i)}

class Monad m => EvalM m f where
  evalMAlg :: f (M m) (M m) i -> m (Sem m i) -- M . evalMAlg :: Alg f (M m)

$(derive [liftSum] [''EvalM])

evalM :: (Monad m, HDifunctor f, EvalM m f) => Term f i -> m (Sem m i)
evalM = unM . cata (M . evalMAlg)

instance Monad m => EvalM m Lam where
  evalMAlg (Lam f) = return $ unM . f . M . return

instance Monad m => EvalM m App where
  evalMAlg (App (M mf) (M mx)) = do f <- mf; f =<< mx

instance Monad m => EvalM m Const where
  evalMAlg (Const n) = return n

instance Monad m => EvalM m Plus where
  evalMAlg (Plus (M mx) (M my)) = liftM2 (+) mx my

instance (MonadError String m, Monad m) => EvalM m Err where
  evalMAlg Err = throwError "error" -- 'throwError' rather than 'error'

e :: Term Sig Int
e = Term ((iLam $ \x -> (iLam (\y -> y `iPlus` x) `iApp` iConst 3)) `iApp` iConst 2)

ex :: Term (Sig :+: Let) Int
ex = Term $ iLet (iLam (\x -> iLam $ \y -> iPlus x y)) (\x -> x `iApp` iConst 5 `iApp` (iConst 7))

v :: Either String Int
v = evalM e

e' :: Term Sig (Int -> Int)
e' = Term iErr --(iLam id)

v' :: Either String (Int -> Either String Int)
v' = evalM e'
