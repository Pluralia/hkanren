----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.Functions.List
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Language.HKanren.Functions.List
  ( appendo
  , allUnique
  , member
  , memberp
  , notMember
  , allo
  , foldlo
  , foldlo'
  , foldl2o
  , foldl2o'
---------------------------
  , sortedMergeTwo
  , merge
  , split
  , sort
  )
where

import Data.HUtils
import Language.HKanren.Syntax
import Language.HKanren.Types.List
import Language.HKanren.Types.Nat
import Language.HKanren.Functions.Nat

import Prelude (return, ($), Int, fromInteger, (*))

-----------------------------------------------------------------------------------------------------

mergeTwo
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k ix
  -> Term k ix
  -> Term k (List ix)
  -> Predicate k
mergeTwo x y merged =
  fresh $ \nil ys -> do
    nil ==^ Nil
    Cons y nil ^== ys
    Cons x ys ^== merged

sortedMergeTwo
  :: forall k. (ListF :<: LFunctor k, NatF :<: LFunctor k, TypeI (Term1 k) Nat, TypeI (Term1 k) (List Nat))
  => Term k Nat
  -> Term k Nat
  -> Term k (List Nat)
  -> Predicate k
sortedMergeTwo x y merged =
  conde
    (do
       leqo x y (iS iZ)
       mergeTwo x y merged)
    (do
       leqo x y iZ
       mergeTwo y x merged)

merge
  :: forall k. (ListF :<: LFunctor k, NatF :<: LFunctor k, TypeI (Term1 k) Nat, TypeI (Term1 k) (List Nat))
  => Term k (List Nat)
  -> Term k (List Nat)
  -> Term k (List Nat)
  -> Predicate k
merge lx ly merged =
  conde
    (do
       lx ==^ Nil
       merged === ly)
    (do
       ly ==^ Nil
       merged === lx)
    (fresh $ \x xs y ys ms -> do
       Cons x xs ^== lx
       Cons y ys ^== ly
       leqo x y (iS iZ)
       merge xs ly ms
       Cons x ms ^== merged)
    (merge ly lx merged)

split
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k (List ix)
  -> Term k (List ix)
  -> Term k (List ix)
  -> Predicate k
split lx ly l =
  conde
    (do
       l ==^ Nil
       lx ==^ Nil
       ly ==^ Nil)
    (fresh $ \nil x -> do
       nil ==^ Nil
       Cons x nil ^== l
       lx === l
       ly ==^ Nil)
    (fresh $ \x xs y ys lx' ly' -> do
       Cons x xs ^== l
       Cons y ys ^== xs
       split lx' ly' ys
       Cons x lx' ^== lx
       Cons y ly' ^== ly)

sort
  :: forall k. (ListF :<: LFunctor k, NatF :<: LFunctor k, TypeI (Term1 k) Nat, TypeI (Term1 k) (List Nat))
  => Term k (List Nat)
  -> Term k (List Nat)
  -> Predicate k
sort l sorted =
  conde
    (do
       l ==^ Nil
       sorted ==^ Nil)
    (fresh $ \nil x -> do
       nil ==^ Nil
       Cons x nil ^== l
       sorted === l)
    (fresh $ \lx ly sx sy -> do
       split lx ly l
       sort lx sx
       sort ly sy
       merge lx ly sorted)

-----------------------------------------------------------------------------------------------------

appendo
  :: (ListF :<: LFunctor k, TypeI (Term1 k) (List ix), TypeI (Term1 k) ix)
  => Term k (List ix)
  -> Term k (List ix)
  -> Term k (List ix)
  -> Predicate k
appendo l r o =
  conde
    (do l ==^ Nil
        o === r)
    (fresh $ \h t o' -> do
      Cons h t  ^== l
      appendo t r o'
      Cons h o' ^== o)

allUnique
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k (List ix) -> Predicate k
allUnique args =
  conde
    (args ==^ Nil)
    (fresh $ \x xs -> do
      args ==^ Cons x xs
      notMember x xs
      allUnique xs)

member
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k ix -> Term k (List ix) -> Predicate k
member x xs =
  (fresh $ \y ys -> do
    xs ==^ Cons y ys
    conde
      (x === y)
      (do x =/= y
          member x ys))

memberp
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k ix -> Term k (List ix) -> Predicate k
memberp x xs =
  (fresh $ \y ys -> do
    xs ==^ Cons y ys
    condp
      ( (2 * one)
      , x === y)
      ( one
      , do x =/= y
           memberp x ys))
  where
    one :: Int
    one = 1

notMember
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k ix -> Term k (List ix) -> Predicate k
notMember x xs =
  conde
    (xs ==^ Nil)
    (fresh $ \y ys -> do
      xs ==^ Cons y ys
      x =/= y
      notMember x ys)

allo
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => (Term k ix -> Predicate k) -> Term k (List ix) -> Predicate k
allo p xs =
  conde
    (xs ==^ Nil)
    (fresh $ \y ys -> do
      xs ==^ Cons y ys
      p y
      allo p ys)

foldlo
  :: forall k acc ix. (ListF :<: LFunctor k, TypeI (Term1 k) acc, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => (Term k acc -> Term k ix -> Term k acc -> Predicate k)
  -> Term k acc
  -> Term k (List ix)
  -> Term k acc
  -> Predicate k
foldlo f acc xs out =
  conde
    (do xs  ==^ Nil
        acc === out)
    (fresh $ \y ys out' -> do
      xs ==^ Cons y ys
      f acc y out'
      foldlo f out' ys out)

foldlo'
  :: forall k acc ix. (ListF :<: LFunctor k, TypeI (Term1 k) acc, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k acc
  -> Term k (List ix)
  -> Term k acc
  -> (Term k acc -> Term k ix -> Term k acc -> Predicate k)
  -> Predicate k
foldlo' acc xs out f = foldlo f acc xs out


foldl2o
  :: forall k acc acc' ix.
     (ListF :<: LFunctor k, TypeI (Term1 k) acc, TypeI (Term1 k) acc', TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => (Term k acc -> Term k acc' -> Term k ix -> Term k acc -> Term k acc' -> Predicate k)
  -> Term k acc
  -> Term k acc'
  -> Term k (List ix)
  -> Term k acc
  -> Term k acc'
  -> Predicate k
foldl2o f acc acc' xs out out' =
  conde
    (do xs   ==^ Nil
        acc  === out
        acc' === out')
    (fresh $ \y ys out1 out2 -> do
      xs ==^ Cons y ys
      f acc acc' y out1 out2
      foldl2o f out1 out2 ys out out')


foldl2o'
  :: forall k acc acc' ix.
     (ListF :<: LFunctor k, TypeI (Term1 k) acc, TypeI (Term1 k) acc', TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k acc
  -> Term k acc'
  -> Term k (List ix)
  -> Term k acc
  -> Term k acc'
  -> (Term k acc -> Term k acc' -> Term k ix -> Term k acc -> Term k acc' -> Predicate k)
  -> Predicate k
foldl2o' acc acc' xs out out' f =
  foldl2o f acc acc' xs out out'
