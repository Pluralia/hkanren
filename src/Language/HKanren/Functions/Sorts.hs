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

module Language.HKanren.Functions.Sorts
  ( merge
  , split
  , mergeSort
  )
where

import Data.HUtils
import Language.HKanren.Syntax
import Language.HKanren.Types.List
import Language.HKanren.Types.Nat
import Language.HKanren.Functions.Nat

import Prelude (return, ($), Int, fromInteger, (*))

-----------------------------------------------------------------------------------------------------

merge
  :: forall k. (ListF :<: LFunctor k, NatF :<: LFunctor k, TypeI (Term1 k) Nat, TypeI (Term1 k) (List Nat))
  => Term k (List Nat)
  -> Term k (List Nat)
  -> Term k (List Nat)
  -> Predicate k
merge lx ly merged =
  conde
    (do
       merged === ly)
       lx ==^ Nil
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

mergeSort
  :: forall k. (ListF :<: LFunctor k, NatF :<: LFunctor k, TypeI (Term1 k) Nat, TypeI (Term1 k) (List Nat))
  => Term k (List Nat)
  -> Term k (List Nat)
  -> Predicate k
mergeSort l sorted =
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
       mergeSort lx sx
       mergeSort ly sy
       merge sx sy sorted)

-----------------------------------------------------------------------------------------------------
