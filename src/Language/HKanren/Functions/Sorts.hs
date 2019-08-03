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
  (
  -- merge sort
    mergeSort
  , split  
  , merge
  , leqo
  -- perm sort
  , permSort
  , smallesto
  , minmaxo
  )
where

import Data.HUtils
import Language.HKanren.Syntax
import Language.HKanren.Types.List
import Language.HKanren.Types.Nat
import Language.HKanren.Functions.Nat()

import Prelude (return, ($)) 


-----------------------------------------------------------------------------------------------------
-- perm sort ----------------------------------------------------------------------------------------

permSort
  :: forall k. (ListF :<: LFunctor k, NatF :<: LFunctor k, TypeI (Term1 k) Nat, TypeI (Term1 k) (List Nat), LVar k)
  => Term k (List Nat)
  -> Term k (List Nat)
  -> Predicate k
permSort l sorted =
  conde
    (do
       l === iNil
       sorted === iNil)
    (fresh $ \small s s' -> do
       iCons small s' === sorted
       smallesto l small s
       permSort s s'
    )

smallesto
  :: forall k. (ListF :<: LFunctor k, NatF :<: LFunctor k, TypeI (Term1 k) Nat, TypeI (Term1 k) (List Nat), LVar k)
  => Term k (List Nat)
  -> Term k Nat
  -> Term k (List Nat)
  -> Predicate k
smallesto l small restl =
  conde
    (do
       iCons small iNil === l
       restl === iNil)
    (fresh $ \h t rh rt small' -> do
       iCons h t === l
       iCons rh rt === restl
       smallesto t small' rt
       minmaxo h small' small rh)

minmaxo
  :: forall k. (NatF :<: LFunctor k, TypeI (Term1 k) Nat, TypeI (Term1 k) (List Nat))
  => Term k Nat
  -> Term k Nat
  -> Term k Nat
  -> Term k Nat
  -> Predicate k
minmaxo a b min max =
  conde
    (do
       leqo a b (iS iZ)
       min === a
       max === b)
    (do
       leqo a b iZ
       min === b
       max === a)

-----------------------------------------------------------------------------------------------------
-- merge sort ---------------------------------------------------------------------------------------

mergeSort
  :: forall k. (ListF :<: LFunctor k, NatF :<: LFunctor k, TypeI (Term1 k) Nat, TypeI (Term1 k) (List Nat), LVar k)
  => Term k (List Nat)
  -> Term k (List Nat)
  -> Predicate k
mergeSort l sorted =
  conde
    (fresh $ \x -> do
       conde
         (do
            l === iNil)
         (do
            iCons x iNil === l)
       sorted === l)
    (fresh $ \h t lx ly sx sy -> do
       iCons h t === l
       split lx ly l
       mergeSort lx sx
       mergeSort ly sy
       merge sx sy sorted)

split
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix), LVar k)
  => Term k (List ix)
  -> Term k (List ix)
  -> Term k (List ix)
  -> Predicate k
split lx ly l =
  conde
    (fresh $ \x -> do
       conde
         (do
            l === iNil)
         (do
            iCons x iNil === l)
       lx === l
       ly === iNil)
    (fresh $ \x xs y ys lx' ly' -> do
       iCons x xs === l
       iCons y ys === xs
       split lx' ly' ys
       iCons x lx' === lx
       iCons y ly' === ly)

merge
  :: forall k. (ListF :<: LFunctor k, NatF :<: LFunctor k, TypeI (Term1 k) Nat, TypeI (Term1 k) (List Nat), LVar k)
  => Term k (List Nat)
  -> Term k (List Nat)
  -> Term k (List Nat)
  -> Predicate k
merge lx ly merged =
  conde
   (do
      lx === iNil
      merged === ly)
    (do
      ly === iNil
      merged === lx)
    (fresh $ \x xs y ys ms -> do
       iCons x xs === lx
       iCons y ys === ly
       conde
         (do
            leqo x y (iS iZ)
            merge xs ly ms
            iCons x ms === merged)
         (do
            leqo x y iZ
            merge lx ys ms
            iCons y ms === merged))

-- x <= y -> 1
-- x > y  -> 0
leqo
  :: (NatF :<: LFunctor k, TypeI (Term1 k) Nat)
  => Term k Nat
  -> Term k Nat
  -> Term k Nat
  -> Predicate k
leqo x y res = do
  conde
    (do
      x === iZ
      y === iZ
      res === iS iZ)
    (do
      x === iZ
      res === iS iZ)
    (do
      y === iZ
      res === iZ)
    (fresh $ \x' y' -> do
      x === iS x'
      y === iS y'
      leqo x' y' res)

