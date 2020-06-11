{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module List where

import Control.Arrow (first)
import Control.Monad (unless)
import qualified Control.Monad as Monad
import Data.Functor.Identity
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import qualified Data.Text.Lazy as T
import Language.HKanren.Functions.Sorts
import Language.HKanren.Functions.Trans
import Language.HKanren.Functions.List
import Language.HKanren.Functions.Nat
import Language.HKanren.Nondeterminism
import qualified Language.HKanren.SafeLVar as Safe
import Language.HKanren.Syntax
import Language.HKanren.Types.List
import Language.HKanren.Types.Nat
import Language.HKanren.Types.Pair
import Text.PrettyPrint.Leijen.Text (Pretty(..), displayT, renderPretty)
import qualified Text.PrettyPrint.Leijen.Text as PP
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck hiding ((===))

import LispLists

import Data.List (sortBy)
import Data.Ord (comparing)
import Data.String
import Prelude hiding ((>>), (>>=))


assertHEqual
  :: (HEq f, HEqHet f, HShow f)
  => String -- ^ prefix
  -> f ix   -- ^ The expected value
  -> f ix'  -- ^ The actual value
  -> Assertion
assertHEqual prefix actual expected =
  unless (actual ==* expected) (assertFailure msg)
  where
    msg = prefix ++ "expected: " ++ hshow expected ++ "\n but got: " ++ hshow actual

failingListTest
  :: forall ix. (TypeI (LispTermF LispTerm) ix)
  => String
  -> (LispTerm ix -> Predicate LispVar)
  -> TestTree
failingListTest testName query =
  testCase testName $
  case runIdentity $ runN nondetBreadthFirst 1 query of
    [] -> return ()
    _  -> assertFailure "predicate unexpectedly succeeded"

lispTest
  :: forall ix. (TypeI (LispTermF LispTerm) ix)
  => String
  -> Int
  -> (LispTerm ix -> Predicate LispVar)
  -> [LispTerm ix]
  -> TestTree
lispTest testName n query expectedAnswers =
  testCase testName $
  case runIdentity $ runN nondetBreadthFirst n query of
    []      -> assertFailure "no results"
    results -> checkSorted results expectedAnswers

checkSorted :: [(LispTerm ix, [Some (Neq LispVar)])] -> [LispTerm ix] -> Assertion
checkSorted results expectedAnswers = do
  unless (resultsCount == expectedAnswersCount) $
    assertFailure $ "expected " ++ show expectedAnswersCount ++ " results but got " ++ show resultsCount
  check (sortBy (comparing (Some . fst)) results) (sortBy (comparing Some) expectedAnswers)
  where
    (>>) = (Monad.>>)
    resultsCount = length results
    expectedAnswersCount = length expectedAnswers

check :: [(LispTerm ix, [Some (Neq LispVar)])] -> [LispTerm ix] -> Assertion
check xs ys = go xs ys
  where
    prefix = display $ PP.align ("results  = " <> pretty (map (first Some) xs)) PP.<$>
                       "|results|  = " <> pretty (length xs) PP.<$>
                       PP.align ("expected = " <> pretty (map Some ys)) PP.<$>
                       "|expected| = " <> pretty (length ys) <> PP.line
    go []          []     = return ()
    go ((t, _):rs) (a:as) = assertHEqual prefix t a Monad.>> go rs as
    go ((t, _):_)  []     = assertFailure $ "more results than answers, next result: " ++ hshow t
    go _           (a:_)  = assertFailure $ "no more results while expecting more answers, e.g.: " ++ hshow a

display :: (Pretty a) => a -> String
display = T.unpack . displayT . renderPretty 0.9 100 . pretty

appendTest
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> [LispTerm ix]
  -> [LispTerm ix]
  -> [LispTerm ix]
  -> TestTree
appendTest testName xs ys zs =
  lispTest
    testName
    1
    (\q -> appendo (list xs) (list ys) q)
    [list zs]

appendTests :: TestTree
appendTests = testGroup "append tests"
  [ appendTest
      "append 1d #1"
      ([] :: [LispTerm Atom])
      []
      []
  , appendTest
      "append 1d #2"
      []
      [iAtom "bar"]
      [iAtom "bar"]
  , appendTest
      "append 1d #3"
      [iAtom "foo"]
      []
      [iAtom "foo"]
  , appendTest
      "append 1d #4"
      [iAtom "foo"]
      [iAtom "bar"]
      [iAtom "foo", iAtom "bar"]
  , appendTest
      "append 1d #5"
      [iAtom "foo", iAtom "bar", iAtom "baz"]
      [iAtom "x", iAtom "y", iAtom "z"]
      [iAtom "foo", iAtom "bar", iAtom "baz", iAtom "x", iAtom "y", iAtom "z"]
  , lispTest
      "append 1d, infer input"
      1
      (\q -> appendo
               q
               (list [])
               (list [iAtom "foo", iAtom "bar"]))
      [list [iAtom "foo", iAtom "bar"]]
  , lispTest
      "append 1d, infer both inputs"
      3
      (\q -> fresh $ \x y -> do
          q ==^ Pair x y
          appendo
            x
            y
            (list [iAtom "foo", iAtom "bar"]))
      [ iPair (list []) (list [iAtom "foo", iAtom "bar"])
      , iPair (list [iAtom "foo"]) (list [iAtom "bar"])
      , iPair (list [iAtom "foo", iAtom "bar"]) (list [])
      ]
  -- , lispTest
  --     "append 1d, infer both inputs, termination"
  --     4
  --     (\q -> fresh $ \x y -> do
  --         q ==^ Pair x y
  --         appendo
  --           x
  --           y
  --           (list [iAtom "foo", iAtom "bar"]))
  --     [ iPair (list []) (list [iAtom "foo", iAtom "bar"])
  --     , iPair (list [iAtom "foo"]) (list [iAtom "bar"])
  --     , iPair (list [iAtom "foo", iAtom "bar"]) (list [])
  --     ]
  , appendTest
      "append 2d #1"
      [ list [iAtom "foo"]
      , list [iAtom "bar", iAtom "baz"]
      ]
      [ list [iAtom "x", iAtom "y"]
      , list [iAtom "z"]
      ]
      [ list [iAtom "foo"]
      , list [iAtom "bar", iAtom "baz"]
      , list [iAtom "x", iAtom "y"]
      , list [iAtom "z"]
      ]
  , lispTest
      "append 2d, infer input"
      1
      (\q -> appendo
               (list
                 [ list [iAtom "foo"]
                 , list [iAtom "bar", iAtom "baz"]
                 ])
               q
               (list
                 [ list [iAtom "foo"]
                 , list [iAtom "bar", iAtom "baz"]
                 , list [iAtom "x", iAtom "y"]
                 , list [iAtom "z"]
                 ]))
      [list [ list [iAtom "x", iAtom "y"]
            , list [iAtom "z"]
            ]]
  ]

succeedingMemberTest
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> LispTerm ix
  -> [LispTerm ix]
  -> TestTree
succeedingMemberTest name x xs =
  lispTest
    name
    1
    (\q -> do
      member x xs'
      x === q)
    [x]
  where
    xs' = list xs

failingMemberTest
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> LispTerm ix
  -> [LispTerm ix]
  -> TestTree
failingMemberTest name x xs =
  failingListTest
    name
    (\q -> do
      member x xs'
      x === q)
  where
    xs' = list xs

memberQuery
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> [LispTerm ix]
  -> [LispTerm ix]
  -> TestTree
memberQuery name xs expectedAnswers =
  lispTest
    name
    (length xs)
    (\q -> do
      member q xs')
    expectedAnswers
  where
    xs' = list xs

memberTests :: TestTree
memberTests = testGroup "append tests"
  [ succeedingMemberTest
      "member succeeds #1"
      (iAtom "foo")
      [iAtom "foo", iAtom "bar"]
  , succeedingMemberTest
      "member succeeds #2"
      (iAtom "bar")
      [iAtom "foo", iAtom "bar"]
  , failingMemberTest
      "member fails #1"
      (iAtom "baz")
      [iAtom "foo", iAtom "bar"]
  , memberQuery
      "member query #1"
      [iAtom "foo", iAtom "bar"]
      [iAtom "foo", iAtom "bar"]
  ]

plusoQuery
  :: String
  -> Int
  -> Int
  -> Int
  -> TestTree
plusoQuery testName x y expected =
  lispTest
    testName
    1
    (\q -> pluso (int2nat x) (int2nat y) q)
    [int2nat expected]

natTests :: TestTree
natTests = testGroup "nat tests"
  [ testGroup "pluso"
      [ plusoQuery "0 + 0 = 0" 0 0 0
      , plusoQuery "0 + 1 = 1" 0 1 1
      , plusoQuery "1 + 0 = 1" 1 0 1
      , plusoQuery "1 + 1 = 2" 1 1 2
      , plusoQuery "10 + 20 = 30" 10 20 30
      ]
  ]

-----------------------------------------------------------------------------------------------------

il2nl :: [Int] -> HFree (LFunctor LispVar) LispVar (List Nat)
il2nl = list . fmap int2nat

-------------------------------------------------
-------------------------------------------------

permSortTests :: TestTree
permSortTests = testGroup "perm sort tests"
  [ testGroup "trans"

      [ permSortIOQuery "3, 1" [3, 1] [1, 3]
      , permSortIOQuery "2" [2] [2]
      , permSortIOQuery "3, 2, 1" [3, 2, 1] [1, 2, 3]
      , permSortIOQuery "1..3" [1..3] [1..3]
      , permSortIOQuery "4, 3" [4, 3] [3, 4]
      , permSortIOQuery "1, 2" [1, 2] [1, 2]
      , permSortIOQuery "4, 1, 3, 2" [4, 1, 3, 2] [1..4]
      , permSortIOQuery "4, 6, 2, 5, 7" [4, 6, 2, 5, 7] [2, 4, 5, 6, 7]
      , permSortIOQuery "2, 4, 6, 2, 5, 7" [2, 4, 6, 2, 5, 7] [2, 2, 4, 5, 6, 7]
      , permSortIOQuery "25..1" [25,24..1] [1..25]
      , permSortIOQuery "30..1" [30,29..1] [1..30]
      , permSortIOQuery "40..1" [40,39..1] [1..40]
      , permSortIOQuery "45..1" [45,44..1] [1..45]
      , permSortIOQuery "50..1" [50,49..1] [1..50]
      , permSortIOQuery "53..1" [53,52..1] [1..53]
      , permSortIOQuery "54..1" [54,53..1] [1..54]
      , permSortIOQuery "55..1" [55,54..1] [1..55]
      , permSortIOQuery "60..1" [60,59..1] [1..60]
      , permSortIOQuery "70..1" [70,69..1] [1..70]
      , permSortIOQuery "80..1" [80,79..1] [1..80]
      , permSortIOQuery "90..1" [90,89..1] [1..90]
      , permSortIOQuery "100..1" [100,99..1] [1..100]
--      , permSortIOQuery "250,249..1" [250,249..1] [1..250]
--      , permSortIOQuery "500,499..1" [500,499..1] [1..500]
--      , permSortIOQuery "750,749" [750,749] [1..750]
      ]
  , testGroup "sort"
      [ permSortQuery "3, 1" [3, 1] [1, 3]
      , permSortQuery "2" [2] [2]
      , permSortQuery "3, 2, 1" [3, 2, 1] [1, 2, 3]
      , permSortQuery "1..3" [1..3] [1..3]
      , permSortQuery "4, 3" [4, 3] [3, 4]
      , permSortQuery "1, 2" [1, 2] [1, 2]
      , permSortQuery "4, 1, 3, 2" [4, 1, 3, 2] [1..4]
      , permSortQuery "4, 6, 2, 5, 7" [4, 6, 2, 5, 7] [2, 4, 5, 6, 7]
      , permSortQuery "2, 4, 6, 2, 5, 7" [2, 4, 6, 2, 5, 7] [2, 2, 4, 5, 6, 7]
      , permSortQuery "10..1" [10,9..1] [1..10]
      , permSortQuery "20..1" [20,19..1] [1..20]
      , permSortQuery "30..1" [30,29..1] [1..30]
      , permSortQuery "40..1" [40,39..1] [1..40]
--      , permSortQuery "25..1" [25,24..1] [1..25]
--      , permSortQuery "30..1" [30,29..1] [1..30]
--      , permSortQuery "40..1" [40,39..1] [1..40]
--      , permSortQuery "45..1" [45,44..1] [1..45]
--      , permSortQuery "50..1" [50,49..1] [1..50]
--      , permSortQuery "53..1" [53,52..1] [1..53]
      , permSortQuery "54..1" [54,53..1] [1..54]
--      , permSortQuery "55..1" [55,54..1] [1..55]
      ]

{-
  , testGroup "smallesto"
      [ smallestoQuery "[3, 1]" [3, 1] 1 [3]
      , smallestoQuery "[2]" [2] 2 []
      , smallestoQuery "[3, 2, 1]" [3, 2, 1] 1 [3, 2]
      , smallestoQuery "[1, 2]" [1, 2] 1 [2]
      , smallestoQuery "4, 1, 3, 2" [4, 1, 3, 2] 1 [4, 2, 3]
      , smallestoQuery "4, 6, 2, 5, 7" [4, 6, 2, 5, 7] 2 [4, 6, 5, 7]
      , smallestoQuery "2, 4, 6, 2, 5, 7" [2, 4, 6, 2, 5, 7] 2 [2, 4, 6, 5, 7]
      ]
  , testGroup "minmaxo"
      [ minmaxoQuery "1 2 -> 1 2" 1 2 1 2
      , minmaxoQuery "2 1 -> 1 2" 2 1 1 2
      , minmaxoQuery "2 2 -> 2 2" 2 2 2 2
      , minmaxoQuery "5 7 -> 5 7" 5 7 5 7
      , minmaxoQuery "7 5 -> 5 7" 7 5 5 7
      , minmaxoQuery "5 5 -> 5 5" 5 5 5 5
      ]
-}
  ]

permSortIOQuery
  :: String
  -> [Int]
  -> [Int]
  -> TestTree
permSortIOQuery testName l sorted =
  testCase testName $ permSortIO (fmap i2p l) @?= [(fmap i2p sorted)]

permSortQuery
  :: String
  -> [Int]
  -> [Int]
  -> TestTree
permSortQuery testName l sorted =
  lispTest
    testName
    1
    (\q -> permSort (il2nl l) q)
    [il2nl sorted]

smallestoQuery
  :: String
  -> [Int]
  -> Int
  -> [Int]
  -> TestTree
smallestoQuery testName l small restl =
  lispTest
    testName
    1
    (\q -> smallesto (il2nl l) (int2nat small) q)
    [il2nl restl]

minmaxoQuery
  :: String
  -> Int
  -> Int
  -> Int
  -> Int
  -> TestTree
minmaxoQuery testName a b min max =
  lispTest
    testName
    1
    (\q -> minmaxo (int2nat a) (int2nat b) (int2nat min) q)
    [int2nat max]

-------------------------------------------------
-------------------------------------------------

mergeSortTests :: TestTree
mergeSortTests = testGroup "merge sort tests"
  [ testGroup "sort"
      [ mergeSortQuery "3, 1" [3, 1] [1, 3]
      , mergeSortQuery "2" [2] [2]
      , mergeSortQuery "3, 2, 1" [3, 2, 1] [1, 2, 3]
      , mergeSortQuery "1..3" [1..3] [1..3]
      , mergeSortQuery "4, 3" [4, 3] [3, 4]
      , mergeSortQuery "1, 2" [1, 2] [1, 2]
      , mergeSortQuery "4, 1, 3, 2" [4, 1, 3, 2] [1..4]
--      , mergeSortQuery "4, 6, 2, 5, 7" [4, 6, 2, 5, 7] [2, 4, 5, 6, 7]
--      , mergeSortQuery "2, 4, 6, 2, 5, 7" [2, 4, 6, 2, 5, 7] [2, 2, 4, 5, 6, 7]
--      , mergeSortQuery "7, 6..1" [7, 6..1] [1..7]
      ]
  , testGroup "split"
      [ splitQuery "3, 2, 1" [3, 2, 1] [3, 1] [2]
      , splitQuery "3, 1" [3, 1] [3] [1]
      , splitQuery "2" [2] [2] []
      , splitQuery "4, 1, 3, 2" [4, 1, 3, 2] [4, 3] [1, 2]
      , splitQuery "3, 2" [3, 2] [3] [2]
      , splitQuery "[]" [] [] []
      , splitQuery "3, 4" [3, 4] [3] [4]
      , splitQuery "1..4" [1..4] [1, 3] [2, 4]
      , splitQuery "2, 4, 6, 2, 5, 7, 4" [2, 4, 6, 2, 5, 7, 4] [2, 6, 5, 4] [4, 2, 7]
      ]
  , testGroup "merge"
      [ mergeQuery "1,3 + 2" [1, 3] [2] [1..3]
      , mergeQuery "3 + 1" [3] [1] [1, 3]
      , mergeQuery "2 + ." [2] [] [2]
      , mergeQuery "3,4 + 1,2" [3, 4] [1, 2] [1..4]
      , mergeQuery "1..4 + ." [1..4] [] [1..4]
      , mergeQuery ". + 1..4" [] [1..4] [1..4]
      , mergeQuery "1 + 1" [1] [1] [1, 1]
      , mergeQuery "1.4..6 + 2,3" [1, 4, 5, 6] [2, 3] [1..6]
      , mergeQuery "2, 3, 4, 6, 6, 7, 8" [3, 6, 7] [2, 4, 6, 8] [2, 3, 4, 6, 6, 7, 8]
      , mergeQuery "1, 2, 3, 4, 5, 6, 7, 8, 9" [1, 5, 8, 9] [2, 3, 4, 6, 7] [1..9]
      , mergeQuery "1, 2, 3, 4, 5, 5, 6, 7, 8, 9" [1, 5, 8, 9] [2, 3, 4, 5, 6, 7] [1, 2, 3, 4, 5, 5, 6, 7, 8, 9]
      , mergeQuery "1, 2, 3, 4, 5, 6, 7, 7, 8, 9" [1, 8, 9] [2, 3, 4, 5, 6, 7, 7] [1, 2, 3, 4, 5, 6, 7, 7, 8, 9]
      ]
  , testGroup "x <= y (leq)"
      [ leqoQuery "1 2 -> 1" 1 2 1
      , leqoQuery "2 1 -> 0" 2 1 0
      , leqoQuery "2 2 -> 1" 2 2 1
      , leqoQuery "5 7 -> 1" 5 7 1
      , leqoQuery "7 5 -> 0" 7 5 0
      , leqoQuery "5 5 -> 1" 5 5 1
      ]
  ]

mergeSortQuery
  :: String
  -> [Int]
  -> [Int]
  -> TestTree
mergeSortQuery testName l sorted =
  lispTest
    testName
    1
    (\q -> mergeSort (il2nl l) q)
    [il2nl sorted]

splitQuery
  :: String
  -> [Int]
  -> [Int]
  -> [Int]
  -> TestTree
splitQuery testName l lx ly =
  lispTest
    testName
    10
    (\q -> fresh $ \x y -> do
        q ==^ Pair x y
        split x y (il2nl l))
    [ iPair (il2nl lx) (il2nl ly)]

mergeQuery
  :: String
  -> [Int]
  -> [Int]
  -> [Int]
  -> TestTree
mergeQuery testName lx ly merged =
  lispTest
    testName
    1
    (\q -> merge (il2nl lx) (il2nl ly) q)
    [il2nl merged]

leqoQuery
  :: String
  -> Int
  -> Int
  -> Int
  -> TestTree
leqoQuery testName x y expected =
  lispTest
    testName
    1
    (\q -> leqo (int2nat x) (int2nat y) q)
    [int2nat expected]

----------------------------------------------------------------------------------------------------

allUniqueQuery
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> [LispTerm ix]
  -> [LispTerm (List ix)]
  -> TestTree
allUniqueQuery name xs expectedAnswers =
  lispTest
    name
    (length expectedAnswers)
    (\q -> do
      allo (\x -> member x xs') q
      allUnique q)
    expectedAnswers
  where
    xs' = list xs

allUniqueTests :: TestTree
allUniqueTests = testGroup "append tests"
  [ allUniqueQuery
      "allUnique query #1"
      [iAtom "foo", iAtom "bar"]
      [ list []
      , list [iAtom "bar"]
      , list [iAtom "foo"]
      , list [iAtom "foo", iAtom "bar"]
      ]
  ]

hcompareIxTest :: (HOrdHet f) => String -> f ix -> f ix' -> Ordering -> TestTree
hcompareIxTest name x y expected =
  testCase name $
  assertEqual "" expected (hordering2ordering (hcompareIx x y))

-- lisp term ordered naturally
type OrderedLispTermF = AtomF :+: ListF
type OrderedLispTerm = Term (Safe.LVar OrderedLispTermF)

-- lisp term ordered unnatuarlly but this ordering should also be acceptable
type ReversedLispTermF = ListF :+: AtomF
type ReversedLispTerm = Term (Safe.LVar ReversedLispTermF)

ixComparisonTests :: TestTree
ixComparisonTests = testGroup "index comparison tests"
  [ hcompareIxTest
      "atom == atom"
      (Atom "foo")
      (Atom "bar")
      EQ
  , testGroup "naturally ordered term"
      [ hcompareIxTest
          "atom : LispType == atom : LispType"
          (iAtom "foo" :: OrderedLispTerm Atom)
          (iAtom "bar" :: OrderedLispTerm Atom)
          EQ
      , hcompareIxTest
          "atom < [atom]"
          (iAtom "foo" :: OrderedLispTerm Atom)
          (iNil        :: OrderedLispTerm (List Atom))
          LT
      , hcompareIxTest
          "[atom] > atom"
          (iNil        :: OrderedLispTerm (List Atom))
          (iAtom "foo" :: OrderedLispTerm Atom)
          GT
      , hcompareIxTest
          "[atom] == [atom]"
          (iNil :: OrderedLispTerm (List Atom))
          (iNil :: OrderedLispTerm (List Atom))
          EQ
      , hcompareIxTest
          "[atom] == [atom] #2"
          (iNil :: OrderedLispTerm (List Atom))
          (iCons (iAtom "foo")
                 (iNil) :: OrderedLispTerm (List Atom))
          EQ
      ]
  , testGroup "reversed term"
      [ hcompareIxTest
          "atom : LispType == atom : LispType"
          (iAtom "foo" :: ReversedLispTerm Atom)
          (iAtom "bar" :: ReversedLispTerm Atom)
          EQ
      , hcompareIxTest
          "atom < [atom]"
          (iAtom "foo" :: ReversedLispTerm Atom)
          (iNil        :: ReversedLispTerm (List Atom))
          GT
      , hcompareIxTest
          "[atom] > atom"
          (iNil        :: ReversedLispTerm (List Atom))
          (iAtom "foo" :: ReversedLispTerm Atom)
          LT
      , hcompareIxTest
          "[atom] == [atom]"
          (iNil :: ReversedLispTerm (List Atom))
          (iNil :: ReversedLispTerm (List Atom))
          EQ
      , hcompareIxTest
          "[atom] == [atom] #2"
          (iNil :: ReversedLispTerm (List Atom))
          (inj (iCons (iAtom "foo")
                      (iNil)) :: ReversedLispTerm (List Atom))
          EQ
      ]
  ]


listOrdInstanceTests :: TestTree
listOrdInstanceTests = testGroup "comparison instanes for lists"
  [ testCase "list of lists of atoms sorting with sortBy" $ do
      let xs :: [LispTerm (List Atom)]
          xs = [ list []
               , list [iAtom "bar"]
               , list [iAtom "foo"]
               , list [iAtom "foo", iAtom "bar"]
               ]
          ys = sortBy (comparing Some) xs
      assertEqual
        "sorted list has different number of items that unsorted one"
        (length xs)
        (length ys)
      assertBool "sorted list is not actually sorted" $ isSorted $ map Some ys
      assertBool "sorted list is not actually h-sorted" $ isHSorted ys
  ]
  where
    (>>) = (Monad.>>)

isSorted :: (Ord a) => [a] -> Bool
isSorted []            = True
isSorted [_]           = True
isSorted (x:xs@(x':_)) = x <= x' && isSorted xs

isHSorted :: (HOrd a) => [a ix] -> Bool
isHSorted []  = True
isHSorted [_] = True
isHSorted (x:xs@(x':_)) =
  case hcompare x x' of
    LT -> isHSorted xs
    EQ -> isHSorted xs
    GT -> False

main :: IO ()
main = defaultMain $
  adjustOption (const $ QuickCheckTests 10000) $
  adjustOption (const $ QuickCheckMaxSize 10000) $
  adjustOption (const $ mkTimeout 1000000000) $
  testGroup "List Tests"
    [ testGroup "functions"
        [
--          appendTests
--        , memberTests
--        , allUniqueTests
          mergeSortTests
        , permSortTests
        ]
--    , natTests
--    , ixComparisonTests
--    , listOrdInstanceTests
    ]

