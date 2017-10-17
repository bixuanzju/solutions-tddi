module Chap10

import Data.List.Views
import Data.Vect.Views
import Data.Nat.Views
import Data.Vect

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])


describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Non-empty, initial portion = " ++ show xs


total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          (NonEmpty ys y) => NonEmpty (x :: ys) y

describeListEnd : List Int -> String
describeListEnd xs with (listLast xs)
  describeListEnd [] | Empty = "Empty"
  describeListEnd (ys ++ [x]) | (NonEmpty ys x) = "Non-empty, initial portion = " ++ show ys


myReverse : List a -> List a
myReverse xs with (listLast xs)
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: (myReverse ys)

data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)


total
splitList : (xs : List a) -> SplitList xs
splitList xs = splitListHelp xs xs
  where
    splitListHelp : List a -> (input : List a) -> SplitList input
    splitListHelp _ [] = SplitNil
    splitListHelp _ [x] = SplitOne
    splitListHelp (_ :: _ :: counter) (item :: items)
      = case splitListHelp counter items of
             SplitNil => SplitOne
             SplitOne {x} => SplitPair [item] [x]
             (SplitPair lefts rights) => SplitPair (item :: lefts) rights
    splitListHelp _ items = SplitPair [] items


mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights)
    = merge (mergeSort lefts) (mergeSort rights)


-- Exercise 1

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             (Exact n_xs) => Exact (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest


-- Exercise 2

halves : List a -> (List a, List a)
halves xs with (takeN (length xs `div` 2) xs)
  halves xs | Fewer = (xs, xs) -- this case should be impossible
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)


-- data SnocList : List a -> Type where
--   SEmpty : SnocList []
--   Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])


-- snocListHelp : (snoc : SnocList input) -> (rest : List a) -> SnocList (input ++ rest)
-- snocListHelp {input = input} snoc [] = rewrite appendNilRightNeutral input in snoc
-- snocListHelp {input = input} snoc (x :: xs) =
--   rewrite appendAssociative input [x] xs in snocListHelp (Snoc snoc {x}) xs


-- snocList : (xs : List a) -> SnocList xs
-- snocList xs = snocListHelp SEmpty xs

myReverseHelper : (input : List a) -> SnocList input -> List a
myReverseHelper [] SEmpty = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

myReverse' : List a -> List a
myReverse' input with (snocList input)
  myReverse' [] | SEmpty = []
  myReverse' (xs ++ [x]) | (Snoc rec) = x :: myReverse' xs | rec


isSuffix : Eq a => List a -> List a -> Bool
isSuffix xs ys with (snocList xs)
  isSuffix [] ys | SEmpty = True
  isSuffix (zs ++ [x]) ys | (Snoc zsrec) with (snocList ys)
    isSuffix (zs ++ [x]) [] | (Snoc zsrec) | SEmpty = False
    isSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc zsrec) | (Snoc rec) =
      if x == y then isSuffix zs xs | zsrec | rec
      else False

mergeSort' : Ord a => List a -> List a
mergeSort' xs with (splitRec xs)
  mergeSort' [] | SplitRecNil = []
  mergeSort' [x] | SplitRecOne = [x]
  mergeSort' (lefts ++ rights) | (SplitRecPair lrec rrec)
    = merge (mergeSort' lefts | lrec) (mergeSort' rights | rrec)


-- Exercise 1

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys with (snocList xs)
  equalSuffix [] ys | Empty = []
  equalSuffix (zs ++ [x]) ys | (Snoc zsrec) with (snocList ys)
    equalSuffix (zs ++ [x]) [] | (Snoc zsrec) | Empty = []
    equalSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc zsrec) | (Snoc xsrec)
      = if x == y then equalSuffix zs xs | zsrec | xsrec ++ [x]
        else []

-- Exercise 2

total
mergeSortVect : Ord a => Vect n a -> Vect n a
mergeSortVect xs with (splitRec xs)
  mergeSortVect [] | SplitRecNil = []
  mergeSortVect [x] | SplitRecOne = [x]
  mergeSortVect (ys ++ zs) | (SplitRecPair lrec rrec)
    = merge (mergeSortVect ys | lrec) (mergeSortVect zs | rrec)


-- Exercise 3

total
toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = toBinary n | rec ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = toBinary n | rec ++ "1"


-- Exercise 4

total
palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec)
    = if x == y then palindrome ys | rec
      else False
