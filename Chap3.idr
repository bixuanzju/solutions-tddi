module Chap3

import Data.Vect

-- 3.2.4.1
my_length : List a -> Nat
my_length [] = 0
my_length (x :: xs) = 1 + my_length xs

-- 3.2.4.2
my_reverse : List a -> List a
my_reverse xs = help [] xs
  where help : List a -> List a -> List a
        help acc [] = acc
        help acc (y :: ys) = help (y :: acc) ys

-- 3.2.4.3
list_map : (a -> b) -> List a -> List b
list_map f [] = []
list_map f (x :: xs) = f x :: list_map f xs

-- 3.2.4.4
vect_map : (a -> b) -> Vect n a -> Vect n b
vect_map f [] = []
vect_map f (x :: xs) = f x :: vect_map f xs

-- 3.3.3.1
create_empties : Vect n (Vect 0 elem)
create_empties = replicate _ []

transpose_mat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transpose_mat [] = create_empties
transpose_mat (x :: xs) = let xs_trans = transpose_mat xs in
                              zipWith (::) x xs_trans

-- 3.3.3.2
addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys

-- 3.3.3.3
helper : Num a => (xs : Vect n (Vect m a)) -> (trans_ys : Vect p (Vect m a)) -> Vect n (Vect p a)
helper [] trans_ys = []
helper (x :: xs) trans_ys =
  map (\y => sum (zipWith (*) x y)) trans_ys :: helper xs trans_ys

multiMatrix : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
multiMatrix xs ys = let trans_ys = transpose_mat ys in
                        helper xs trans_ys
