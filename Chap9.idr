module Chap9

import Data.Vect


oneInVector : Elem 3 [1,2,3]
oneInVector = There (There Here)



removeElem : (value : a) -> (xs : Vect (S n) a) -> (prf : Elem value xs) -> Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later) = y :: removeElem value ys later

not_in_tail : (noThere : Elem value xs -> Void) -> (contra : (value = x) -> Void) -> Elem value (x :: xs) -> Void
not_in_tail noThere contra Here = contra Refl
not_in_tail noThere contra (There later) = noThere later

isElem' : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (Elem value xs)
isElem' value [] = No uninhabited
isElem' value (x :: xs) = case decEq value x of
                              (Yes Refl) => Yes Here
                              (No contra) => (case isElem' value xs of
                                                   (Yes prf) => Yes (There prf)
                                                   (No noThere) => No (not_in_tail noThere contra))


-- 9.1.6.2

data Last : List a -> a -> Type where
     LastOne : Last [item] item
     LastCons : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [1,2,3] 3
last123 = LastCons (LastCons LastOne)

last_nil : Last [] value -> Void
last_nil LastOne impossible
last_nil (LastCons _) impossible

last_one_neq : (contra : (x = value) -> Void) -> Last [x] value -> Void
last_one_neq contra LastOne = contra Refl
last_one_neq contra (LastCons prf) = last_nil prf

last_cons : (contra : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
last_cons contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No last_nil
isLast [x] value = case decEq x value of
                        (Yes Refl) => Yes LastOne
                        (No contra) => No (last_one_neq contra)
isLast (x :: y :: xs) value = case isLast (y :: xs) value of
                                   (Yes prf) => Yes (LastCons prf)
                                   (No contra) => No (last_cons contra)
