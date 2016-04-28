module Chap8

-- import Data.Vect

data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a


data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
     Same : (num : Nat) -> EqNat num num


sameS : (x : EqNat k j) -> EqNat (S k) (S j)
sameS {k = j} {j = j} (Same j) = Same (S j)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same 0)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just x) => Just (sameS x)


exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case checkEqNat m len of
                             Nothing => Nothing
                             (Just (Same m)) => Just input

-- 8.1.7.1
same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons Refl = Refl

-- 8.1.7.2
same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl Refl = Refl

-- 8.1.7.3
data ThreeEq : a -> b -> c -> Type where
  Refl3 : ThreeEq x x x

-- 8.1.7.4
allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x Refl3 = Refl3

reverseProof : Vect (k + 1) elem -> Vect (S k) elem
reverseProof {k} xs = rewrite plusCommutative 1 k in xs

-- 8.2.6.1
my_plusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
my_plusCommutes Z m = sym (plusZeroRightNeutral m)
my_plusCommutes (S k) m = let result = my_plusCommutes k m in
                          rewrite result in (plusSuccRightSucc m k)


-- 8.2.6.2
reverseProof_xs : Vect ((S n) + k) a -> Vect (plus n (S k)) a
reverseProof_xs {n} {k} xs = rewrite sym (plusSuccRightSucc n k) in xs

my_reverse : Vect n a -> Vect n a
my_reverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n + m) a
        reverse' {n} acc [] = rewrite (plusZeroRightNeutral n) in acc
        reverse' acc (x :: xs) = reverseProof_xs (reverse' (x :: acc) xs)


twoplustwo : 2 + 2 = 5 -> Void
twoplustwo Refl impossible

zero_not_suc : (0 = S k) -> Void
zero_not_suc Refl impossible

suc_not_zero : (S k = 0) -> Void
suc_not_zero Refl impossible

no_rec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
no_rec contra Refl = contra Refl

checkEqNatDec : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNatDec Z Z = Yes Refl
checkEqNatDec Z (S k) = No zero_not_suc
checkEqNatDec (S k) Z = No suc_not_zero
checkEqNatDec (S k) (S j) = case checkEqNatDec k j of
                                 (Yes prf) => Yes (cong prf)
                                 (No contra) => No (no_rec contra)

-- 8.3.4.1
head_unequal : DecEq a => {xs : Vect n a} -> {ys : Vect m a} ->
               (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
head_unequal contra Refl = contra Refl

tail_unequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
               (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tail_unequal contra Refl = contra Refl


-- 8.3.4.2
DecEq a => DecEq (Vect n a) where
    decEq [] [] = Yes Refl
    decEq (x :: y) (z :: w) = case decEq x z of
                                   (Yes Refl) => (case decEq y w of
                                                      (Yes Refl) => Yes Refl
                                                      (No contra) => No (tail_unequal contra))
                                   (No contra) => No (head_unequal contra)
