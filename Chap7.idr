module Chap7

-- 7.1.6
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

Eq Shape where
    (==) (Triangle x z) (Triangle x' z') = x == x' && z == z'
    (==) (Rectangle x z) (Rectangle x' z') = x == x' && z == z'
    (==) (Circle x) (Circle x') = x == x'
    (==) _ _ = False

area : Shape -> Double
area (Triangle x y) = x * y * 0.5
area (Rectangle x y) = x * y
area (Circle x) = pi * x * x

Ord Shape where
    compare x y = let x_shape = area x
                      y_shape = area y
                  in compare x_shape y_shape

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

eval : (Neg num, Integral num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs (eval x)

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub
  abs = Abs

-- 7.2.4.1
Show ty => Show (Expr ty) where
    show (Val x) = show x
    show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
    show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
    show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
    show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
    show (Abs x) = "|" ++ show x ++ "|"

-- 7.2.4.2
(Eq ty, Integral ty, Num ty, Neg ty) => Eq (Expr ty) where
    (==) x y = eval x == eval y

(Neg num, Integral num) => Cast (Expr num) num where
    cast orig = eval orig

-- 7.3.4.1
Functor Expr where
    map f (Val x) = Val (f x)
    map f (Add x y) = Add (map f x) (map f y)
    map f (Sub x y) = Sub (map f x) (map f y)
    map f (Mul x y) = Mul (map f x) (map f y)
    map f (Div x y) = Div (map f x) (map f y)
    map f (Abs x) = Abs (map f x)

-- 7.3.4.2
data Vect : Nat -> Type -> Type where
  Nil : Vect Z elem
  Cons : elem -> Vect n elem -> Vect (S n) elem

Eq elem => Eq (Vect n elem) where
    (==) [] [] = True
    (==) (Cons x z) (Cons y w) = x == y && z == w

Foldable (Vect n) where
    foldr f acc [] = acc
    foldr f acc (Cons x y) = f x (foldr f acc y)
