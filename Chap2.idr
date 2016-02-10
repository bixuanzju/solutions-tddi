module Chap2

-- 2.5.2
palindrome : String -> Bool
palindrome str = str == reverse str

-- 2.5.3
palindrome2 : String -> Bool
palindrome2 str = let str_lower = toLower str in
                      str_lower == reverse str_lower

-- 2.5.4
palindrome3 : String -> Bool
palindrome3 str = palindrome str && length str > 10

-- 2.5.5
palindrome4 : Nat -> String -> Bool
palindrome4 len str = palindrome str && length str > len

-- 2.5.6
-- Characters including space?
counts : String -> (Nat, Nat)
counts inp = (length (words inp), length inp)

-- 2.5.7
-- If less than 10, return the whole list (defualt behaviour of `take`)
top_ten : Ord a => List a -> List a
top_ten xs = take 10 (sort xs)

-- 2.5.8
over_length : Nat -> List String -> Nat
over_length len = length . filter (\s => length s > len)

-- 2.5.9
palindrome' : IO ()
palindrome' = repl "Enter a string: "
              (\s => "Is is a palindrome? " ++ show (palindrome s) ++ "\n")
