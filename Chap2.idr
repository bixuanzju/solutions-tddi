module Chap2

-- 2
palindrome : String -> Bool
palindrome str = str == reverse str

-- 3
palindrome2 : String -> Bool
palindrome2 str = let str_lower = toLower str in
                      str_lower == reverse str_lower

-- 4
palindrome3 : String -> Bool
palindrome3 str = palindrome str && length str > 10

-- 5
palindrome4 : Nat -> String -> Bool
palindrome4 len str = palindrome str && length str > len
