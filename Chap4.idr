module Chap4

import Data.Vect

data Tree a = Empty
            | Node (Tree a) a (Tree a)

%name Tree left, right

insert : Ord a => a -> Tree a -> Tree a
insert x Empty = Node Empty x Empty
insert x t@(Node left y right) = case compare x y of
                                    LT => Node (insert x left) y right
                                    EQ => t
                                    GT => Node left y (insert x right)



-- 4.1.5.1
listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)

-- 4.1.5.2
treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node left x right) = treeToList left ++ (x :: treeToList right)

-- 4.1.5.3
data Expr = Lit Int
          | Addr Expr Expr
          | Sub Expr Expr
          | Mult Expr Expr

-- 4.1.5.4
evaluate : Expr -> Int
evaluate (Lit x) = x
evaluate (Addr x y) = evaluate x + evaluate y
evaluate (Sub x y) = evaluate x - evaluate y
evaluate (Mult x y) = evaluate x * evaluate y

-- 4.1.5.5
maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = case compare x y of
                                  LT => Just y
                                  EQ => Just x
                                  GT => Just x

-- 4.2.4.4
my_take : (n : Nat) -> Vect (n + m) a -> Vect n a
my_take Z xs = []
my_take (S k) (x :: xs) = x :: my_take k xs

-- 4.2.4.5
sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
                                Nothing => Nothing
                                (Just x) => Just (index x xs + index x ys)

-- 4.3.5
data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size items) = size

items : (store : DataStore) -> Vect (size store) String
items (MkData size items) = items

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) y = MkData _ (addToData items)
  where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [y]
    addToData (x :: xs) = x :: addToData xs

data Command = Add String | Get Integer | Size | Search String | Quit


parseCommand : List String -> Maybe Command
parseCommand ("add" :: str) = Just (Add (unwords str))
parseCommand ["get", val] = case all isDigit (unpack val) of
                                False => Nothing
                                True => Just (Get (cast val))
parseCommand ["size"] = Just Size
parseCommand ("search" :: str) = Just (Search (unwords str))
parseCommand ["quit"] = Just Quit
parseCommand _ = Nothing

parse : (input : String) -> Maybe Command
parse input = parseCommand (words input)


getEntry : (x : Integer) -> (store : DataStore) -> (inp : String) -> Maybe (String, DataStore)
getEntry x store inp = let store_items = items store in
                           (case integerToFin x (size store) of
                                 Nothing => Just ("Out of range\n", store)
                                 (Just x) => Just (index x store_items ++ "\n", store))

searchSubStr : (str : String) -> (store : DataStore) -> Maybe (String, DataStore)
searchSubStr str store =
  let store_items = items store
      match_items = filter (Strings.isInfixOf str) store_items
  in case match_items of
       (x ** pf) => Just ("The result is: "  ++ concat (intersperse ", " pf) ++ "\n", store)



processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse inp of
                              Nothing => Just ("Invalid command\n", store)
                              (Just (Add x)) => Just ("ID " ++ show (size store) ++ "\n", addToStore store x)
                              (Just (Get x)) => getEntry x store inp
                              (Just Size) => Just ("Size is: " ++ show (size store) ++ "\n", store)
                              (Just (Search str)) => searchSubStr str store
                              (Just Quit) => Nothing



main : IO ()
main = replWith (MkData _ []) "Command: " processInput
