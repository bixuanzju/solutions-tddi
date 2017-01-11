
data ListLast : List a -> Type where
     Empty : ListLast []
     NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describe_help : Show a => (input : List a) -> (form : ListLast input) -> String
describe_help [] Empty = "Empty"
describe_help (xs ++ [x]) (NonEmpty xs x) = "Non-empty: initial portion = " ++ show xs

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          (NonEmpty ys y) => NonEmpty (x :: ys) y

describe_list_end : List Int -> String
describe_list_end [] = ?describe_list_end_rhs_1
describe_list_end (x :: xs) = ?describe_list_end_rhs_2
