module Chap6

import Data.Vect

-- 6.2.3.2
data Format = Number Format
            | Str Format
            | Lit String Format
            | Cha Format
            | Dou Format
            | End

PrintfType : Format -> Type
PrintfType (Number x) = Int -> PrintfType x
PrintfType (Str x) = String -> PrintfType x
PrintfType (Cha x) = Char -> PrintfType x
PrintfType (Dou x) = Double -> PrintfType x
PrintfType (Lit x y) = PrintfType y
PrintfType End = String


printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number x) acc = \n => printfFmt x (acc ++ show n)
printfFmt (Str x) acc = \s => printfFmt x (acc ++ s)
printfFmt (Cha x) acc = \c => printfFmt x (acc ++ cast c)
printfFmt (Dou x) acc = \d => printfFmt x (acc ++ show d)
printfFmt (Lit x y) acc = printfFmt y (acc ++ x)
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Cha (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Dou (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                          Lit lit chars' => Lit (strCons c lit) chars'
                          fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

-- 6.2.3.3
TupleVect : (num : Nat) -> (ty : Type) -> Type
TupleVect Z ty = ()
TupleVect (S k) ty = (ty, TupleVect k ty)



-- 6.3.8
infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)


record DataStore  where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)



addToStore : (store : DataStore) -> (SchemaType (schema store)) -> DataStore
addToStore (MkData schema size items) y = MkData schema _ (addToData items)
  where
    addToData : Vect old (SchemaType schema) ->
                Vect (S old) (SchemaType schema)
    addToData [] = [y]
    addToData (x :: xs) = x :: addToData xs


data Command : Schema -> Type where
  SetSchema : (newSchema : Schema) -> Command schema
  Add : SchemaType schema -> Command schema
  Get : Maybe Integer -> Command schema
  Quit : Command schema


parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString item = getQuoted (unpack item)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) = case span (/= '"') xs of
                              (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
                              _ => Nothing
    getQuoted _ = Nothing

parsePrefix SInt item = case span isDigit item of
                          ("", rest) => Nothing
                          (num, rest) => Just (cast num, ltrim rest)
parsePrefix SChar item = getSingleQuoted (unpack item)
  where
    getSingleQuoted : List Char -> Maybe (Char, String)
    getSingleQuoted ('\'' :: c :: '\'' :: xs) = Just (c, ltrim (pack xs))
    getSingleQuoted _ = Nothing

parsePrefix (x .+. y) item = do (a, rem1) <- parsePrefix x item
                                (b, rem2) <- parsePrefix y rem1
                                Just ((a, b), rem2)


parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema x = case parsePrefix schema x of
                              Nothing => Nothing
                              (Just (res, "")) => Just res
                              Just _ => Nothing


parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) =
  case xs of
    [] => Just SString
    _ => case parseSchema xs of
           Nothing => Nothing
           Just xs_sch => Just (SString .+. xs_sch)
parseSchema ("Int" :: xs) =
  case xs of
    [] => Just SInt
    _ => case parseSchema xs of
           Nothing => Nothing
           Just xs_sch => Just (SInt .+. xs_sch)
parseSchema ("Char" :: xs) =
  case xs of
    [] => Just SChar
    _ => case parseSchema xs of
           Nothing => Nothing
           Just xs_sch => Just (SChar .+. xs_sch)
parseSchema _ = Nothing


parseCommand : (schema : Schema) -> List String -> Maybe (Command schema)
parseCommand schema ("add" :: str) =
  case parseBySchema schema (unwords str) of
    Nothing => Nothing
    Just restok => Just (Add restok)

parseCommand schema ["get", val] =
  case all isDigit (unpack val) of
    False => Nothing
    True => Just (Get (Just (cast val)))

parseCommand schema ["get"] = Just (Get Nothing)

parseCommand schema ("schema" :: rest) =
  case parseSchema rest of
    Nothing => Nothing
    Just schemaok => Just (SetSchema schemaok)
parseCommand schema ["quit"] = Just Quit
parseCommand _ _ = Nothing

parse : (schema : Schema ) -> (input : String) -> Maybe (Command schema)
parse schema input = parseCommand schema (words input)


display : SchemaType schema -> String
display {schema = SString} x = show x
display {schema = SInt} x = show x
display {schema = SChar} x = show x
display {schema = (y .+. z)} (a, b) = display a ++ ", " ++ display b

getEntry : (x : Maybe Integer) -> (store : DataStore) -> (inp : String) -> Maybe (String, DataStore)
getEntry (Just x) store inp = let store_items = items store in
                               (case integerToFin x (size store) of
                                 Nothing => Just ("Out of range\n", store)
                                 (Just x) => Just (display (index x store_items) ++ "\n", store))
getEntry Nothing store inp = let store_items = items store in
                               Just (concat (intersperse "\n" (map display store_items)) ++ "\n", store)

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                      Z => Just (MkData schema _ [])
                      S _ => Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse (schema store) inp of
                           Nothing => Just ("Invalid command\n", store)
                           (Just (Add x)) => Just ("ID " ++ show (size store) ++ "\n", addToStore store x)
                           (Just (Get x)) => getEntry x store inp
                           (Just (SetSchema schema')) =>
                             case setSchema store schema' of
                               Nothing => Just ("Cannot update schema\n", store)
                               Just store' => Just ("OK\n", store')
                           (Just Quit) => Nothing



main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
