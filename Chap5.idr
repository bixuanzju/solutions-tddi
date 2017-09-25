module Chap5

import Data.Vect


readVectLen : (len : Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) = do x <- getLine
                       xs <- readVectLen k
                       pure (x :: xs)


data VectUnknown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnknown a


readVect : IO (VectUnknown String)
readVect = do x <- getLine
              if (x == "")
              then pure (MkVect _ [])
              else do MkVect _ xs <- readVect
                      pure (MkVect _ (x :: xs))


printVect : Show a => VectUnknown a -> IO ()
printVect (MkVect len xs) = putStrLn (show xs ++ " (length " ++ show len ++ ")")

readVect2 : IO (len ** Vect len String)
readVect2 = do x <- getLine
               if (x == "")
               then pure (_ ** [])
               else do (_ ** xs) <- readVect2
                       pure (_ ** x :: xs)


zipInputs : IO ()
zipInputs = do putStrLn "Enter first vector (blank line to end):"
               (len1 ** vec1) <- readVect2
               putStrLn "Enter second vector (blank line to end):"
               (len2 ** vec2) <- readVect2
               case exactLength len1 vec2 of
                     Nothing => putStrLn "Vectors are different lengths"
                     Just vec2' => printLn (zip vec1 vec2')


readToBlank : IO (List String)
readToBlank = do x <- getLine
                 if x == ""
                 then pure []
                 else do xs <- readToBlank
                         pure (x :: xs)

readAndSave : IO ()
readAndSave = do xs <- readToBlank
                 putStrLn "Enter a filename:"
                 fname <- getLine
                 Right _ <- writeFile fname (unlines xs)
                   | Left err => putStrLn (show err)
                 pure ()

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right h <- openFile filename Read
    | Left err => pure (_ ** [])
  xs <- readVectFromFile h
  closeFile h
  pure xs
 where
    readVectFromFile : File -> IO (n ** Vect n String)
    readVectFromFile h = do
      b <- fEOF h
      if b then pure (_ ** [])
      else do Right x <- fGetLine h
                | Left err => pure (_ ** [])
              (_ ** xs) <- readVectFromFile h
              pure (_ ** (x :: xs))
