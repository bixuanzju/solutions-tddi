module Chap11

%default total

-- Exercise 1

every_other : Stream Integer -> Stream Integer
every_other (num1 :: (num2 :: nums)) = num2 :: every_other nums

-- Exercise 2

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem


Functor InfList where
  map f (x :: xs) = f x :: map f xs


-- Exercise 3

data Face = Heads | Tails


getFace : Int -> Face
getFace x = if x > 0 then Heads else Tails

coinFaces : (count : Nat) -> Stream Int -> List Face
coinFaces Z xs = []
coinFaces (S k) (value :: xs) = getFace value :: coinFaces k xs


-- Exercise 4

square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx =
  approx :: square_root_approx number ((approx + (number / approx)) / 2)


square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) -> (approxs : Stream Double) -> Double
square_root_bound Z number bound (value :: xs) = value
square_root_bound (S k) number bound (val :: xs) =
  if abs (val * val - number) < bound
  then val
  else square_root_bound k number bound xs

square_root : (number : Double) -> Double
square_root number = square_root_bound 100 number 0.00000000001 (square_root_approx number number)


data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO


loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg) (\_ => loopPrint msg)


data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do


-- Exercise

totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action = do
  putStr prompt
  input <- getLine
  putStrLn (action input)
  totalREPL prompt action


greet : InfIO
greet = do
  putStrLn "Enter your name: "
  name <- getLine
  putStrLn $ "Hello " ++ name
  greet


data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  ReadFile : String -> Command (Either FileError String)
  WriteFile : String -> String -> Command (Either FileError ())

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  DoC : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = DoC


runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (ReadFile x) = readFile x
runCommand (WriteFile x y) = writeFile x y
runCommand (Pure val) = pure val
runCommand (Bind c f) = do res <- runCommand c
                           runCommand (f res)

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind


run : Fuel -> ConsoleIO a -> IO (Maybe a)
run fuel (Quit val) = pure (Just val)
run Dry (DoC c f) = pure Nothing
run (More fuel) (DoC c f) = do res <- runCommand c
                               run fuel (f res)


data Input = Answer Int | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                      then Pure QuitCmd
                      else Pure (Answer (cast answer))


-- Exercise 1

quiz : Stream Int -> (score : Nat) -> (num : Nat) -> ConsoleIO Nat
quiz (num1 :: (num2 :: nums)) score num = do
  PutStr $ "Score so far: " ++ show score ++ " / " ++ show num ++ "\n"
  input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
  (case input of
        (Answer answer) => if answer == num1 * num2
                           then do PutStr "Correct!\n"
                                   quiz nums (score + 1) (num + 1)
                           else do PutStr ("Wong, the answer is " ++ show answer ++ "\n")
                                   quiz nums score (num + 1)
        QuitCmd => Quit score)



-- Exercise 3

data ShellInp = Cat String | Copy String String | QuitShell | InvalidCmd String


readShellInp : Command ShellInp
readShellInp = do
  PutStr "> "
  str <- GetLine
  if toLower str == "exit"
  then Pure QuitShell
  else process (words str)
 where
    process : List String -> Command ShellInp
    process ["cat", filename] = Pure $ Cat filename
    process ["copy", source, dest] = Pure $ Copy source dest
    process x = Pure $ InvalidCmd $ unwords x


shell : ConsoleIO ()
shell = do
  input <- readShellInp
  case input of
        Cat x => do
          Right r <- ReadFile x
            | Left _ => do
               PutStr $ "Invalid filepath: " ++ x ++ "\n"
               shell
          PutStr r
          shell
        Copy x y => do
          Right r <- ReadFile x
            | Left _ => do
                PutStr $ "Invalid filepath: " ++ x ++ "\n"
                shell
          Right l <- WriteFile y r
            | Left _ => do
                PutStr $ "Invalid filepath: " ++ y ++ "\n"
                shell
          shell
        QuitShell => Quit ()
        InvalidCmd x => do
          PutStr $ "Invalid command: " ++ x ++ "\n"
          shell
