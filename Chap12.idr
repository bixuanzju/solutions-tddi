
import Control.Monad.State
import Data.Primitives.Views

%default total

data Tree a = Empty | Node (Tree a) a (Tree a)


testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred" (Node Empty "Shelia" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))


flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right



treeLabelWith : Tree a -> State (Stream b) (Tree (b, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node left val right) = do
  left_labelled <- treeLabelWith left
  (this :: rest) <- get
  put rest
  right_labelled <- treeLabelWith right
  pure (Node left_labelled (this, val) right_labelled)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = evalState (treeLabelWith tree) [1..]

-- Exercise

update : (a -> a) -> State a ()
update f = do
  s <- get
  put (f s)

increase : Nat -> State Nat ()
increase inc = update (+inc)


-- Exercise 2

countEmpty : Tree a -> State Nat ()
countEmpty Empty = update (+1)
countEmpty (Node left val right) = do
  countEmpty left
  countEmpty right

-- Exercise 3

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = do
  (a, b) <- get
  put (a + 1, b)
countEmptyNode (Node left val right) = do
  countEmptyNode left
  (a, b) <- get
  put (a, b+1)
  countEmptyNode right

record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int


initState : GameState
initState = MkGameState (MkScore 0 0) 12


Show GameState where
  show st = show (correct (score st)) ++ "/" ++
            show (attempted (score st)) ++ "\n" ++
            "Difficulty: " ++ show (difficulty st)

addWrong : GameState -> GameState
addWrong = record { score->attempted $= (+1) }

addCorrect : GameState -> GameState
addCorrect = record { score->correct $= (+1)
                    , score->attempted $= (+1)
                    }


data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  GetGameState : Command GameState
  PutGamaState : GameState -> Command ()

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

-- Exercise 2

Functor Command where
  map func c = Bind c (\a => Pure (func a))

Applicative Command where
  pure = Pure
  (<*>) x y = Bind x (\x' => Bind y (\y' => Pure (x' y')))

Monad Command where
  (>>=) = Bind


data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  DoC : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = DoC


data Input = Answer Int | QuitCmd


mutual
  correct : ConsoleIO GameState
  correct = do
    PutStr "Correct!\n"
    st <- GetGameState
    PutGamaState (addCorrect st)
    quiz

  wrong : Int -> ConsoleIO GameState
  wrong ans = do
    PutStr $ "Wrong, the answer is " ++ show ans ++ "\n"
    st <- GetGameState
    PutGamaState (addWrong st)
    quiz

  readInput : (prompt : String) -> Command Input
  readInput prompt = do PutStr prompt
                        answer <- GetLine
                        if toLower answer == "quit"
                        then Pure QuitCmd
                        else Pure (Answer (cast answer))

  quiz : ConsoleIO GameState
  quiz = do
    num1 <- GetRandom
    num2 <- GetRandom
    st <- GetGameState
    PutStr (show st ++ "\n")

    input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
    case input of
      Answer answer => if answer == num1 * num2
                       then correct
                       else wrong (num1 * num2)
      QuitCmd => Quit st


runCommand : Stream Int -> GameState -> Command a -> IO (a, Stream Int, GameState)
runCommand rnds state (PutStr x) = do
  putStr x
  pure ((), rnds, state)
runCommand rnds state GetLine = do
  res <- getLine
  pure (res, rnds, state)
runCommand (val :: rnds) state GetRandom =
    pure (getRandom val (difficulty state), rnds, state)
  where
    getRandom : Int -> Int -> Int
    getRandom val max with (divides val max)
      getRandom val 0 | DivByZero = 1
      getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1

runCommand rnds state GetGameState = pure (state, rnds, state)
runCommand rnds state (PutGamaState x) = pure ((), rnds, x)
runCommand rnds state (Pure x) = pure (x, rnds, state)
runCommand rnds state (Bind x f) = do
  (res, newRnds, newState) <- runCommand rnds state x
  runCommand newRnds newState (f res)

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever


run : Fuel -> Stream Int -> GameState -> ConsoleIO a -> IO (Maybe a, Stream Int, GameState)
run fuel rnds state (Quit x) = pure (Just x, rnds, state)
run Dry rnds state (DoC y f) = pure (Nothing, rnds, state)
run (More fuel) rnds state (DoC c f) = do
  (res, newRnds, newState) <- runCommand rnds state c
  run fuel newRnds newState (f res)


-- Exercise
updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = do
  st <- GetGameState
  PutGamaState (f st)




partial
main : IO ()
main = do
  (Just score, _, state) <- run forever [1..] initState quiz
    | _ => putStrLn "Ran out of fuel"
  putStrLn $ "Final score: " ++ show state
