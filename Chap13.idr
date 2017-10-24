import Data.Vect


%default total


-- Exercise 2

data GuessCmd : Type -> Nat -> Nat -> Type where
  Try : Integer -> GuessCmd Ordering (S n) n

  PureG : ty -> GuessCmd ty state state
  Bind : GuessCmd a state1 state2 -> (a -> GuessCmd b state2 state3) -> GuessCmd b state1 state3

namespace GuessDo
  (>>=) : GuessCmd a state1 state2 -> (a -> GuessCmd b state2 state3) -> GuessCmd b state1 state3
  (>>=) = Bind

threeGuess : GuessCmd () 3 0
threeGuess = do Try 10
                Try 20
                Try 15
                PureG ()

-- Exercise 3

data Matter = Solid | Liquid | Gas

data MatterCmd : Type -> Matter -> Matter -> Type where
  Melt : MatterCmd () Solid Liquid
  Boil : MatterCmd () Liquid Gas
  Freeze : MatterCmd () Liquid Solid
  Condense : MatterCmd () Gas Liquid

  PureM : ty -> MatterCmd ty state state
  BindM : MatterCmd a state1 state2 -> (a -> MatterCmd b state2 state3) -> MatterCmd b state1 state3

namespace MatterDo
  (>>=) : MatterCmd a state1 state2 -> (a -> MatterCmd b state2 state3) -> MatterCmd b state1 state3
  (>>=) = BindM


iceSteam : MatterCmd () Solid Gas
iceSteam = do Melt
              Boil

steamIce : MatterCmd () Gas Solid
steamIce = do Condense
              Freeze


data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)

  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height

  PureS : ty -> StackCmd ty height height
  (>>=) : StackCmd a height1 height2 -> (a -> StackCmd b height2 height3) -> StackCmd b height1 height3

namespace StackDo

  Pure : ty -> StackCmd ty height height
  Pure = PureS


testAdd : StackCmd Integer 0 0
testAdd = do
  Push 10
  Push 20
  val1 <- Pop
  val2 <- Pop
  Pure (val1 + val2)

runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           IO (ty, Vect outHeight Integer)
runStack stk (Push val) = pure (() , val :: stk)
runStack (val :: stk) Pop = pure (val, stk)
runStack (val :: stk) Top = pure (val, val :: stk)
runStack stk GetStr = do
  str <- getLine
  pure (str, stk)
runStack stk (PutStr x) = do
  putStr x
  pure ((), stk)
runStack stk (PureS x) = pure (x, stk)
runStack stk (cmd >>= next) = do
  (cmdRes, newStk) <- runStack stk cmd
  runStack newStk (next cmdRes)

doArith : (Integer -> Integer -> Integer) -> StackCmd () (S (S height)) (S height)
doArith op = do
  val1 <- Pop
  val2 <- Pop
  Push (op val2 val1)


data StackIO : Nat -> Type where
  Do : StackCmd a height1 height2 -> (a -> Inf (StackIO height2)) -> StackIO height1


namespace StackDo
  (>>=) : StackCmd a height1 height2 -> (a -> Inf (StackIO height2)) -> StackIO height1
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever


run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry xs y = pure ()
run (More fuel) stk (Do cmd next) = do
  (res, newStk) <- runStack stk cmd
  run fuel newStk (next res)


data StkInput = Number Integer | Add | Sub | Mul | Neg | Dis | Dup

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Sub
strToInput "multiply" = Just Mul
strToInput "negate" = Just Neg
strToInput "discard" = Just Dis
strToInput "duplicate" = Just Dup
strToInput x = if all isDigit (unpack x) then Just (Number (cast x)) else Nothing

mutual
  tryArith : (Integer -> Integer -> Integer) -> StackIO height
  tryArith {height = S (S h)} op = do
    doArith op
    result <- Top
    PutStr $ show result ++ "\n"
    stackCalc
  tryArith _ = do
    PutStr "Fewer than two items on the stack\n"
    stackCalc

  tryNeg : StackIO height
  tryNeg {height = S h} = do
    res <- Pop
    Push (-res)
    result <- Top
    PutStr $ show result ++ "\n"
    stackCalc
  tryNeg = do
    PutStr "Fewer than one item on the stack\n"
    stackCalc

  tryDis : StackIO height
  tryDis {height = Z} = do
    PutStr "No item on the stack to discard\n"
    stackCalc
  tryDis {height = (S k)} = do
    res <- Pop
    PutStr $ "Discarded " ++ show res ++ "\n"
    stackCalc

  tryDup : StackIO height
  tryDup {height = Z} = do
    PutStr "No item on the stack to duplicate\n"
    stackCalc
  tryDup {height = (S k)} = do
    res <- Top
    Push res
    PutStr $ "Duplicated " ++ show res ++ "\n"
    stackCalc



  stackCalc : StackIO height
  stackCalc = do
    PutStr "> "
    input <- GetStr
    case strToInput input of
      Nothing => do PutStr "Invalid input\n"
                    stackCalc
      Just (Number x) => do Push x
                            stackCalc
      Just Add => tryArith (+)
      Just Sub => tryArith (-)
      Just Mul => tryArith (*)
      Just Neg => tryNeg
      Just Dis => tryDis
      Just Dup => tryDup

partial
main : IO ()
main = run forever [] stackCalc
