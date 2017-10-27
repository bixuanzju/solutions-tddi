import Data.Vect


PIN : Type
PIN = Vect 4 Char


data ATMState = Ready | CardInserted | Session


data PINCheck = CorrectPIN | IncorrectPIN


data HasCard : ATMState -> Type where
  HasCI : HasCard CardInserted
  HasSession : HasCard Session


data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
  InsertCard : ATMCmd () Ready (const CardInserted)
  EjectCard : {auto pdf : HasCard state} -> ATMCmd () state (const Ready)
  GetPIN : ATMCmd PIN CardInserted (const CardInserted)
  CheckPIN : PIN -> ATMCmd PINCheck CardInserted (\check => case check of
                                                                 CorrectPIN => Session
                                                                 IncorrectPIN => CardInserted)
  GetAmount : ATMCmd Nat state (const state)
  Dispense : (amount : Nat) -> ATMCmd () Session (const Session)
  Message : String -> ATMCmd () state (const state)
  Pure : (res : ty) -> ATMCmd ty (state_fn res) state_fn
  (>>=) : ATMCmd a state1 state2_fn -> ((res : a) -> ATMCmd b (state2_fn res) state3_fn) -> ATMCmd b state1 state3_fn


atm : ATMCmd () Ready (const Ready)
atm = do InsertCard
         pin <- GetPIN
         pinOK <- CheckPIN pin
         case pinOK of
               CorrectPIN => do cash <- GetAmount
                                Dispense cash
                                EjectCard
               IncorrectPIN => EjectCard


testPIN : Vect 4 Char
testPIN = ['1', '2', '3', '5']


readVect : (n : Nat) -> IO (Vect n Char)
readVect Z = do discard <- getLine
                pure []
readVect (S k) = do ch <- getChar
                    chs <- readVect k
                    pure (ch :: chs)

runATM : ATMCmd res inState outState_fn -> IO res
runATM InsertCard = do putStrLn "Please insert your card (press enter)"
                       x <- getLine
                       pure ()
runATM EjectCard = putStrLn "Card ejected"
runATM GetPIN = do putStr "Enter PIN: "
                   readVect 4
runATM (CheckPIN pin) = if pin == testPIN
                       then pure CorrectPIN
                       else pure IncorrectPIN
runATM GetAmount = do putStr "How much would you like? "
                      x <- getLine
                      pure (cast x)
runATM (Dispense amount) = putStrLn $ "Here is " ++ show amount
runATM (Message x) = putStrLn x
runATM (Pure res) = pure res
runATM (x >>= f) = do x' <- runATM x
                      runATM (f x')


-- Exercise 1

data Access = LoggedOut | LoggedIn

data PwdCheck = Correct | InCorrect

data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
  Password : String -> ShellCmd PwdCheck LoggedOut (\res => case res of
                                                                 Correct => LoggedIn
                                                                 InCorrect => LoggedOut)
  Logout : ShellCmd () LoggedIn (const LoggedOut)
  GetSecret : ShellCmd String LoggedIn (const LoggedIn)
  PutStr : String -> ShellCmd () state (const state)
  PureS : (res : ty) -> ShellCmd ty (state_fn res) state_fn
  Bind : ShellCmd a state1 state2_fn -> ((res : a) -> ShellCmd b (state2_fn res) state3_fn) -> ShellCmd b state1 state3_fn


namespace ShellDo
  (>>=) : ShellCmd a state1 state2_fn -> ((res : a) -> ShellCmd b (state2_fn res) state3_fn) -> ShellCmd b state1 state3_fn
  (>>=) = Bind


session : ShellCmd () LoggedOut (const LoggedOut)
session = do Correct <- Password "wureshs"
               | InCorrect => PutStr "Wrong password"
             msg <- GetSecret
             PutStr $ "Screte code: " ++ show msg ++ "\n"
             Logout

-- sessionBad : ShellCmd () LoggedOut (const LoggedOut)
-- sessionBad = do Password "wurres"
--                 msg <- GetSecret
--                 PutStr $ "Screte code: " ++ show msg ++ "\n"
--                 Logout
