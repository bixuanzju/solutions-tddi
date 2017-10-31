import Control.ST
import Control.ST.ImplicitCall

%default total

data Access = LoggedOut | LoggedIn

data LoginResult = OK | BadPassword


interface DataStore (m : Type -> Type) where
  Store : Access -> Type
  connect : ST m Var [add (Store LoggedOut)]
  disconnect : (store : Var) -> ST m () [remove store (Store LoggedOut) ]
  readSecret : (store : Var) -> ST m String [store ::: Store LoggedIn]
  login : (store : Var) -> ST m LoginResult [store ::: Store LoggedOut :->
                              (\res => Store (case res of
                                                   OK => LoggedIn
                                                   BadPassword => LoggedOut))]
  logout : (store : Var) -> ST m () [store ::: Store LoggedIn :-> Store LoggedOut]


doConnect : DataStore m => ST m () []
doConnect = do st <- connect
               disconnect st

getSecret : (ConsoleIO m, DataStore m) => ST m () []
getSecret = do st <- connect
               OK <- login st
                 | BadPassword => do putStrLn "Failure"
                                     disconnect st
               secret <- readSecret st
               putStrLn ("Secret is: " ++ show secret)
               logout st
               disconnect st

DataStore IO where
  Store x = State String
  connect = do store <- new "Secret Data"
               pure store
  disconnect store = delete store
  readSecret store = read store
  login store = do putStr "Enter password: "
                   p <- getStr
                   if p == "hello jeremy"
                   then pure OK
                   else pure BadPassword
  logout store = pure ()


partial
getData : (ConsoleIO m, DataStore m) => (st, failcount : Var) ->
          ST m () [st ::: Store {m} LoggedOut, failcount ::: State Integer]
getData st failcount = do
  OK <- login st
    | BadPassword => do putStrLn "Failure"
                        fc <- read failcount
                        write failcount (fc + 1)
                        putStrLn $ "Number of failures: " ++ show (fc + 1)
                        getData st failcount
  secret <- readSecret st
  putStrLn $ "Secret is : " ++ show secret
  logout st
  getData st failcount


partial
main : IO ()
main = run (do fc <- new 0
               st <- connect
               getData st fc
               disconnect st
               delete fc)


-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
