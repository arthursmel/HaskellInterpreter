{-# Language MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-} 

module Interpreter (
  run, help, uninitialised, unused, prog10, errProg10
) where

import Prelude hiding (lookup, print)
import qualified Data.Map as Map
import Data.Maybe
import qualified System.IO as System

import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Evaluator

-- (Part 2)
step :: Statement -> Run ()

step smt@(Assign s v) = do debug
                           liftIO $ putStrLn $ pprint smt
                           st <- get
                           Right val <- return $ runEval st (eval v)  
                           set (s,val)

step smt@(Print e) = do debug
                        liftIO $ putStrLn $ pprint smt
                        st <- get
                        Right val <- return $ runEval st (eval e) 
                        liftIO $ System.print ("[System.Print] " ++ show val)
                        return () 

step smt@(If cond s0 s1) = do debug 
                              liftIO $ putStrLn $ pprint smt
                              st <- get
                              Right (B val) <- return $ runEval st (eval cond)
                              if val then do step s0 else do step s1

step smt@(While cond s) = do debug 
                             liftIO $ putStrLn $ pprint smt
                             st <- get
                             Right (B val) <- return $ runEval st (eval cond)
                             if val then do step s >> step (While cond s) else return ()

step smt@(Try s0 s1) = do debug
                          liftIO $ putStrLn $ pprint smt
                          catchError (step s0) (\e -> step s1)

step (Seq s0 s1) = do step s0 >> step s1
                        
step Pass = return ()


set :: (Name, Val) -> Run ()
set (s,i) = do  vs <- gets vars
                modify (\env -> env { vars = Map.insert s i vs })


{-------------------------------------------------------------------}
{- The debugger                                                    -}
{-------------------------------------------------------------------}

-- Called each time a step is executed
debug :: Run ()
debug = do step <- gets nStep
           -- Exec next step if "n" has been chosen from prompt
           -- regardless of dbg value 
           if step then do
               -- Unset the nStep as next step has been exec 
               modify (\env -> env { nStep = False })
               prompt
           else do 
               -- Test conditional breakpoint
               e <- gets expr
               case e of 
                   -- If breakpoint has not been set, prompt if in dbg mode 
                   Const (B True) -> do d <- gets dbg
                                        when d prompt 

                   -- If breakpoint has been set, test & if result is True
                   -- set debug to false (i.e. exec program until it tests as false
                   -- or until the user decides to exec a single statement)                      
                   otherwise       -> do res <- testExpr
                                         setDbg $ not res
                                         when (not res) prompt

-- Prompts user to exec next statement or to call promptVar
-- (part 3.1)
prompt :: Run ()
prompt = do rs <- liftIO $ getLine
            case rs of 
                -- Next statement to be exec, regardless of debug mode or not
                "n"       -> modify (\env -> env { nStep = True })

                -- Check value of a certain variable
                "v"       -> do promptVar
                                prompt

                -- Run program, debugging mode set to false (all lines will be exec)
                "r"       -> setDbg False   

                -- Show help 
                "h"       -> do liftIO $ putStrLn help
                                prompt

                -- Set conditional breakpoint expression
                -- Debugging mode will be set to true if this expression evals to false
                "c"       -> do e <- readExpr
                                setExpr e
                                prompt

                -- Remove conditional breakpoint expression
                "cr"      -> do liftIO $ putStrLn "Removed"
                                setExpr initExpr
                                prompt

                otherwise -> do liftIO $ putStrLn "invalid prompt"
                                prompt 

-- Prompts user to enter a variable name to output current value 
-- (part 3.2)
promptVar :: Run ()
promptVar = do liftIO $ putStrLn "Enter variable: "
               s <- liftIO $ getLine
               vars <- gets vars
               do  v <- lookup s vars
                   liftIO $ putStrLn $ show $ v
                   return ()
               `catchError` \e -> do
                   -- Catch error if the user enters an unknown variable
                   liftIO $ putStrLn $ "Error: " ++ e
                   promptVar

-- Conditional breakpoint expression
-- (part 4)
readExpr :: Run Expr
readExpr = do expr <- liftIO $ readLn
              return expr

setExpr :: Expr -> Run ()
setExpr e = modify (\env -> env { expr = e })

-- Returns true is the conditional breakpoint
-- expression evaluates to true or if it gives an error
testExpr :: Run Bool
testExpr = do st <- get
              res <- return $ runEval st (eval $ expr st)
              case res of 
                  (Right (B True))    -> return True
                  (Left err)          -> return True
                  otherwise           -> return False

setDbg :: Bool -> Run ()
setDbg b = do d <- gets dbg
              modify (\env -> env { dbg = b })

{-------------------------------------------------------------------}
{- Static analysis (part 5 - 1. & 3.)                              -}
{-------------------------------------------------------------------}

-- Each variable will have a VarCount which
-- will store the program counter value when
-- a reference or an assignment to the variable
-- occurs 
data VarCount = VarCount {
    asn :: [Int], -- assignments
    ref :: [Int]  -- references
} deriving (Show)

-- The static analysis will use the state monad
-- where the state contains a VarCount for each 
-- of the variables as the interpreter encounters them
-- along with the program counter 
data StaticState = StaticState {
    varCounts :: Map.Map String VarCount,
    pc :: Int -- program counter
} deriving (Show)

initStaticState :: StaticState
initStaticState = StaticState Map.empty 0

-- Inserting the pc value to either the assignment or references of
-- a variable's VarCount. If the variable is fresh, a VarCount with a 
-- singleton array   and an empty array
insertVcs :: (Int -> VarCount -> VarCount) -> (Int -> VarCount) -> String -> State StaticState ()
insertVcs fAdj fIns s = do vcs <- gets varCounts
                           p <- gets pc
                           if Map.member s vcs then 
                                modify (\st -> StaticState (Map.adjust (fAdj p) s vcs) p)                   
                           else modify (\st -> StaticState (Map.insert s (fIns p) vcs) p)


insertRef :: String -> State StaticState ()
insertRef = insertVcs 
    (\pc vc -> VarCount (asn vc) ((ref vc) ++ [pc])) 
    -- if the var counts does not contain the variable yet
    -- create + add to referencess
        (\pc -> VarCount [] [pc]) 


insertAsn :: String -> State StaticState ()
insertAsn = insertVcs 
    (\pc vc -> VarCount ((asn vc) ++ [pc]) (ref vc)) 
    -- if the var counts does not contain the variable yet
    -- create + add to assignments
        (\pc -> VarCount [pc] [])

-- Increment the program counter
incPc :: State StaticState ()
incPc = do vcs <- gets varCounts
           p <- gets pc
           modify (\st -> StaticState vcs (p + 1))
             

-- Analysis of the given expression
aExpr :: Expr -> State StaticState ()

aExpr (Var s)     = insertRef s
                                
aExpr (Const v)   = return ()

aExpr (Not e0)    = aExpr e0
aExpr (Add e0 e1) = aExpr e0 >> aExpr e1 
aExpr (Sub e0 e1) = aExpr e0 >> aExpr e1 
aExpr (Mul e0 e1) = aExpr e0 >> aExpr e1 
aExpr (Div e0 e1) = aExpr e0 >> aExpr e1 
aExpr (And e0 e1) = aExpr e0 >> aExpr e1 
aExpr (Or e0 e1)  = aExpr e0 >> aExpr e1 
aExpr (Eq e0 e1)  = aExpr e0 >> aExpr e1 
aExpr (Gt e0 e1)  = aExpr e0 >> aExpr e1 
aExpr (Lt e0 e1)  = aExpr e0 >> aExpr e1 

-- Analysis of the given statment
aStatement :: Statement -> State StaticState ()

aStatement (Assign s v)    = incPc >> insertAsn s >> aExpr v

aStatement (Print e)       = incPc >> aExpr e

aStatement (If cond s0 s1) = do incPc >> aExpr cond 
                                incPc >> aStatement s0 
                                incPc >> aStatement s1

aStatement (While cond s)  = do incPc >> aExpr cond 
                                incPc >> aStatement s

aStatement (Try s0 s1)     = do incPc >> aStatement s0
                                incPc >> aStatement s1

aStatement (Seq s0 s1)     = do incPc >> aStatement s0 
                                incPc >> aStatement s1   

aStatement Pass            = return ()

-- Analyse the variables of the given program
-- Populates the state with a VarCount for each variable encountered
-- Filters by the given function and returns the filtered names
aVars :: (VarCount -> Bool) -> Program -> [String]
aVars f p = ((map fst) . Map.toList . (Map.filter f)) vcs 
            where 
                p'   = compile p
                vcs  = varCounts $ execState (aStatement p') initStaticState

-- A variable is accessed when uninitialsed if the 
-- PC of the first assignment is larger than the 
-- PC of the first reference
isUninit :: [Int] -> [Int] -> Bool 
isUninit []  [r] = True
isUninit [a] []  = False
isUninit as  rs  = (head as) > (head rs)

-- A variable is unused if it has been assigned a value
-- but it has never been referenced
unused :: Program -> [String]
unused = aVars (\vc -> ((length . asn) vc > 0) && ((length . ref) vc == 0))

uninitialised :: Program -> [String]
uninitialised = aVars (\vc -> isUninit (asn vc) (ref vc))


{- Pour some sugar over this -}
{- This next section deals exclusively with defining convenience functions -}
{- which we will use when writing the actual programs in the DSL. -}

int = Const . I
bool = Const . B
var = Var

class SmartAssignment a where
  assign :: String -> a -> Statement

instance SmartAssignment Int where
  assign v i = Assign v (Const (I i))

instance SmartAssignment Bool where
  assign v b = Assign v (Const (B b))

instance SmartAssignment Expr where
  assign v e = Assign v e


class PrettyExpr a b where
  (.*) :: a -> b -> Expr
  (.-) :: a -> b -> Expr

instance PrettyExpr String String where
  x .* y = (Var x) `Mul` (Var y)
  x .- y = (Var x) `Sub` (Var y)

instance PrettyExpr String Int where
  x .* y = (Var x) `Mul` (Const (I y))
  x .- y = (Var x) `Sub` (Const (I y))

instance Semigroup Statement where
    a <> b = a `Seq` b

instance Monoid Statement where
    mempty = Pass

type Program = Writer Statement ()

compile :: Program -> Statement
compile p = snd . runIdentity $ runWriterT p

-- Used when the conditional breakpoint expr is unset
initExpr :: Expr
initExpr = Const (B True)

emptyEnv :: Env
emptyEnv = Env Map.empty True initExpr False

run :: Program -> IO ()
run program = do result <- runExceptT $ (runStateT $ step $ snd $ runIdentity $ (runWriterT program)) emptyEnv
                 case result of
                      Right ( (), env ) -> return ()                     
                      Left exn -> System.print ("Uncaught exception: "++exn)


infixl 1 .=
(.=) :: String -> Expr -> Program 
var .= val = tell $ assign var val

iif :: Expr -> Program -> Program -> Program
iif cond tthen eelse = tell $ If cond (compile tthen) (compile eelse)

while :: Expr -> Program -> Program
while cond body = tell $ While cond (compile body)

print :: Expr -> Program
print e = tell $ Print e

try :: Program -> Program -> Program
try block recover = tell $ Try (compile block) (compile recover)

help :: String
help = unlines [
        "n:\texec next statement",
        "v:\tprint variable",
        "r:\trun program",
        "h:\thelp",
        "c:\tset conditional break point",
        "cr:\tremove conditional break point"]

-- Example program with uninitialised & unused variables
errProg10 :: Program
errProg10 = do
           "arg"     .= int 10
           "scratch" .= var "arg"
           "unused"  .= int 1000
           "total"   .= int 1
           while ( (var "scratch") `Gt` (int 1) ) (
            do "total"   .=  "total" .* "scratch"
               "scratch" .= "scratch" .- (1::Int)
               print $ var "scratch"
               print $ var "uninitialised"
               print $ ((var "uninitialised2") `Gt` (int 1))
               "unused2" .= int 1000
            )
           print $ var "total"

prog10 :: Program
prog10 = do
           "arg"     .= int 10
           "scratch" .= var "arg"
           "total"   .= int 1
           while ( (var "scratch") `Gt` (int 1) ) (
            do "total"   .=  "total" .* "scratch"
               "scratch" .= "scratch" .- (1::Int)
               print $ var "scratch"
            )
           print $ var "total"
