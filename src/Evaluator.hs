{-# Language MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-} 

module Evaluator (
    eval, Val(..), Expr(..), Name, Vars, Env(..), lookup, Eval,
    runEval, Statement(..), Run, runRun, pprint
) where

import Prelude hiding (lookup)
import qualified Data.Map as Map

import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State


data Val = I Int | B Bool
            deriving (Eq, Show, Read)

data Expr = Const Val
    | Add Expr Expr | Sub Expr Expr  | Mul Expr Expr | Div Expr Expr
    | And Expr Expr | Or Expr Expr   | Not Expr 
    | Eq Expr Expr  | Gt Expr Expr   | Lt Expr Expr
    | Var String
    deriving (Eq, Show, Read)

type Name = String 
type Vars = Map.Map Name Val

data Env = Env {
    vars  :: Vars, 
    dbg   :: Bool, -- Debug mode for the environment 
    expr  :: Expr, -- The conditional breakpoint expression 
    nStep :: Bool  -- Whether a single next statement should be exec
                   -- regardless of debug mode
}

lookup k t = case Map.lookup k t of
                Just x -> return x
                Nothing -> throwError ("Unknown variable "++k)


type Eval a = ReaderT Env (ExceptT String Identity) a 
runEval env ex = runIdentity ( runExceptT ( runReaderT ex env) )

evali op e0 e1 = do e0' <- eval e0
                    e1' <- eval e1
                    case (e0', e1') of
                            (I i0, I i1) -> return $ I (i0 `op` i1)
                            _            -> throwError "type error in arithmetic expression"

evalb op e0 e1 = do e0' <- eval e0
                    e1' <- eval e1
                    case (e0', e1') of
                         (B i0, B i1) -> return $ B (i0 `op` i1)
                         _            -> throwError "type error in boolean expression"

evalib op e0 e1 = do e0' <- eval e0
                     e1' <- eval e1
                     case (e0', e1') of
                          (I i0, I i1) -> return $ B (i0 `op` i1)
                          _            -> throwError "type error in arithmetic expression"

eval :: Expr -> Eval Val
eval (Const v) = return v
eval (Add e0 e1) = do evali (+) e0 e1
eval (Sub e0 e1) = do evali (-) e0 e1
eval (Mul e0 e1) = do evali (*) e0 e1
eval (Div e0 e1) = do evali div e0 e1

eval (And e0 e1) = do evalb (&&) e0 e1
eval (Or e0 e1) = do evalb (||) e0 e1

eval (Not e0  ) = do evalb (const not) e0 (Const (B True)) 
                       where not2 a _ = not a -- hack, hack

eval (Eq e0 e1) = do evalib (==) e0 e1
eval (Gt e0 e1) = do evalib (>) e0 e1
eval (Lt e0 e1) = do evalib (<) e0 e1
                        
eval (Var s) = do vs <- asks vars
                  lookup s vs

data Statement = Assign String Expr
               | If Expr Statement Statement
               | While Expr Statement
               | Print Expr
               | Seq Statement Statement
               | Try Statement Statement
               | Pass                    
      deriving (Eq, Show)

type Run a = StateT Env (ExceptT String IO) a 
runRun p =  runExceptT (runStateT p Map.empty) 

-- The string representation of the "next line" for debugging
pprint :: Statement -> String
pprint (Assign s e) = s ++ " .= " ++ (show e)
pprint (If e s0 s1) = "iif (" ++ (show e) ++ ")"
pprint (While e s ) = "while (" ++ (show e) ++ ")"
pprint (Print e   ) = "print " ++ (show e)
pprint (Seq s0 s1 ) = "seq"
pprint (Try s0 s1 ) = "try"
pprint (Pass      ) = "pass"
