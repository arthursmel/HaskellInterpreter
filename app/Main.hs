{-# Language MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-} 

module Main where

import Interpreter

main = do
    -- Gt ((Var "scratch")) (Const (I 5))
    prog <- return $ prog10

    -- Running static analysis 
    un <- return $ unused prog
    putStrLn $ "Unused variables: " ++ show un

    ui <- return $ uninitialised prog
    putStrLn $ "Uninitialised variables: " ++ show ui

    -- Running debugger 
    putStrLn help
    run prog
