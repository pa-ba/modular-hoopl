{-# LANGUAGE GADTs, TemplateHaskell, TypeOperators, FlexibleContexts #-}


module SourceSyntax (module SourceSyntax, module HFixpoint, module Types) where

import Types
import Derive
import HFixpoint

-----------------------------------
-- Syntax of the Source Language --
-----------------------------------


-- The following two empty types are used as indices for the
-- definition of the syntax (higher-order) functors. We could use
-- promoted data types instead, but this approach keeps the set of
-- indices open, in accordance with our goal for modular definitions.
data Exp e
data Stmt

type IExp = Exp IntT
type BExp = Exp BoolT

data Arith  e l where
   Val :: Int -> Arith e IExp
   Add :: e IExp -> e IExp -> Arith e IExp 
   Mul :: e IExp -> e IExp -> Arith e IExp 


data Except e l where
    Throw :: Except e Stmt
    Catch :: e Stmt -> e Stmt -> Except e Stmt

newtype Var = Var String  deriving (Eq, Ord)

instance Show Var where
    show (Var x) = x

data State e l where
    Get :: Var -> State e IExp
    Set :: Var -> e IExp -> State e Stmt


data While e l where
    While ::  e BExp -> e Stmt -> While e Stmt

data Comp e l where
    Equ :: e IExp -> e IExp -> Comp e BExp
    Lt :: e IExp -> e IExp -> Comp e BExp

data Boolean e l where
    BVal :: Bool  -> Boolean e BExp
    And :: e BExp -> e BExp -> Boolean e BExp
    Or :: e BExp -> e BExp -> Boolean e BExp
    Not :: e BExp -> Boolean e BExp

data If e l where
    If :: e BExp -> e l -> e l -> If e l

data Seq e l where
    Seq :: e Stmt -> e l -> Seq e l

$(derive [makeHFunctor] [''Arith, ''Except, ''State, ''While, ''If, ''Seq, ''Comp, ''Boolean])

-- Smart constructors --

valF :: (Arith ::< f) => Int -> HFix f IExp
valF x = hinject (Val x)
addF :: (Arith ::< f) => HFix f IExp -> HFix f IExp -> HFix f IExp
addF x y = hinject (Add x y)
mulF :: (Arith ::< f) => HFix f IExp -> HFix f IExp -> HFix f IExp
mulF x y = hinject (Mul x y)

throwF :: (Except ::< f) => 
          HFix f Stmt
throwF = hinject Throw
catchF :: (Except ::< f) => HFix f Stmt -> HFix f Stmt -> HFix f Stmt
catchF x y = hinject (Catch x y)
getF :: (State ::< f) => Var -> HFix f IExp
getF x = hinject (Get x)
setF :: (State ::< f) => Var -> HFix f IExp -> HFix f Stmt
setF x y = hinject (Set x y)
whileF :: (While ::< f) => HFix f BExp -> HFix f Stmt -> HFix f Stmt
whileF x y = hinject (While x y)
ifF :: (If ::< f) => HFix f BExp -> HFix f i -> HFix f i -> HFix f i
ifF x y z = hinject (If x y z)
seqF :: (Seq ::< f) => HFix f Stmt -> HFix f i -> HFix f i
seqF x y = hinject (Seq x y)

bvalF :: (Boolean ::< f) => Bool -> HFix f BExp
bvalF x = hinject (BVal x)
ltF :: (Comp ::< f) => HFix f IExp -> HFix f IExp -> HFix f BExp
ltF x y = hinject (Lt x y)
equF :: (Comp ::< f) => HFix f IExp -> HFix f IExp -> HFix f BExp
equF x y = hinject (Equ x y)
orF :: (Boolean ::< f) => HFix f BExp -> HFix f BExp -> HFix f BExp
orF x y = hinject (Or x y)
andF :: (Boolean ::< f) => HFix f BExp -> HFix f BExp -> HFix f BExp
andF x y = hinject (And x y)
notF :: (Boolean ::< f) => HFix f BExp -> HFix f BExp
notF x = hinject (Not x)
