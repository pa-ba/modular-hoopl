{-# LANGUAGE TypeOperators, 
             GADTs, 
             DeriveFunctor,
             FlexibleInstances,
             NoMonomorphismRestriction,
             MultiParamTypeClasses, 
             FlexibleContexts, 
             ScopedTypeVariables,
             UndecidableInstances,
             OverlappingInstances,
             IncoherentInstances,
             StandaloneDeriving,
             PolyKinds,
             TemplateHaskell#-}


module TargetSyntax 
    ( module TargetSyntax, 
      module Nodes, 
      module Signatures, 
      module Compiler.Hoopl,
      module Types ) where

import Compiler.Hoopl
import Signatures
import Nodes
import Types
import Derive
import Graph hiding (Var)

data Halt lab l r e x where
    Halt :: Halt lab l r O C

deriving instance Show (Halt lab l r e x)
instance NonLocal (Halt lab l r) where
    entryLabel _ = undefined
    successors Halt =[]

iHalt = mkLast $ injN Halt


data Cond lab lhs rhs e x where
    Cond :: rhs BoolT -> lab -> lab -> Cond lab lhs rhs O C

iCond x y z = mkLast $ injN $ Cond x y z

deriving instance (Show lab, Show (r BoolT)) => Show (Cond lab l r e x)
instance NonLocal (Cond Label lhs rhs) where
    entryLabel _ = undefined
    successors (Cond _ l1 l2) =[l1,l2]

data Except lab l r e x where
    Throw :: Except lab l r O C
    Mark :: lab -> Except lab l r O O
    Unmark :: Except lab l r O O

deriving instance Show lab => Show (Except lab l r e x)
instance NonLocal (Except lab l r) where
    entryLabel _ = undefined
    successors Throw = []

iThrow = mkLast $ injN Throw
iMark = mkMiddle . injN . Mark
iUnmark = mkMiddle $ injN Unmark

type AssignI = Assign IntT
type AssignB = Assign BoolT

data CopyOp j rhs i where
    Copy :: rhs i -> CopyOp i rhs i

type CopyOpI = CopyOp IntT
type CopyOpB = CopyOp BoolT

type CopyI = AssignI CopyOpI
type CopyB = AssignB CopyOpB

iCopy x y = iAssign x $ Copy y

data ArithOp rhs i where
    Add :: rhs IntT -> rhs IntT -> ArithOp rhs IntT
    Mul :: rhs IntT -> rhs IntT -> ArithOp rhs IntT
    Neg :: rhs IntT -> ArithOp rhs IntT

iAdd x y z = iAssign x $ Add y z
iMul x y z = iAssign x $ Mul y z
iNeg x y = iAssign x $ Neg y

deriving instance (Show (r IntT)) => Show (ArithOp r IntT)

type Arith = AssignI ArithOp

data BoolOp rhs i where
    Or :: rhs BoolT -> rhs BoolT -> BoolOp rhs BoolT
    And :: rhs BoolT -> rhs BoolT -> BoolOp rhs BoolT
    Not :: rhs BoolT -> BoolOp rhs BoolT

iAnd x y z = iAssign x $ And y z
iOr x y z = iAssign x $ Or y z
iNot x y = iAssign x $ Not y

deriving instance (Show (r BoolT)) => Show (BoolOp r i)

type Boolean = AssignB BoolOp

data CompOp rhs i where
    Lt :: rhs IntT -> rhs IntT -> CompOp rhs BoolT
    Lte :: rhs IntT -> rhs IntT -> CompOp rhs BoolT
    Equ :: rhs IntT -> rhs IntT -> CompOp rhs BoolT

deriving instance (Show (r IntT)) => Show (CompOp r i)

type Comp = AssignB CompOp

iLt x y z = iAssign x $ Lt y z
iLte x y z = iAssign x $ Lte y z
iEqu x y z = iAssign x $ Equ y z



data Tmp i = Tmp Int deriving (Eq, Ord)
instance Show (Tmp i) where
    show (Tmp x) = "@" ++ show x
data Var i = Var String  deriving (Eq, Ord)
instance Show (Var i) where
    show (Var x) = "$"++ x
    

iVar = inj . Var

data Const i where
    Const :: Int -> Const IntT

iConst = inj . Const

instance Show (Const i) where
    show (Const c) = show c
deriving instance Eq (Const i)
deriving instance Ord (Const i)

data BConst i where
    BConst :: Bool -> BConst BoolT 

instance Show (BConst i) where
    show (BConst c) = show c
deriving instance Eq (BConst i)
deriving instance Ord (BConst i)

iBConst = inj . BConst

$(derive [makeNFunctor, makeNFoldable, makeNTraversable] 
    [''Cond, ''Halt])


