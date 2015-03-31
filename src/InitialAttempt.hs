-- This is my first attempt. It uses a generic representation of
-- operators. However, this generic representation makes some of the
-- instance declarations quite cumbersome.

{-# LANGUAGE TypeOperators, 
             GADTs, 
             DeriveFunctor,
             FlexibleInstances,
             NoMonomorphismRestriction,
             MultiParamTypeClasses, 
             FlexibleContexts, 
             ScopedTypeVariables,
             UndecidableInstances #-}

module Nodes where

import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map

------------------------------------
-- Modular functors/indexed types --
------------------------------------


infixr 8 :+:
data (f :+: g) e = Inl (f e) | Inr (g e)      deriving (Functor)

instance (Show a, Show (f a), Show (g a)) => Show ((f :+: g) a) where
    show (Inl x) = show x
    show (Inr x) = show x


class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a
  
instance Functor f => (:<:) f f where
  inj = id
  
instance (Functor f, Functor g) => (:<:) f (f :+: g) where
  inj = Inl
  
instance (Functor g, (:<:) f h) => (:<:) f (g :+: h) where
  inj = Inr . inj
  

-----------------------
-- Modular Node Type --
-----------------------


infixr 8 :+
data (n :+ m) a b = Innl (n a b) | Innr (m a b)

instance (NonLocal n, NonLocal m) => NonLocal (n :+ m) where
    entryLabel (Innl x) = entryLabel x
    entryLabel (Innr x) = entryLabel x

    successors (Innl x) = successors x
    successors (Innr x) = successors x

class sub :< sup where
  injN :: sub e x -> sup e x
  
instance (:<) f f where
  injN = id
  
instance (:<) f (f :+ g) where
  injN = Innl
  
instance ((:<) f h) => (:<) f (g :+ h) where
  injN = Innr . injN

-- Modular tuples --


class a :@ b where
  pr  ::  b -> a
  modify :: (a -> a) -> b -> b

instance a :@ a where
    pr = id
    modify = id

instance (c :@ b) => c :@ (a,b) where
    pr = pr . snd
    modify f (a,b) = (a, modify f b)

instance a :@ (a,b) where
    pr = fst
    modify f (a,b) = (modify f a, b)

instance a :@ ((a,b),c) where
    pr = fst . fst
    modify f ((a,b),c) = ((f a,b),c)

instance b :@ ((a,b),c) where
    pr = snd . fst
    modify f ((a,b),c) = ((a,f b),c)


-- Example --

data IntT
data BoolT

data Jump e x where
    Jump :: Label -> Jump O C
    Target :: Label -> Jump C O

jump = injN . Jump
target = injN . Target

instance NonLocal Jump where
    entryLabel (Target l) = l
    successors (Jump l) =[l]

data Cond src e x where
    Cond :: src BoolT -> Label -> Label -> Cond src O C


instance NonLocal (Cond src) where
    entryLabel _ = undefined
    successors (Cond _ l1 l2) =[l1,l2]

data Op op src tgt e x where
    BinOp :: op (t, s1, s2) -> tgt t -> src s1 -> src s2 -> Op op src tgt O O
    UnOp :: op (t, s) -> tgt t -> src s -> Op op src tgt O O

instance NonLocal (Op op src tgt) where
    entryLabel _ = undefined
    successors _ = undefined

data Tmp i where 
    Tmp :: Int -> Tmp IntT

data Var i where
    Var :: String -> Var IntT

data BVar i where
    BVar :: String -> BVar BoolT

data Const i where
    Const :: Int -> Const IntT

data BConst i where
    BConst :: Bool -> BConst BoolT

data IdOp i where
    IdOp :: IdOp (IntT,IntT)

data BoolIdOp i where
    BoolIdOp :: BoolIdOp (BoolT,BoolT)

data ArithOp i where
    Add :: ArithOp (IntT,IntT,IntT)
    Mul :: ArithOp (IntT,IntT,IntT)
    Neg :: ArithOp (IntT,IntT)

data BoolOp i where
    Or :: BoolOp (BoolT,BoolT,BoolT)
    And :: BoolOp (BoolT,BoolT,BoolT)
    Not :: BoolOp (BoolT,BoolT)

data CompOp i where
    Lt :: CompOp (BoolT,IntT,IntT)
    Lte :: CompOp (BoolT,IntT,IntT)
    Equ :: CompOp (BoolT,IntT,IntT)



type Src = Const :+: BConst :+: Tgt
type Tgt = Tmp :+: Var :+: BVar

type Node = Op (ArithOp :+: IdOp) Src Tgt :+ Jump :+ Cond Src


-- Constant Propagation --


flatJoin :: Eq a => Label -> OldFact a -> NewFact a -> (ChangeFlag, Pointed C b a)
flatJoin _ (OldFact old) (NewFact new)
               | old == new = (NoChange, PElem new)
               | otherwise  = (SomeChange, Top)

flatLattice :: Eq a => String -> DataflowLattice (Pointed C C a)
flatLattice name = addPoints' name flatJoin


flatMapLattice :: (Eq a, Ord k) => String -> DataflowLattice (Map k (Pointed C O a))
flatMapLattice name = DataflowLattice {
                        fact_name = name,
                        fact_bot = Map.empty,
                        fact_join = joinMaps $ extendJoinDomain flatJoin }


type ConstLattice tgt i t = Map (tgt i) (Pointed C O t)
type IntConstLattice tgt = ConstLattice tgt IntT Int
type BoolConstLattice tgt = ConstLattice tgt BoolT Bool

insertCL ::  forall i f t tgt . (ConstLattice tgt i t :@ f, Ord (tgt i)) => tgt i -> t -> f -> f
insertCL k v = modify $ Map.insert k (PElem v :: Pointed C O t)

-- | Constant propagation transfer function 
class ConstPropTrans n f where 
    constPropTrans :: n e x -> f -> Fact x f

instance (ConstPropTrans n f, ConstPropTrans m f) => ConstPropTrans (n :+ m) f where
    constPropTrans (Innl x) = constPropTrans x
    constPropTrans (Innr x) = constPropTrans x


instance ConstPropTrans Jump f where
    constPropTrans (Target _) f = f
    constPropTrans (Jump l) f = mapSingleton l f

instance ConstPropTrans (Cond src) f where
    constPropTrans (Cond _ l1 l2) f = mapFromList [(l1,f),(l2,f)]

instance (ConstPropTrans (Op op1 src tgt) f, ConstPropTrans (Op op2 src tgt) f) =>
    ConstPropTrans (Op (op1 :+: op2) src tgt) f where
        constPropTrans (BinOp (Inl op) x y z) = constPropTrans (BinOp op x y z)
        constPropTrans (BinOp (Inr op) x y z) = constPropTrans (BinOp op x y z)
        constPropTrans (UnOp (Inl op) x y) = constPropTrans (UnOp op x y)
        constPropTrans (UnOp (Inr op) x y) = constPropTrans (UnOp op x y)

instance (IntConstLattice tgt :@ f, Ord (tgt IntT)) => ConstPropTrans (Op IdOp Const tgt) f where
    constPropTrans (UnOp IdOp t (Const c)) = insertCL t c
    constPropTrans BinOp {} = id -- this clause is impossible but GHC still gives me a warning

instance (IntConstLattice tgt :@ f, Ord (tgt IntT)) => ConstPropTrans (Op IdOp src tgt) f where
    constPropTrans UnOp {} = id
    constPropTrans BinOp {} = id -- this clause is impossible but GHC still gives me a warning
