{-# LANGUAGE TypeOperators, 
             DeriveFunctor,
             FlexibleInstances,
             MultiParamTypeClasses, 
             OverlappingInstances,
             FlexibleContexts, 
             KindSignatures,
             PolyKinds,
             TypeFamilies #-}

module Nodes where

import Compiler.Hoopl


-----------------------
-- Modular Node Type --
-----------------------


infixr 8 :+
data (n :+ m) lab lhs rhs a b = Innl (n lab lhs rhs a b) | Innr (m lab lhs rhs a b) deriving (Eq, Ord)

instance (NonLocal (n lab l r), NonLocal (m lab l r)) => NonLocal ((n :+ m) lab l r) where
    entryLabel (Innl x) = entryLabel x
    entryLabel (Innr x) = entryLabel x

    successors (Innl x) = successors x
    successors (Innr x) = successors x


instance (Show (f lab l r a b), Show (g lab l r a b)) => Show ((f :+ g) lab l r a b) where
    show (Innl x) = show x
    show (Innr x) = show x


class sub :< sup where
  injN :: sub lab l r e x -> sup lab l r e x
  
instance (:<) f f where
  injN = id
  
instance (:<) f (f :+ g) where
  injN = Innl
  
instance ((:<) f h) => (:<) f (g :+ h) where
  injN = Innr . injN


type family Den i :: *
