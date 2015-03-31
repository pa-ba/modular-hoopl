{-# LANGUAGE TypeOperators, 
             DeriveFunctor,
             FlexibleInstances,
             MultiParamTypeClasses, 
             OverlappingInstances,
             FlexibleContexts #-}


module Signatures where

------------------------------------
-- Modular functors/indexed types --
------------------------------------


infixr 8 :+:
data (f :+: g) e = Inl (f e) | Inr (g e)      deriving (Functor, Eq, Ord)

instance (Show a, Show (f a), Show (g a)) => Show ((f :+: g) a) where
    show (Inl x) = show x
    show (Inr x) = show x


class sub :<: sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)
  

instance (f :+: g) :<: (f :+: g) where
  inj = id
  prj = Just

instance f :<: f where
  inj = id
  prj = Just
  
instance f :<: (f :+: g) where
  inj = Inl
  prj (Inl x) = Just x
  prj (Inr _) = Nothing
  
instance (f :<: h) => f :<: (g :+: h) where
  inj = Inr . inj
  prj (Inr x) = prj x
  prj (Inl _) = Nothing
  
