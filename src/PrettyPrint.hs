{-# LANGUAGE GADTs, 
             FlexibleInstances,
             FlexibleContexts,
             ScopedTypeVariables,
             StandaloneDeriving #-}


module PrettyPrint where


import Compiler.Hoopl
import TargetSyntax
import Unsafe.Coerce
import Graph

deriving instance Show a => Show (MaybeO e a)


-- hack
instance (Show (n () ()), NonLocal n) => Show (Graph n e x) where
    show = showGraph showInstance where
        showInstance :: forall n . Show (n () ()) => forall e x . n e x -> String
        showInstance n = show (unsafeCoerce n :: n () ())


instance (Show (l i), Show (r i)) => Show (Assign i (CopyOp i) lab l r e x) where
    show (Assign x (Copy y)) = show x ++ " <- " ++ show y

instance (Show (l IntT), Show (r IntT)) => Show (Arith lab l r e x) where
    show (Assign x y) = show x ++ " <- " ++ show y

instance (Show (l BoolT), Show (r BoolT)) => Show (Boolean lab l r e x) where
    show (Assign x y) = show x ++ " <- " ++ show y

instance (Show (l BoolT), Show (r IntT)) => Show (Comp lab l r e x) where
    show (Assign x y) = show x ++ " <- " ++ show y
