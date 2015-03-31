{-# LANGUAGE TypeOperators, 
             GADTs, 
             FlexibleInstances,
             MultiParamTypeClasses, 
             FlexibleContexts, 
             ScopedTypeVariables,
             UndecidableInstances,
             OverlappingInstances,
             PolyKinds,
             KindSignatures,
             TypeFamilies #-}

module ConstantFolding where

import TargetSyntax
import Graph

class ConstFold n n' lhs rhs where
    constFold :: n Label lhs rhs e x -> Maybe (Graph (n' Label lhs rhs) e x)


constFoldRewrite :: (FuelMonad m, ConstFold n n lhs rhs) => FwdRewrite m (n Label lhs rhs) f
constFoldRewrite = mkFRewrite (\ n _ -> return $ constFold n)

instance (ConstFold n1 m lhs rhs, ConstFold n2 m lhs rhs) => ConstFold (n1 :+ n2) m lhs rhs where
    constFold (Innl x) = constFold x
    constFold (Innr x) = constFold x

class ConstFoldOp op rhs where
    constFoldOp :: op rhs i -> Maybe (Den i)

instance ConstFoldOp CopyOpI rhs where
    constFoldOp _ = Nothing

instance ConstFoldOp CopyOpB rhs where
    constFoldOp _ = Nothing

instance (ConstFoldOp op rhs, Const :<: rhs, AssignI CopyOpI :< m)
    => ConstFold (AssignI op) m lhs rhs where
    constFold (Assign x op) = do n <- constFoldOp op
                                 return $ iCopy x $ iConst n


instance (ConstFoldOp op rhs, BConst :<: rhs, AssignB CopyOpB :< m)
    => ConstFold (AssignB op) m lhs rhs where
    constFold (Assign x op) = do n <- constFoldOp op
                                 return $ iCopy x $ iBConst n

intOp2 :: (Const :<: rhs) => (Int -> Int -> a) -> rhs IntT -> rhs IntT -> Maybe a
intOp2 op x y = do Const p <- prj x
                   Const q <- prj y
                   return (op p q)

boolOp2 :: (BConst :<: rhs) => (Bool -> Bool -> a) -> rhs BoolT -> rhs BoolT -> Maybe a
boolOp2 op x y = do BConst p <- prj x
                    BConst q <- prj y
                    return (op p q)

instance (Const :<: rhs) => ConstFoldOp ArithOp rhs where
    constFoldOp (Add x y) = intOp2 (+) x y
    constFoldOp (Mul x y) = intOp2 (*) x y
    constFoldOp (Neg y) = do Const p <- prj y
                             return (- p)

instance (BConst :<: rhs) => ConstFoldOp BoolOp rhs where
    constFoldOp (And x y) = boolOp2 (&&) x y
    constFoldOp (Or x y) = boolOp2 (||) x y
    constFoldOp (Not y) = do BConst p <- prj y
                             return (not p)

instance (Const :<: rhs) => ConstFoldOp CompOp rhs where
    constFoldOp (Lte x y) = intOp2 (<=) x y
    constFoldOp (Lt x y) = intOp2 (<) x y
    constFoldOp (Equ x y) = intOp2 (==) x y

instance (Jump :< n, BConst :<: rhs) => ConstFold Cond n lhs rhs where
    constFold (Cond x l1 l2) = do BConst b <- prj x 
                                  return $ iJump $ if b then l1 else l2

instance ConstFold m n lhs rhs where
    constFold _ = Nothing
