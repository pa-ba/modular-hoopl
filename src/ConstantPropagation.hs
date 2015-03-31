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
             DefaultSignatures #-}

module ConstantPropagation where

import TargetSyntax hiding ((<*>))
import Lattice

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad
import Control.Applicative hiding (Const)
import Data.Monoid
import Graph

type ConstLattice lhs i = Map (lhs i) (WithTop (Den i))
type IntConstLattice lhs = ConstLattice lhs IntT
type BoolConstLattice lhs = ConstLattice lhs BoolT

data Proxy (t :: k) = Proxy

insertCL ::  forall i f lhs . (ConstLattice lhs i :@ f, Ord (lhs i)) => lhs i -> Den i -> f -> f
insertCL k v = modify $ Map.insert k (PElem v :: Pointed C O (Den i))


insertTop ::  forall i f lhs . (ConstLattice lhs i :@ f, Ord (lhs i)) => lhs i -> f -> f
insertTop k = modify $ Map.insert k (Top :: (WithTop (Den i)))



lookupCL' :: forall i f lhs rhs . (ConstLattice lhs i :@ f, Ord (lhs i), lhs :<: rhs) 
            => Proxy lhs -> rhs i -> f -> Maybe (Den i)
lookupCL' _ k f = do k' <- prj k :: Maybe (lhs i)
                     r <- Map.lookup k' (pr f) :: Maybe (WithTop (Den i))
                     fromPointed r

lookupCL :: (ConstLattice lhs i :@ f, Ord (lhs i), lhs :<: rhs) 
            => Proxy lhs -> (Den i -> rhs i) -> rhs i -> f -> (ChangeFlag, rhs i)
lookupCL t coerce k f = toChangeFlag k $ liftM coerce (lookupCL' t k f)


toChangeFlag :: t -> Maybe t -> (ChangeFlag, t)
toChangeFlag d m = case m of
                    Just n -> (SomeChange, n)
                    Nothing -> (NoChange, d)

-- The following Monoid instance will give us an instance of
-- Applicative (ChangeFlag, ). This will allow us to disjunctively
-- propagate changes. Compare this to the Maybe applicative, which
-- propagates changes conjunctively.

instance Monoid ChangeFlag where
    mempty = NoChange
    mappend NoChange NoChange = NoChange
    mappend _ _               = SomeChange



-- | Constant propagation transfer function. Here we assume that the
-- only non-trivial cases (i.e. facts are not merely copied) are nodes
-- that are open on exit. This is a reasonable assumption (one could
-- even go further and only consider nodes that are open on both entry
-- and exit). Even if there should be an instance where nodes of the
-- remaining shape (viz. closed on exit) have non-trivial transfer
-- functions, we can simply add another type class for that shape.
class ConstPropTrans n l r f where 
    constPropTrans :: n Label l r e O -> f -> f
    constPropTransC :: n Label l r O C -> f -> FactBase f

    default constPropTransC :: NonLocal (n Label l r) => n Label l r O C -> f -> FactBase f
    constPropTransC n f = mapFromList [(l,f) | l <- successors n]

constPropTrans' :: (NonLocal (n Label l r), ConstPropTrans n l r f) => FwdTransfer (n Label l r) f
constPropTrans' = mkFTransfer3 constPropTrans constPropTrans constPropTransC



instance (ConstPropTrans n l r f, ConstPropTrans m l r f) => ConstPropTrans (n :+ m) l r f where
    constPropTrans (Innl x) = constPropTrans x
    constPropTrans (Innr x) = constPropTrans x

    constPropTransC (Innl x) = constPropTransC x
    constPropTransC (Innr x) = constPropTransC x

instance ConstPropTrans Halt l r f where
     constPropTrans _ = id

instance ConstPropTrans Jump l r f where
     constPropTrans _ = id

instance (lhs :<: rhs, BoolConstLattice lhs :@ f, Ord (lhs BoolT)) => ConstPropTrans Cond lhs rhs f where
    constPropTrans _ = id
    constPropTransC (Cond b l1 l2) f = case prj b :: Maybe (lhs BoolT) of
                                        Just t -> mapFromList [(l1,insertCL t True f),
                                                              (l2,insertCL t False f)]
                                        Nothing -> mapFromList [(l1, f),(l1,f)]

instance (IntConstLattice lhs :@ f, Ord (lhs IntT), Const :<: rhs)
    => ConstPropTrans (AssignI CopyOpI) lhs rhs f where
    constPropTrans (Assign t (Copy c)) = case prj c of
                                    Just (Const c') -> insertCL t c'
                                    _               -> insertTop t

instance (BoolConstLattice lhs :@ f, Ord (lhs BoolT), BConst :<: rhs)
    => ConstPropTrans (AssignB CopyOpB) lhs rhs f where
    constPropTrans (Assign t (Copy c)) = case prj c of
                                    Just (BConst c') -> insertCL t c'
                                    _                -> insertTop t

instance (ConstLattice lhs i :@ f, Ord (lhs i))
    => ConstPropTrans (Assign i op) lhs rhs f where
    constPropTrans (Assign t _) = insertTop t


class ConstProp n n' f lhs rhs where
    constProp :: n Label lhs rhs e x -> f -> Maybe (Graph (n' Label lhs rhs) e x)
    constProp n f = case constProp' n f of
                      (NoChange,_) -> Nothing
                      (SomeChange,k) -> Just k

    -- | Instead of 'constProp' one can give an implementation of this
    -- method. An implementation of 'constProp' in terms of
    -- 'constProp'' is then derived via the default implementation of
    -- 'constProp'.
    constProp' :: n Label lhs rhs e x -> f -> (ChangeFlag, Graph (n' Label lhs rhs) e x)
    constProp' _ _ = (NoChange, undefined)


constPropRewrite :: FuelMonad m => ConstProp n n f lhs rhs => FwdRewrite m (n Label lhs rhs) f
constPropRewrite = mkFRewrite (\ n f -> return $ constProp n f)



instance (ConstProp n1 m f lhs rhs, ConstProp n2 m f lhs rhs) => ConstProp (n1 :+ n2) m f lhs rhs where
    constProp (Innl x) = constProp x
    constProp (Innr x) = constProp x

class ConstPropOp op f lhs rhs where
    constPropOp :: Proxy lhs -> op rhs i -> f -> (ChangeFlag, (op rhs i))

instance (ConstPropOp op f lhs rhs, Assign i op :< n) => ConstProp (Assign i op) n f lhs rhs where
    constProp' (Assign x op) f = iAssign x <$> constPropOp (Proxy :: Proxy lhs) op f

instance (IntConstLattice lhs :@ f, Const :<: rhs, lhs :<: rhs, 
          Ord (lhs IntT))  => ConstPropOp ArithOp f lhs rhs where
    constPropOp _ n f = case n of
                      Add y z -> Add <$> li y <*> li z
                      Mul y z -> Mul <$> li y <*> li z
                      Neg y   -> Neg <$> li y
       where li x = lookupCL (Proxy :: Proxy lhs) iConst (x :: rhs IntT) f


instance (BoolConstLattice lhs :@ f, BConst :<: rhs, lhs :<: rhs, 
          Ord (lhs BoolT))  => ConstPropOp BoolOp f lhs rhs where
    constPropOp _ n f = case n of
                      And y z -> And <$> lb y <*> lb z
                      Or y z -> Or <$> lb y <*> lb z
                      Not y -> Not <$> lb y
       where lb x = lookupCL (Proxy :: Proxy lhs) iBConst (x :: rhs BoolT) f

instance (IntConstLattice lhs :@ f, Const :<: rhs, lhs :<: rhs, 
          Ord (lhs IntT))  => ConstPropOp CompOp f lhs rhs where
    constPropOp _ n f = case n of
                      Lte y z -> Lte <$> li y <*> li z
                      Lt y z  -> Lt <$> li y <*> li z
                      Equ y z -> Equ <$> li y <*> li z
       where li x = lookupCL (Proxy :: Proxy lhs) iConst (x :: rhs IntT) f


instance (BoolConstLattice lhs :@ f, BConst :<: rhs, lhs :<: rhs, 
          Ord (lhs BoolT))  => ConstPropOp CopyOpB f lhs rhs where
    constPropOp _ (Copy y) f = Copy <$> lb y
       where lb x = lookupCL (Proxy :: Proxy lhs) iBConst (x :: rhs BoolT) f

instance (IntConstLattice lhs :@ f, Const :<: rhs, lhs :<: rhs, 
          Ord (lhs IntT))  => ConstPropOp CopyOpI f lhs rhs where
    constPropOp _ (Copy y) f = Copy <$> lb y
       where lb x = lookupCL (Proxy :: Proxy lhs) iConst (x :: rhs IntT) f

instance (BoolConstLattice lhs :@ f, Cond :< n, BConst :<: rhs, lhs :<: rhs, 
          Ord (lhs BoolT))  => ConstProp Cond n f lhs rhs where
    constProp' (Cond x t e) f = (\ x -> iCond x t e) <$> lb x
       where lb x = lookupCL (Proxy :: Proxy lhs) iBConst (x :: rhs BoolT) f

instance ConstProp m n f lhs rhs where
    constProp _ _ = Nothing
