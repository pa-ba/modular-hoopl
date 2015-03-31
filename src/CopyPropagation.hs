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


			 
module CopyPropagation where

import TargetSyntax hiding ((<*>))
import Lattice
import Data.Map (Map)
import qualified Data.Set as S
import qualified Data.Map as Map
import Control.Monad
import Control.Applicative hiding (Const)
import Data.Monoid
import Graph

data Proxy (t :: k) = Proxy

instance Monoid ChangeFlag where
    mempty = NoChange
    mappend NoChange NoChange = NoChange
    mappend _ _               = SomeChange
	
-- The lattice for this optimisation associates lhs's with the strings identifying variables.
-- We can reconstruct the variables again [for an arbitrary type] using the iVar constructor.

type VarLattice lhs i = Map (lhs i) (WithTop (lhs i))

type IntVarLattice lhs  = VarLattice lhs IntT 
type BoolVarLattice lhs = VarLattice lhs BoolT 

insertVL :: forall i f lhs . (VarLattice lhs i :@ f, Ord (lhs i)) => lhs i -> lhs i -> f -> f
insertVL k v = modify $ Map.insert k (PElem v :: WithTop (lhs i))

insertTop ::  forall i f lhs . (VarLattice lhs i :@ f, Ord (lhs i)) => lhs i -> f -> f
insertTop k = modify $ Map.insert k (Top :: WithTop (lhs i))

lookupVL' :: forall i f lhs rhs . (VarLattice lhs i :@ f, Ord (lhs i), lhs :<: rhs) 
          => Proxy lhs -> rhs i -> f -> Maybe (rhs i)
lookupVL' _ k f = do k' <- prj k :: Maybe (lhs i)
                     r <- Map.lookup k' (pr f) :: Maybe (WithTop (lhs i))
                     r' <- fromPointed r
                     return (inj r')

lookupVL :: (VarLattice lhs i :@ f, Ord (lhs i), lhs :<: rhs) 
         => Proxy lhs -> rhs i -> f -> (ChangeFlag, rhs i)
lookupVL t k f = toChangeFlag k (lookupVL' t k f)

toChangeFlag :: t -> Maybe t -> (ChangeFlag, t)
toChangeFlag d m = case m of
                    Just n  -> (SomeChange, n)
                    Nothing -> (SomeChange, d)

class CopyPropTrans n l r f where 
    copyPropTrans :: n Label l r e O -> f -> f
    copyPropTransC :: n Label l r O C -> f -> FactBase f

    default copyPropTransC :: NonLocal (n Label l r) => n Label l r O C -> f -> FactBase f
    copyPropTransC n f = mapFromList [(l,f) | l <- successors n]

instance (CopyPropTrans n l r f, CopyPropTrans m l r f) => CopyPropTrans (n :+ m) l r f where
    copyPropTrans (Innl x) = copyPropTrans x
    copyPropTrans (Innr x) = copyPropTrans x

    copyPropTransC (Innl x) = copyPropTransC x
    copyPropTransC (Innr x) = copyPropTransC x
	
instance NonLocal (n Label l r) => CopyPropTrans n l r f where
    copyPropTrans _ = id
	
instance (VarLattice lhs i :@ f, Ord (lhs i), lhs :<: rhs) 
         => CopyPropTrans (Assign i (CopyOp i)) lhs rhs f where
    copyPropTrans (Assign t (Copy c)) = case prj c of 
                  Just (c' :: lhs  i) -> insertVL t c'
                  _ -> insertTop t


copyPropTrans' :: (NonLocal (n Label l r), CopyPropTrans n l r f) => FwdTransfer (n Label l r) f
copyPropTrans' = mkFTransfer3 copyPropTrans copyPropTrans copyPropTransC

------------------------------------------

class CopyProp n n' f lhs rhs where
    copyProp :: n Label lhs rhs e x -> f -> Maybe (Graph (n' Label lhs rhs) e x)
    copyProp n f = case copyProp' n f of (NoChange,_) -> Nothing; (SomeChange,k) -> Just k
    copyProp' :: n Label lhs rhs e x -> f -> (ChangeFlag, Graph (n' Label lhs rhs) e x)
    copyProp' _ _ = (NoChange, undefined)

copyPropRewrite :: FuelMonad m => CopyProp n n f lhs rhs => FwdRewrite m (n Label lhs rhs) f
copyPropRewrite = mkFRewrite (\ n f -> return $ copyProp n f)

instance (CopyProp n1 m f lhs rhs, CopyProp n2 m f lhs rhs) 
         => CopyProp (n1 :+ n2) m f lhs rhs where
    copyProp (Innl x) = copyProp x
    copyProp (Innr x) = copyProp x


class CopyPropOp op f lhs rhs where
    copyPropOp :: Proxy lhs -> op rhs i -> f -> (ChangeFlag, op rhs i)
	
instance (CopyPropOp op f lhs rhs, Assign i op :< n) => CopyProp (Assign i op) n f lhs rhs where
    copyProp' (Assign x op) f = iAssign x <$> copyPropOp (Proxy :: Proxy lhs) op f


instance (IntVarLattice lhs :@ f, Var :<: rhs, lhs :<: rhs, Ord (lhs IntT))  
         => CopyPropOp ArithOp f lhs rhs where
    copyPropOp _ n f = case n of
                        Add y z -> Add <$> li y <*> li z
                        Mul y z -> Mul <$> li y <*> li z
                        Neg y   -> Neg <$> li y
       where li x = lookupVL (Proxy :: Proxy lhs) (x :: rhs IntT) f
	   
instance (BoolVarLattice lhs :@ f, Var :<: rhs, lhs :<: rhs, Ord (lhs BoolT))
         => CopyPropOp BoolOp f lhs rhs where
    copyPropOp _ n f = case n of
                        And y z -> And <$> lb y <*> lb z
                        Or y z -> Or <$> lb y <*> lb z
                        Not y -> Not <$> lb y
       where lb x = lookupVL (Proxy :: Proxy lhs) (x :: rhs BoolT) f

instance (IntVarLattice lhs :@ f, Var :<: rhs, lhs :<: rhs, Ord (lhs IntT))
         => CopyPropOp CompOp f lhs rhs where
    copyPropOp _ n f = case n of
                        Lte y z -> Lte <$> li y <*> li z
                        Lt y z  -> Lt <$> li y <*> li z
                        Equ y z -> Equ <$> li y <*> li z
       where li x = lookupVL (Proxy :: Proxy lhs) (x :: rhs IntT) f
	   
instance (BoolVarLattice lhs :@ f, Var :<: rhs, lhs :<: rhs, Ord (lhs BoolT))
         => CopyPropOp CopyOpB f lhs rhs where
    copyPropOp _ (Copy y) f = Copy <$> lb y
       where lb x = lookupVL (Proxy :: Proxy lhs) (x :: rhs BoolT) f

instance (IntVarLattice lhs :@ f, Var :<: rhs, lhs :<: rhs, Ord (lhs IntT))
         => CopyPropOp CopyOpI f lhs rhs where
    copyPropOp _ (Copy y) f = Copy <$> lb y
       where lb x = lookupVL (Proxy :: Proxy lhs) (x :: rhs IntT) f

instance (BoolVarLattice lhs :@ f, Cond :< n, Var :<: rhs, lhs :<: rhs, Ord (lhs BoolT))
         => CopyProp Cond n f lhs rhs where
    copyProp' (Cond x t e) f = (\ x -> iCond x t e) <$> lb x
       where lb x = lookupVL (Proxy :: Proxy lhs) (x :: rhs BoolT) f
					  
instance CopyProp Halt n f lhs rhs where
    copyProp _ _ = Nothing

instance CopyProp Jump n f lhs rhs where
    copyProp _ _ = Nothing

