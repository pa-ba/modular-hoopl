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
			 IncoherentInstances,
             DefaultSignatures #-}

module DeadCodeElimination where

import TargetSyntax hiding ((<*>))
import Lattice
import Data.Map (Map)
import qualified Data.Set as S
import qualified Data.Map as Map
import Control.Monad
import Control.Applicative hiding (Const)
import Data.Monoid
import Graph
import Data.Maybe (catMaybes, fromMaybe)

data Proxy (t :: k) = Proxy

toChangeFlag :: t -> Maybe t -> (ChangeFlag, t)
toChangeFlag d m = case m of
                    Just n -> (SomeChange, n)
                    Nothing -> (NoChange, d)

type Live = S.Set String
liveLattice :: DataflowLattice Live
liveLattice = DataflowLattice
  { fact_name = "Live Variables [String References]"
  , fact_bot  = S.empty
  , fact_join = add
  }
    where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `S.union` old
              ch = changeIf (S.size j > S.size old)
			  
---------------------------------
{- 
   LivenessTrans defines the dead code transfer function, which takes a node and returns a fact transformer, taking 
   a fact flowing into the node and returns the transformed fact that flows out of the node.

fold_EE :: (a -> Expr -> a) -> a -> Expr      -> a
fold_EE f z e@(Lit _)         = f z e
fold_EE f z e@(Var _)         = f z e
fold_EE f z e@(Load addr)     = f (f z addr) e
fold_EE f z e@(Binop _ e1 e2) = f (f (f z e2) e1) e

fold_EN :: (a -> Expr -> a) -> a -> Insn e x -> a
fold_EN _ z (Label _)       = z
fold_EN f z (Assign _ e)    = f z e

addVar :: (S.Set Live -> Expr -> S.Set Live)
addVar s (Var v) = S.insert v s
addVar s _       = s     

I'm not sure if the VariableSet class is what we want, and we're breaking modularity here anyway.
I just want to get this to work for a start. ;_:

 -}

class VariableSet n l r where
  addUses :: Live -> n Label l r e x -> Live
  default addUses :: Live -> n Label l r e x -> Live; addUses = foldEN (foldEE addVar)
  addVar  :: Live -> n Label l r e x -> Live
  foldEE :: (Live -> n Label l r e x -> Live) -> Live -> n Label l r e x -> Live
  foldEN :: (Live -> n Label l r e x -> Live) -> Live -> n Label l r e x -> Live
  
instance (VariableSet n l r, VariableSet m l r) => VariableSet (n :+ m) l r where 
  addVar f (Innl x) = addVar f x
  addVar g (Innr y) = addVar g y
  -- do we need some defaults for the foldEE and foldEN?
  
instance VariableSet n l r where
  addVar = undefined
  foldEE = undefined
  foldEN = undefined
 
class LivenessTrans n l r f where 
    livenessTrans  :: n Label l r e O -> f -> f
    livenessTransC :: n Label l r O C -> FactBase f -> f

    default livenessTransC :: NonLocal (n Label l r) => n Label l r O C -> FactBase f -> f;
    livenessTransC n fb = undefined -- addUses (S.unions $ map (\l -> fact fb l) (successors n)) n
	-- if we can treat f as a Live set then the commented out code works as a default.

livenessTrans' :: (NonLocal (n Label l r), LivenessTrans n l r f) => BwdTransfer (n Label l r) f
livenessTrans' = mkBTransfer3 livenessTrans livenessTrans livenessTransC

instance (LivenessTrans n l r f, LivenessTrans m l r f) => LivenessTrans (n :+ m) l r f where
    livenessTrans (Innl x)  = livenessTrans x
    livenessTrans (Innr x)  = livenessTrans x
    livenessTransC (Innl x) = livenessTransC x
    livenessTransC (Innr x) = livenessTransC x
	
instance (Ord (lhs IntT), Var :<: lhs) => LivenessTrans (AssignI CopyOpI) lhs rhs Live where
    livenessTrans n@(Assign t _) f = case prj t of Just (TargetSyntax.Var v) -> addUses (S.delete v f) n; _ -> f
	
instance (Ord (lhs BoolT), Var :<: lhs) => LivenessTrans (AssignB CopyOpB) lhs rhs Live where
    livenessTrans n@(Assign t _) f = case prj t of Just (TargetSyntax.Var v) -> addUses (S.delete v f) n; _ -> f

instance (lhs :<: rhs, Ord (lhs BoolT)) => LivenessTrans Cond lhs rhs Live where
    livenessTrans _                   = id
    livenessTransC n@(Cond _ l1 l2) f = addUses (fact f l1 `S.union` fact f l2) n
								
instance NonLocal (n Label l r) => LivenessTrans n l r f where
    livenessTrans _ = id
	
fact :: FactBase Live -> Label -> Live
fact f l = fromMaybe S.empty (lookupFact l f)

---------------------------------

{- DeadCode implements the rewrite function, which takes a node and an input fact, and performs a monadic
   action resulting from the rewrite [either Nothing or Just GNil].
   This is complete. Just need to work on this accursed transfer function now. -}

data  Status = Living | Dead
class DeadCode n f lhs rhs where
    deadCode  :: n Label lhs rhs O O -> f -> Status
	
instance (DeadCode n1 f lhs rhs, DeadCode n2 f lhs rhs) => DeadCode (n1 :+ n2) f lhs rhs where
    deadCode (Innl x) = deadCode x
    deadCode (Innr x) = deadCode x
	
instance (Var :<: lhs) => DeadCode (AssignB CopyOpB) Live lhs rhs where
    deadCode (Assign x _) f = case prj x of Just (TargetSyntax.Var v) -> (case v `S.member` f of True -> Living; False -> Dead);
											_ -> Living;
	
instance (Var :<: lhs) => DeadCode (AssignI CopyOpI) Live lhs rhs where
    deadCode (Assign y _) f = case prj y of Just (TargetSyntax.Var v) -> (case v `S.member` f of True -> Living; False -> Dead);
											_ -> Living;

instance DeadCode n f l r where
    deadCode _ _ = Living
	
embed :: forall n . Status -> Maybe (Graph n O O)
embed Living = Nothing
embed Dead   = Just GNil
	
deadCodeRewrite :: (FuelMonad m, DeadCode n f lhs rhs) => BwdRewrite m (n Label lhs rhs) f
deadCodeRewrite = mkBRewrite3 (\_ _ -> return Nothing) (\n f -> return (embed (deadCode n f))) (\_ _ -> return Nothing)
	
-----------------------------------

