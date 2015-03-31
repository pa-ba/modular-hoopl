{-# LANGUAGE MultiParamTypeClasses, TypeOperators, FlexibleInstances, GADTs, FlexibleContexts,
             FunctionalDependencies, GeneralizedNewtypeDeriving, KindSignatures, PackageImports,
             UndecidableInstances #-}

module Compiler where

import TargetSyntax as TGT
import SourceSyntax as SRC

import Control.Monad
import Compiler.Hoopl.Internals
import Graph


infixl 0  |>
(|>) :: (Monad m, NonLocal n) => m (Graph n e c) 
     -> m (Graph n c x) -> m (Graph n e x)
(|>) c d = liftM2 gSplice c d 

(|#>) :: (Monad m, NonLocal n) => m (Graph n e c) 
     -> (Graph n c x) -> m (Graph n e x)
(|#>) c d = liftM (`gSplice` d) c


data Res lhs l where
    Here :: lhs t  -> Res lhs (Exp t)
    None :: Res lhs Stmt

newtype F t lhs rhs l = F (Res lhs l -> Code t lhs rhs -> SimpleUniqueMonad (Code t lhs rhs))



class (HFunctor s) => CompAlg s lhs rhs t where
  compAlg :: s (F t lhs rhs) l -> Res lhs l -> Code t lhs rhs -> SimpleUniqueMonad (Code t lhs rhs)


compAlg' :: CompAlg s lhs rhs t => s (F t lhs rhs) :-> F t lhs rhs
compAlg' x = F (compAlg x)

instance (CompAlg f lhs rhs g, CompAlg h lhs rhs g) => CompAlg (f ::+ h) lhs rhs g where
  compAlg (HInl x)     = compAlg x
  compAlg (HInr y)     = compAlg y

freshTmp  :: UniqueMonad m => m (Tmp i)
freshTmp = liftM Tmp freshUnique

freshTmp2 :: UniqueMonad m => m (Tmp i, Tmp j)
freshTmp2 = do x <- freshTmp
               y <- freshTmp
               return (x,y)

freshLabel3 :: UniqueMonad m => m (Label, Label, Label)
freshLabel3 = do x <- freshLabel
                 y <- freshLabel
                 z <- freshLabel
                 return (x,y,z)


instance (CopyI :< t, Const :<: rhs, Tmp :<: lhs, Tmp :<: rhs, lhs :<: rhs, 
          TGT.Arith :< t, NonLocal (t Label lhs rhs)) 
    => CompAlg SRC.Arith lhs rhs t where
  compAlg (Val n) (Here v) c = return $ iCopy v (iConst n) <*> c
  compAlg (SRC.Add (F x) (F y)) (Here v) c = binOp iAdd v x y c
  compAlg (SRC.Mul (F x) (F y)) (Here v) c = binOp iMul v x y c

-- Due to a bug (cf. https://ghc.haskell.org/trac/ghc/ticket/3927),
-- GHC still emits warnings about non-exhaustive pattern matches in
-- the above definition for compAlg. The same applies also to the
-- remaining instance declarations of CompAlg.


instance (NonLocal (t Label lhs rhs), CopyI :< t, TGT.Var :<: rhs, TGT.Var :<: lhs)
    => CompAlg State lhs rhs t where
  compAlg (Get (SRC.Var var)) (Here v) c = return (iCopy v (iVar var)) |#> c
  compAlg (Set (SRC.Var var) (F x)) _  c = x (Here (iVar var)) c

instance (NonLocal (t Label lhs rhs), Jump :< t, Cond :< t, Tmp :<: rhs, Tmp :<: lhs) 
    => CompAlg While lhs rhs t where
  compAlg (While (F ch) (F b)) _ c = do {(l1, l2, l3) <- freshLabel3; v <- freshTmp;
     return (iJump l1) |#> iTarget l1 |> ch (Here $ inj v) (iCond (inj v) l2 l3) |#> iTarget l2 
                                  |> b None (iJump l1) |#> iTarget l3 |#> c}

instance (NonLocal (t Label lhs rhs)) => CompAlg Seq lhs rhs t where
  compAlg (Seq (F s1) (F s2)) x c = s1 None =<< s2 x c


instance (NonLocal (t Label lhs rhs), Tmp :<: lhs, Tmp :<: rhs, Cond :< t, Jump :< t)
    => CompAlg If lhs rhs t where
  compAlg (If (F e) (F e1) (F e2)) x c = do {(l1, l2, l3) <- freshLabel3; v <- freshTmp;
     e (Here $ inj v) (iCond (inj v) l1 l2) |#> iTarget l1 |> e1 x (iJump l3)
                      |#> iTarget l2 |> e2 x (iJump l3) |#> iTarget l3 |#> c }

instance (CopyB :< t, BConst :<: rhs, Tmp :<: lhs, Tmp :<: rhs, lhs :<: rhs,
          TGT.Boolean :< t, NonLocal (t Label lhs rhs)) 
    => CompAlg SRC.Boolean lhs rhs t where
  compAlg (BVal b) (Here v) c = return  (iCopy v (iBConst b) <*> c)
  compAlg (SRC.And (F x) (F y)) (Here v) c = binOp iAnd v x y c
  compAlg (SRC.Or (F x) (F y)) (Here v) c = binOp iOr v x y c
  compAlg (SRC.Not (F x)) (Here v) c = upOp iNot v x c

instance (Tmp :<: lhs, Tmp :<: rhs, lhs :<: rhs,
          TGT.Comp :< t, NonLocal (t Label lhs rhs))
    => CompAlg SRC.Comp lhs rhs t where
  compAlg (SRC.Equ (F x) (F y)) (Here v) = binOp iEqu v x y
  compAlg (SRC.Lt (F x) (F y)) (Here v) = binOp iLt v x y

instance (TGT.Except :< t, Jump :< t, NonLocal (t Label lhs rhs))
    => CompAlg SRC.Except lhs rhs t where
  compAlg (SRC.Throw) _ c = return $ iThrow
  compAlg (SRC.Catch (F x) (F h)) _ c = do {(l1, l2, l3) <- freshLabel3; 
      return (iMark l1) |#> (iJump l2) |#> iTarget l1 |> h None (iJump l3) |#> iTarget l2 
                        |> x None (iUnmark `gSplice` iJump l3) |#> iTarget l3 |#> c}





upOp :: (NonLocal (t Label lhs rhs), Tmp :<: rhs, UniqueMonad m, Tmp :<: lhs) =>
     (lhs a -> rhs b -> Graph (t Label lhs rhs) O O)
     -> lhs a -> (Res lhs (Exp b) -> Code t lhs rhs -> m (Code t lhs rhs))
     -> Code t lhs rhs ->  m (Code t lhs rhs)
upOp op v x c = do xv <- freshTmp
                   x (Here $ inj xv) (op v (inj xv) <*> c)


binOp  :: (NonLocal (t Label lhs rhs), UniqueMonad m, Tmp :<: lhs, lhs :<: rhs, Tmp :<: rhs) =>
     (lhs a -> rhs b -> rhs c -> Graph (t Label lhs rhs) O O)
     -> lhs a
     -> (Res lhs (Exp b) -> Code t lhs rhs -> m (Code t lhs rhs))
     -> (Res lhs (Exp c) -> Code t lhs rhs -> m (Code t lhs rhs))
     -> Code t lhs rhs
     -> m (Code t lhs rhs)
binOp op v x y c = do (xv,yv) <- freshTmp2
                      x (Here $ inj xv) =<< y (Here $ inj yv)  (op v (inj xv) (inj yv) <*> c)


-- The variants below reuse temporaries; should be avoided if the
-- target code is supposed to be in SSA form.

-- upOp' :: (NonLocal (t lhs rhs), lhs :<: rhs, Monad m) =>
--      (lhs a -> rhs a -> Code t lhs rhs)
--      -> lhs a -> (Res lhs (Exp a) -> m (Code t lhs rhs)) -> m (Code t lhs rhs)
-- upOp' op v x = x (Here v) |#> op v (inj v)


-- binOp'  :: (NonLocal (t lhs rhs), UniqueMonad m, Tmp :<: lhs, lhs :<: rhs, Tmp :<: rhs) =>
--      (lhs a -> rhs a -> rhs b -> Code t lhs rhs)
--      -> lhs a
--      -> (Res lhs (Exp a) -> m (Code t lhs rhs))
--      -> (Res lhs (Exp b) -> m (Code t lhs rhs))
--      -> m (Code t lhs rhs)
-- binOp' op v x y = do yv <- freshTmp
--                     x (Here v) |> y (Here $ inj yv) |#> op v (inj v) (inj yv)


comp :: (CompAlg s lhs rhs t, HFunctor s) => HFix s l -> Res lhs l -> Code t lhs rhs -> Code t lhs rhs
comp s r c = let F f = hfold compAlg' s in runSimpleUniqueMonad (f r c)

compStmt :: (CompAlg s lhs rhs t, HFunctor s, Halt :< t) => HFix s Stmt -> Code t lhs rhs
compStmt s = comp s None iHalt
