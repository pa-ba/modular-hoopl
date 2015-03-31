{-# LANGUAGE MultiParamTypeClasses, TypeOperators, FlexibleInstances, GADTs, FlexibleContexts,
             FunctionalDependencies, GeneralizedNewtypeDeriving, KindSignatures, PackageImports,
             UndecidableInstances #-}

module SCompiler where

import TargetSyntax as TGT
import SourceSyntax as SRC

import Graph
import NFunctor


gCopy x y c = injectOp x (Copy y) c
gAdd x y z c = injectOp x (TGT.Add y z) c
gMul x y z c = injectOp x (TGT.Mul y z) c
gAnd x y z c = injectOp x (TGT.And y z) c
gOr x y z c = injectOp x (TGT.Or y z) c
gNot x y c = injectOp x (TGT.Not y) c
gCond x y z = injectC (TGT.Cond x y z)
gEqu x y z c = injectOp x (TGT.Equ y z) c
gLt x y z c = injectOp x (TGT.Lt y z) c
gMark x c = injectO (TGT.Mark x) c
gUnmark c = injectO TGT.Unmark c
gThrow :: (TGT.Except :< n) => SCodeT n lhs rhs v
gThrow = injectC TGT.Throw
gHalt :: (TGT.Halt :< n) => SCodeT n lhs rhs v
gHalt = injectC TGT.Halt

freshTmp :: (Tmp i -> SGraphT f v) -> SGraphT f v
freshTmp f = Fresh (f . Tmp)

freshTmp2 :: (Tmp i -> Tmp i -> SGraphT f v) -> SGraphT f v
freshTmp2 f = freshTmp (\x -> freshTmp (\ y -> f x y))

data Res lhs l where
    Here :: lhs t  -> Res lhs (Exp t)
    None :: Res lhs Stmt

newtype F t lhs rhs v l = F (Res lhs l -> SCodeT t lhs rhs v -> SCodeT t lhs rhs v)



class (HFunctor s) => CompAlg s lhs rhs t where
  compAlg :: s (F t lhs rhs v) l -> Res lhs l -> SCodeT t lhs rhs v -> SCodeT t lhs rhs v


compAlg' :: CompAlg s lhs rhs t => s (F t lhs rhs v) :-> F t lhs rhs v
compAlg' x = F (compAlg x)

instance (CompAlg f lhs rhs g, CompAlg h lhs rhs g) => CompAlg (f ::+ h) lhs rhs g where
  compAlg (HInl x)     = compAlg x
  compAlg (HInr y)     = compAlg y


instance (CopyI :< t, Const :<: rhs, Tmp :<: lhs, Tmp :<: rhs, lhs :<: rhs, TGT.Arith :< t) 
    => CompAlg SRC.Arith lhs rhs t where
  compAlg (Val n) (Here v) c = gCopy v (iConst n) c
  compAlg (SRC.Add (F x) (F y)) (Here v) c = binOp gAdd v x y c
  compAlg (SRC.Mul (F x) (F y)) (Here v) c = binOp gMul v x y c

-- Due to a bug (cf. https://ghc.haskell.org/trac/ghc/ticket/3927),
-- GHC still emits warnings about non-exhaustive pattern matches in
-- the above definition for compAlg. The same applies also to the
-- remaining instance declarations of CompAlg.


instance (CopyI :< t, TGT.Var :<: rhs, TGT.Var :<: lhs)
    => CompAlg State lhs rhs t where
  compAlg (Get (SRC.Var var)) (Here v) c = (gCopy v (iVar var)) c
  compAlg (Set (SRC.Var var) (F x)) _ c = x (Here (iVar var)) c

instance (Cond :< t, Tmp :<: rhs, Tmp :<: lhs) 
    => CompAlg While lhs rhs t where
  compAlg (While (F ch) (F b)) _ c = freshTmp $ \ v ->
     mu (\ l -> ch (Here $ inj v) $ gCond (inj v) (b None l) c)


instance CompAlg Seq lhs rhs t where
  compAlg (Seq (F s1) (F s2)) x c = s1 None $ s2 x $ c


instance (Tmp :<: lhs, Tmp :<: rhs, Cond :< t)
    => CompAlg If lhs rhs t where
  compAlg (If (F e) (F e1) (F e2)) x c = freshTmp $ \ v-> 
     e (Here $ inj v) $ gCond (inj v) (e1 x c) (e2 x c)

instance (CopyB :< t, BConst :<: rhs, Tmp :<: lhs, Tmp :<: rhs, lhs :<: rhs,
          TGT.Boolean :< t, NonLocal (t Label lhs rhs)) 
    => CompAlg SRC.Boolean lhs rhs t where
  compAlg (BVal b) (Here v) c = gCopy v (iBConst b) c
  compAlg (SRC.And (F x) (F y)) (Here v) c = binOp gAnd v x y c
  compAlg (SRC.Or (F x) (F y)) (Here v) c = binOp gOr v x y c
  compAlg (SRC.Not (F x)) (Here v) c = upOp gNot v x c

instance (Tmp :<: lhs, Tmp :<: rhs, lhs :<: rhs,
          TGT.Comp :< t, NonLocal (t Label lhs rhs))
    => CompAlg SRC.Comp lhs rhs t where
  compAlg (SRC.Equ (F x) (F y)) (Here v) c = binOp gEqu v x y c
  compAlg (SRC.Lt (F x) (F y)) (Here v) c = binOp gLt v x y c

instance (TGT.Except :< t)
    => CompAlg SRC.Except lhs rhs t where
  compAlg (SRC.Throw) _ _ = gThrow
  compAlg (SRC.Catch (F x) (F h)) _ c = 
      gMark (h None c) $ gUnmark $ x None $ c





upOp op v x c = freshTmp $ \ xv -> x (Here $ inj xv) $ op v (inj xv) $ c


binOp op v x y c = freshTmp2 $ \ xv yv ->
                  x (Here $ inj xv) $
                  y (Here $ inj yv) $
                  op v (inj xv) (inj yv) $ c


comp :: (CompAlg s lhs rhs t, HFunctor s) => HFix s l -> Res lhs l -> SCodeT t lhs rhs v -> SCodeT t lhs rhs v
comp s r c = let F f = hfold compAlg' s in f r c

compStmt' :: (CompAlg s lhs rhs t, HFunctor s, Halt :< t) => HFix s Stmt -> SCode t lhs rhs
compStmt' s = SGraph (comp s None gHalt)

compStmt :: (CompAlg s lhs rhs t, HFunctor s, Halt :< t, NTraversable t, NonLocal (t Label lhs rhs)) => HFix s Stmt -> Code (Jump :+ t) lhs rhs
compStmt = toHoopl . compStmt'
