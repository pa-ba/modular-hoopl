{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}

import SCompiler
import SourceSyntax as SRC
import TargetSyntax as TGT
import Graph
import Lattice
import qualified Data.Map as Map
import qualified Data.Set as S
import PrettyPrint ()

import ConstantPropagation
import ConstantFolding
import CopyPropagation
import DeadCodeElimination

type Rhs = Const :+: BConst :+: Lhs
type Lhs = Tmp :+: TGT.Var

type Node = Jump :+ TGT.Boolean :+ TGT.Arith :+ Cond :+ CopyI :+ CopyB
    :+ TGT.Comp :+ Halt


compFull :: HFix (SRC.Arith ::+ State ::+ While ::+ SRC.Comp ::+ SRC.Boolean ::+ If ::+ Seq) Stmt -> Code Node Lhs Rhs
compFull = compStmt


x = SRC.Var "x"
y = SRC.Var "y"
z = SRC.Var "z"


exFact = compFull $
         setF y (valF 1) `seqF` 
         whileF (valF 0 `ltF` getF x)
           (setF y (getF y `mulF` getF x) `seqF` 
            setF x (getF x `addF` valF (-1)) )


tmp :: SRC.Var
tmp = SRC.Var "tmp"
		 
exGCD = compFull $
        setF z (valF 1) `seqF` 
		(
         whileF (notF (getF z `equF` getF x)) $ -- while z /= x 
			ifF (getF x `equF` getF y) 
				(setF z (getF x)) $ -- i.e. x == y, then set z to x
			ifF (getF x `ltF` getF y) 
				(setF tmp (getF x) `seqF` setF x (getF y) `seqF` setF y (getF tmp))  -- i.e. x < y, iterate with gcd y x
				(setF tmp (getF y `mulF` valF (-1)) `seqF` setF x (getF x `addF` (getF tmp)))
		) -- otherwise, y < x, iterate with gcd (x - y) y

-- instantiate the transfer function for the example language
constPropPass :: FuelMonad m => FwdPass m (Node Label Lhs Rhs) (IntConstLattice Lhs, BoolConstLattice Lhs)
constPropPass = FwdPass {
                  fp_lattice = pairLattice (flatMapLattice "Int") (flatMapLattice "Bool"),
                  fp_transfer = constPropTrans',
                  fp_rewrite = constPropRewrite }


runInfFuel :: InfiniteFuelMonad SimpleUniqueMonad a -> a
runInfFuel = runSimpleUniqueMonad . runWithFuel infiniteFuel

applyConstProp :: Graph (Node Label Lhs Rhs) O x 
               -> (Graph (Node Label Lhs Rhs) O x, FactBase (IntConstLattice Lhs, BoolConstLattice Lhs),
                           MaybeO x (IntConstLattice Lhs, BoolConstLattice Lhs)) 
applyConstProp g = runInfFuel $ 
                   analyzeAndRewriteFwd constPropPass (NothingC :: MaybeC O Label) g (Map.empty,Map.empty)



-- instantiate the transfer function for the example language
constFoldPass :: forall m . FuelMonad m => 
                 FwdPass m (Node Label Lhs Rhs) (IntConstLattice Lhs, BoolConstLattice Lhs)
constFoldPass = (constPropPass :: FwdPass m (Node Label Lhs Rhs) (IntConstLattice Lhs, BoolConstLattice Lhs))
                {fp_rewrite = fp_rewrite constPropPass `thenFwdRw` constFoldRewrite}


-- | Applies constant propagation followed by constant folding

applyConstFold :: Graph (Node Label Lhs Rhs) O x 
               -> (Graph (Node Label Lhs Rhs) O x, FactBase (IntConstLattice Lhs, BoolConstLattice Lhs),
                           MaybeO x (IntConstLattice Lhs, BoolConstLattice Lhs)) 
applyConstFold g = runInfFuel $ 
                   analyzeAndRewriteFwd constFoldPass (NothingC :: MaybeC O Label) g (Map.empty,Map.empty)
				   
copyPropPass :: forall m . FuelMonad m => 
				FwdPass m (Node Label Lhs Rhs) (IntVarLattice Lhs, BoolVarLattice Lhs)
copyPropPass = FwdPass {
                  fp_lattice  = pairLattice (flatMapLattice "IntT") (flatMapLattice "BoolT"),
                  fp_transfer = copyPropTrans',
                  fp_rewrite  = copyPropRewrite
				  }
				  
applyCopyProp :: Graph (Node Label Lhs Rhs) O x 
             -> (Graph (Node Label Lhs Rhs) O x, FactBase (IntVarLattice Lhs, BoolVarLattice Lhs),
                           MaybeO x (IntVarLattice Lhs, BoolVarLattice Lhs)) 
applyCopyProp g = runInfFuel $ 
                   analyzeAndRewriteFwd copyPropPass (NothingC :: MaybeC O Label) g (Map.empty, Map.empty)
				  
deadCodePass :: forall m . FuelMonad m =>
				BwdPass m (Node Label Lhs Rhs) Live
deadCodePass = BwdPass {
					bp_lattice  = liveLattice,
					bp_transfer = livenessTrans',
					bp_rewrite  = undefined -- deadCodeRewrite
				}

