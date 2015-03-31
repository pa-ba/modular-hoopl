{-# LANGUAGE KindSignatures, RankNTypes, GADTs, PolyKinds, TypeOperators, FlexibleContexts,
  FlexibleInstances, ScopedTypeVariables, StandaloneDeriving, DeriveFunctor, TemplateHaskell #-}

module Graph where

import Control.Monad.State hiding (mapM)
import Control.Monad.Writer hiding (mapM)
import Compiler.Hoopl.Internals
import Compiler.Hoopl hiding ((<*>))
import Data.List
import Nodes
import NFunctor
import Derive

data SGraphT f v = Var v
                | Mu ([v] -> [SGraphT f v])
                | Fresh (Unique -> SGraphT f v)
                | GIn (f (SGraphT f v))

newtype SGraph f = SGraph {unGraph :: forall v . SGraphT f v}

mu     :: (SGraphT f v -> SGraphT f v) -> SGraphT f v
mu f = Mu (\ ~(x : _) -> [f (Var x)])


type SCode n (lhs :: * -> *) (rhs :: * -> *) = SGraph (Func n lhs rhs)
type Code n (lhs :: * -> *) (rhs :: * -> *) = Graph (n Label lhs rhs) O C

type SCodeT n (lhs :: * -> *) (rhs :: * -> *) = SGraphT (Func n lhs rhs)


data Jump lab l r e x where
    Jump :: lab -> Jump lab l r O C
    Target :: lab -> Jump lab l r C O

deriving instance Show lab => Show (Jump lab l r e x)
instance NonLocal (Jump Label l r) where
    entryLabel (Target l) = l
    successors (Jump l) =[l]


iJump :: (Jump :< n) =>  Label -> Graph (n Label l r) O C
iJump = mkLast . injN . Jump
iTarget :: (Jump :< n) => Label -> Graph (n Label l r) C O
iTarget = mkFirst . injN . Target


data Assign i op lab lhs rhs e x where
    Assign :: lhs i -> op rhs i -> Assign i op lab lhs rhs O O

instance NonLocal (Assign i op lab lhs rhs) where
    -- None of the methods needs implementation, but GHC gives
    -- warnings anyway.
    entryLabel _ = undefined
    successors _ = undefined

iAssign x = mkMiddle . injN . Assign x


$(derive [makeNFunctor, makeNFoldable, makeNTraversable] 
    [''Jump, ''Assign])

injectOp :: (Assign i op :< m) => lhs i -> op rhs i -> SCodeT m lhs rhs v -> SCodeT m lhs rhs v
injectOp x op e = injectO (Assign x op) e

injectO :: (n :< m) => n (SCodeT m lhs rhs v) lhs rhs O O -> SCodeT m lhs rhs v -> SCodeT m lhs rhs v
injectO n e = GIn $ FuncO (injN n) e

injectC :: (n :< m) => n (SCodeT m lhs rhs v) lhs rhs O C -> SCodeT m lhs rhs v
injectC n = GIn $ FuncC (injN n)


gfold :: Functor f => (t -> c) -> ((Unique -> c) -> c) -> (([t] -> [c]) -> c) -> (f c -> c) -> SGraph f -> c
gfold v fr l f (SGraph g) = trans g where
   trans (Var x) = v x 
   trans (Fresh g) = fr (trans . g)
   trans (Mu g) = l (map trans . g)
   trans (GIn fa) = f (fmap trans fa)



lin :: NTraversable n => n (Fresh a) l r e x -> Fresh (n Label l r e x, [(Label,a)])
lin n = runWriterT (nmapM extract n)
        where extract r = do r' <- lift r 
                             (l:fresh) <- get
                             put fresh
                             tell [(l,r')]
                             return l

target :: (Jump :< n, NonLocal (n Label lhs rhs)) =>
          [(Label, Code n lhs rhs)] -> Code n lhs rhs -> Code n lhs rhs
target gs ent = foldl' (\ ent' (l, g) -> gSplice ent' $ 
                        gSplice (mkFirst $ injN $ Target l) g) ent gs



type Fresh = StateT [Label] SimpleUniqueMonad


toHoopl :: forall n lhs rhs . (NonLocal (n Label lhs rhs), NTraversable n) => 
           SCode n lhs rhs -> Code (Jump :+ n) lhs rhs
toHoopl g = fst $ runSimpleUniqueMonad $ flip runStateT labels $ gfold var fresh mu gin g
    where labels :: [Label]
          labels = fmap uniqueToLbl [0..]
          var :: Label -> Fresh (Code (Jump :+ n) lhs rhs)
          var l = return $ mkLast . injN . Jump $ l
          fresh :: (Unique -> Fresh (Code (Jump :+ n) lhs rhs)) -> Fresh (Code (Jump :+ n) lhs rhs)
          fresh f =  lift freshUnique >>= f
          mu :: ([Label] -> [Fresh (Code (Jump :+ n) lhs rhs)]) -> 
                Fresh (Code (Jump :+ n) lhs rhs)
          mu f = do fresh <- get
                    let mres = f fresh
                        n = length mres
                        (labs, fresh') = splitAt n fresh
                    let middle (l, f) = do g <- f
                                           return $ gSplice (mkFirst $ injN $ Target l) g
                    put fresh'
                    res <- mapM middle $ zip labs mres
                    return $ foldl (|*><*|) (mkLast . injN . Jump $ head labs) res
          gin :: Func n lhs rhs (Fresh (Code (Jump :+ n) lhs rhs))
                 -> Fresh (Code (Jump :+ n) lhs rhs)
          gin (FuncO n e) = do (n', mappings) <- lin n
                               e' <- e
                               return $ target mappings $ gSplice (mkMiddle (Innr n')) e' 
          gin (FuncC n) = do (n', mappings) <- lin n
                             return $ target mappings $ mkLast (Innr n')
