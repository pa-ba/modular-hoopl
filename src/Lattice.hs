{-# LANGUAGE TypeOperators, 
             MultiParamTypeClasses, 
             FlexibleInstances,
             OverlappingInstances,
             IncoherentInstances #-}

module Lattice where
import Compiler.Hoopl
import Data.Map (Map)
import qualified Data.Map as Map

--------------------
-- Modular tuples -- -- Stratego from Nijmegen/ Typed Assembly Language/Proof Carrying Code
--------------------

class a :@ b where
  pr  ::  b -> a
  modify :: (a -> a) -> b -> b

instance a :@ a where
    pr = id
    modify = id

instance (c :@ b) => c :@ (a,b) where
    pr = pr . snd
    modify f (a,b) = (a, modify f b)

instance a :@ (a,b) where
    pr = fst
    modify f (a,b) = (modify f a, b)

instance a :@ ((a,b),c) where
    pr = fst . fst
    modify f ((a,b),c) = ((f a,b),c)

instance b :@ ((a,b),c) where
    pr = snd . fst
    modify f ((a,b),c) = ((a,f b),c)

--------------------------
-- lattice construction --
--------------------------

flatJoin :: Eq a => Label -> OldFact a -> NewFact a -> (ChangeFlag, Pointed C b a)
flatJoin _ (OldFact old) (NewFact new)
               | old == new = (NoChange, PElem new)
               | otherwise  = (SomeChange, Top)

flatLattice :: Eq a => String -> DataflowLattice (Pointed C C a)
flatLattice name = addPoints' name flatJoin

flatMapLattice :: (Eq a, Ord k) => String -> DataflowLattice (Map k (WithTop a))
flatMapLattice name = DataflowLattice {
                        fact_name = name,
                        fact_bot = Map.empty,
                        fact_join = joinMaps $ extendJoinDomain flatJoin }

fromPointed :: Pointed t b a -> Maybe a
fromPointed (PElem x) = Just x
fromPointed _ = Nothing
