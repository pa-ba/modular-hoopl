{-# LANGUAGE KindSignatures, TypeOperators #-}

module NFunctor where

import Data.Traversable
import Data.Foldable
import Control.Applicative
import Control.Monad

import Nodes

import Compiler.Hoopl hiding ((<*>))

data Func n (l :: * -> *) (r :: * -> *) e = FuncO (n e l r O O) e
                  | FuncC (n e l r O C)


class NFunctor (n :: * -> (* -> *) -> (* -> *) -> * -> * -> *) where
    nfmap :: (a -> b) -> n a l r e x -> n b l r e x

instance NFunctor n => Functor (Func n l r) where
    fmap f (FuncO n e) = FuncO (nfmap f n) (f e)
    fmap f (FuncC n) = FuncC (nfmap f n)

class NFoldable (n :: * -> (* -> *) -> (* -> *) -> * -> * -> *) where
    nfoldr :: (a -> b -> b) -> b -> n a l r e x -> b 

instance NFoldable n => Foldable (Func n l r) where
    foldr f z (FuncO n e) =  nfoldr f (f e z) n
    foldr f z (FuncC n) = nfoldr f z n

class (NFunctor n, NFoldable n) => 
    NTraversable (n :: * -> (* -> *) -> (* -> *) -> * -> * -> *) where 
    ntraverse :: Applicative f => (a -> f b) -> n a l r e x -> f (n b l r e x)
    nmapM :: Monad m => (a -> m b) -> n a l r e x -> m (n b l r e x) 


instance NTraversable n => Traversable (Func n  l r) where
    traverse f (FuncO n e) = FuncO <$> (ntraverse f n) <*> f e
    traverse f (FuncC n) = FuncC <$> (ntraverse f n)

    mapM f (FuncO n e) = liftM2 FuncO (nmapM f n) (f e)
    mapM f (FuncC n) = liftM FuncC (nmapM f n)


instance (NFunctor n, NFunctor m) => NFunctor (n :+ m) where
    nfmap f (Innl x) = Innl $ nfmap f x
    nfmap f (Innr x) = Innr $ nfmap f x

instance (NFoldable n, NFoldable m) => NFoldable (n :+ m) where
    nfoldr f z (Innl x) = nfoldr f z x
    nfoldr f z (Innr x) = nfoldr f z x

instance (NTraversable n, NTraversable m) => NTraversable (n :+ m) where
    ntraverse f (Innl x) = Innl <$> ntraverse f x
    ntraverse f (Innr x) = Innr <$> ntraverse f x

    nmapM f (Innl x) = Innl `liftM` nmapM f x
    nmapM f (Innr x) = Innr `liftM` nmapM f x
