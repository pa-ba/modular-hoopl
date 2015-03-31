{-# LANGUAGE TypeOperators, 
             DeriveFunctor,
             FlexibleInstances,
             MultiParamTypeClasses, 
             OverlappingInstances,
             FlexibleContexts,
             RankNTypes,
             KindSignatures, 
             UndecidableInstances #-}


module HFixpoint where

------------------------------------
-- Modular functors/indexed types --
------------------------------------

infixr 8 ::+
data (f ::+ g) (h :: * -> *) e = HInl (f h e)
                               | HInr (g h e)


infixr 0 :-> -- same precedence as function space operator ->
infixr 0 :=> -- same precedence as function space operator ->
infixr 0 :~> -- same precedence as function space operator ->

-- | This type represents natural transformations.
type f :-> g = forall i . f i -> g i


-- | This type represents co-cones from @f@ to @a@. @f :=> a@ is
-- isomorphic to f :-> K a
type f :=> a = forall i . f i -> a

-- | This type represents natural transformations.
type f :~> g = forall i . f i -> Maybe (g i)



class HFunctor h where
    -- A higher-order functor @f@ maps every functor @g@ to a
    -- functor @f g@.
    --
    -- @ffmap :: (Functor g) => (a -> b) -> f g a -> f g b@
    -- 
    -- We omit this, as it does not work for GADTs (see Johann and
    -- Ghani 2008).

    -- | A higher-order functor @f@ also maps a natural transformation
    -- @g :-> h@ to a natural transformation @f g :-> f h@
    hfmap :: (f :-> g) -> h f :-> h g

instance (HFunctor f, HFunctor g) => HFunctor (f ::+ g) where
    hfmap f (HInl v) = HInl $ hfmap f v
    hfmap f (HInr v) = HInr $ hfmap f v

instance (Show (f a i), Show (g a i)) => Show ((f ::+ g) a i) where
    show (HInl x) = show x
    show (HInr x) = show x

instance Show (f (HFix f) i) => Show (HFix f i) where
    show (HIn f) = show f

-- |The subsumption relation.
class (sub :: (* -> *) -> * -> *) ::< sup where
    hinj :: sub a :-> sup a
    hprj :: sup a :~> sub a

instance (::<) f f where
    hinj = id
    hprj = Just

instance (::<) f (f ::+ g) where
    hinj = HInl
    hprj (HInl x) = Just x
    hprj (HInr _) = Nothing


instance (f ::< g) => (::<) f (h ::+ g) where
    hinj = HInr . hinj
    hprj (HInr x) = hprj x
    hprj (HInl _) = Nothing


data HFix f i = HIn (f (HFix f) i)

hinject :: (g ::< f) => g (HFix f) :-> HFix f
hinject = HIn . hinj


hfold :: HFunctor f => (f a :-> a) -> HFix f :-> a
hfold f (HIn t) =  f (hfmap (hfold f) t)

newtype K a i = K {unK :: a}
newtype (f :. g) i = C { unC :: f (g i)}
