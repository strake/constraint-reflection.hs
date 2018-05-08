{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies, RankNTypes, DefaultSignatures, TypeApplications, UndecidableInstances, PackageImports #-}

module Data.Reflection.Constraint where

import Prelude hiding (Functor, (<$>), map)
import Control.Categorical.Functor
import Data.Constraint
import Data.Function (on)
import Data.Morphism.Iso
import Data.Proxy
import Data.Reflection (Reifies (..), reify)

newtype Reflected c s a = Reflected { unReflected :: a }

unReflected' :: proxy s -> Reflected c s a -> a
unReflected' _ = unReflected

class Functor (Iso (->)) (->) (Methods c) => Reifiable c where
    data Methods c a
    reifiable :: Reifies s (Methods c a) => Dict (c (Reflected c s a))
    default reifiable :: c (Reflected c s a) => Dict (c (Reflected c s a))
    reifiable = Dict

reifiable' :: (Reifiable c, Reifies s (Methods c a)) => proxy s -> Dict (c (Reflected c s a))
reifiable' _ = reifiable

by :: ∀ c f a . (Reifiable c, Functor (Iso (->)) (->) f) => Methods c a -> (∀ a . c a => f a) -> f a
by methods a = reify methods (\ proxy -> Iso (unReflected' proxy) (Reflected @c) <$> withDict (reifiable' proxy) a)

instance Reifiable Eq  where newtype Methods Eq  a = EqMethods  { eqMethod      :: a -> a -> Bool }
instance Reifiable Ord where newtype Methods Ord a = OrdMethods { compareMethod :: a -> a -> Ordering }

instance Reifiable Semigroup where newtype Methods Semigroup a = SemigroupMethods { combineMethod :: a -> a -> a }
instance Reifiable Monoid    where data    Methods Monoid    a = MonoidMethods    { semigroupMethods :: Methods Semigroup a
                                                                                  , memptyMethod :: a }

instance {-# OVERLAPPING #-} Functor (Iso (->)) (->) (Methods Ord) where map (Iso _ f) (OrdMethods cmp) = OrdMethods (cmp `on` f)
instance {-# OVERLAPPING #-} Functor (Iso (->)) (->) (Methods Eq)  where map (Iso _ f) (EqMethods  eq)  = EqMethods  (eq  `on` f)

instance {-# OVERLAPPING #-} Functor (Iso (->)) (->) (Methods Semigroup) where map (Iso f f') (SemigroupMethods (<>))  = SemigroupMethods (\ a b -> f (f' a <> f' b))
instance {-# OVERLAPPING #-} Functor (Iso (->)) (->) (Methods Monoid)    where map φ@(Iso f _) (MonoidMethods sg mempty)  = MonoidMethods (φ <$> sg) (f mempty)

instance Reifies s (Methods Eq a) => Eq (Reflected Eq s a) where
    (==) = (eqMethod . reflect) (Proxy @s) `on` unReflected

instance Reifies s (Methods Ord a) => Eq (Reflected Ord s a) where
    x == y = EQ == compare x y

instance Reifies s (Methods Ord a) => Ord (Reflected Ord s a) where
    compare = (compareMethod . reflect) (Proxy @s) `on` unReflected

instance Reifies s (Methods Semigroup a) => Semigroup (Reflected Semigroup s a) where
    a <> b = Reflected $ ((combineMethod . reflect) (Proxy @s) `on` unReflected) a b

instance Reifies s (Methods Monoid a) => Semigroup (Reflected Monoid s a) where
    a <> b = Reflected $ ((combineMethod . semigroupMethods . reflect) (Proxy @s) `on` unReflected) a b

instance Reifies s (Methods Monoid a) => Monoid (Reflected Monoid s a) where
    mempty = Reflected $ (memptyMethod . reflect) (Proxy @s)
