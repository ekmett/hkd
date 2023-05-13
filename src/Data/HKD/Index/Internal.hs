{-# Language GeneralizedNewtypeDeriving #-}
{-# Language ImportQualifiedPost #-}
{-# Language Unsafe #-}
{-# options_haddock not-home #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-style OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable

module Data.HKD.Index.Internal
( Index(UnsafeIndex,Index,IZ,IS,KnownIZ,KnownIS)
, lowerFin, liftFin
, pattern IntIndex
, toIndex
, Length
, KnownLength
, len
) where

import Control.Arrow (first)
import Data.Coerce
import Data.GADT.Compare
import Data.GADT.Show
import Data.Proxy
import Data.Kind
import Data.Some
import Data.Type.Coercion
import Data.Type.Equality
import GHC.TypeLits
import GHC.TypeNats qualified as TN
import Numeric.Fin.Internal
import Unsafe.Coerce

type role Index nominal nominal

type family Length (as :: [i]) :: Nat where
  Length '[] = 0
  Length (x ': xs) = 1 + Length xs

newtype Index (as :: [i]) (a :: i) = UnsafeIndex { fromIndex :: Int }
  deriving newtype (Eq, Ord, Show)

pattern Index :: Int -> Index as i
pattern Index i <- UnsafeIndex i
{-# complete Index #-}

len :: forall as. KnownLength as => Int
len = int @(Length as)
{-# inline len #-}

liftFin :: forall i (as :: [i]). Fin (Length as) -> Some (Index as)
liftFin = \(Fin i) -> Some (UnsafeIndex i)
{-# inline liftFin #-}

lowerFin :: forall i (as :: [i]) (a :: i). Index as a -> Fin (Length as)
lowerFin = coerce
{-# inline lowerFin #-}

type role Index' nominal nominal
data Index' :: [i] -> i -> Type where
  IZ' :: Index' (a:as) a
  IS' :: Index as a -> Index' (b:as) a

type KnownLength (as :: [i]) = KnownNat (Length as)

pattern IntIndex
  :: forall i (as :: [i]). KnownLength as
  => forall (a :: i). Index as a -> Int
pattern IntIndex i <- (toIndex -> Just (Some i)) where
  IntIndex i = fromIndex i

toIndex :: KnownLength is => Int -> Maybe (Some (Index is))
toIndex = fmap liftFin . toFin
{-# inline toIndex #-}

upIndex :: Index is i -> Index' is i
upIndex (Index 0) = unsafeCoerce IZ'
upIndex (Index n) = unsafeCoerce $ IS' $ UnsafeIndex (n - 1)
{-# inline[0] upIndex #-}

pattern IZ :: () => forall bs. as ~ (a:bs) => Index as a
pattern IZ <- (upIndex -> IZ') where
  IZ = UnsafeIndex 0

pattern IS :: () => forall bs. as ~ (b:bs) => Index bs a -> Index as a
pattern IS n <- (upIndex -> IS' n) where
  IS n = UnsafeIndex (fromIndex n + 1)
{-# complete IZ, IS #-}

type role KnownIndex' nominal nominal
data KnownIndex' :: [i] -> i -> Type where
  KnownIZ' :: KnownLength as => KnownIndex' (a:as) a
  KnownIS' :: KnownLength as => Index as a -> KnownIndex' (b:as) a

upKnownIndex :: forall is i. KnownLength is => Index is i -> KnownIndex' is i
upKnownIndex = case TN.someNatVal $ TN.natVal (Proxy :: Proxy (Length is)) - 1 of
   SomeNat (Proxy :: Proxy n) -> case unsafeCoerce Refl of
     (Refl :: n :~: Length js) -> case unsafeCoerce Refl of
       (Refl :: (is :~: (j ': js))) -> case unsafeCoerce Refl of
         (Refl :: (Length is :~: S (Length js))) -> \case
           UnsafeIndex 0 -> case unsafeCoerce Refl of
             (Refl :: j :~: i) -> (KnownIZ' :: KnownIndex' is i)
           UnsafeIndex n -> (KnownIS' $ UnsafeIndex (n-1) :: KnownIndex' is i)
{-# inline[0] upKnownIndex #-}

pattern KnownIZ :: KnownLength is => forall js j. (KnownLength js, is ~ j ': js) => Index is i
pattern KnownIZ <- (upKnownIndex -> KnownIZ') where
  KnownIZ = UnsafeIndex 0

pattern KnownIS :: KnownLength is => forall js j. (KnownLength js, is ~ j ': js) => Index js i -> Index is i
pattern KnownIS n <- (upKnownIndex -> KnownIS' n) where
  KnownIS n = UnsafeIndex (fromIndex n + 1)
{-# complete KnownIZ, KnownIS #-}


instance GEq (Index is) where
  geq = \(Index i) (Index j) ->
    if i == j
    then Just (unsafeCoerce Refl)
    else Nothing
  {-# inline geq #-}

instance GCompare (Index is) where
  gcompare = \(Index i) (Index j) ->
    case compare i j of
      LT -> GLT
      EQ -> unsafeCoerce GEQ
      GT -> GGT
  {-# inline gcompare #-}

instance TestEquality (Index is) where
  testEquality = geq
  {-# inline testEquality #-}

instance TestCoercion (Index is) where
  testCoercion = \x y -> repr <$> geq x y
  {-# inline testCoercion #-}

instance GShow (Index as) where
  gshowsPrec = showsPrec
  {-# inline gshowsPrec #-}

instance KnownLength as => GRead (Index as) where
  greadsPrec = \ d s -> first (liftFinWith mkGReadResult) <$> readsPrec d s

liftFinWith :: forall i (as :: [i]) f. (forall (x :: i -> Type) (a :: i). x a -> f x) -> Fin (Length as) -> f (Index as)
liftFinWith = \ f (Fin i) -> f (UnsafeIndex i)
{-# inline liftFinWith #-}

