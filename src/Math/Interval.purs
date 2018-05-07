module Math.Interval
  ( module Math.Interval
  , module ForReExport
  ) where

import Prelude

import Data.Generic (class Generic, gShow)
import Data.Lattice (meet)
import Data.Maybe (Maybe(..))
import Data.Ord (lessThanOrEq)
import Data.Tuple (Tuple(..))
import Math.Interval.Bound (Bound)
import Math.Interval.Bound as Bound
import Math.Interval.Internal (Interval(..))
import Math.Interval.Internal (Interval) as ForReExport
import Math.Interval.Openness (Openness(..))
import Partial.Unsafe (unsafeCrashWith)

make ::
     forall n. Ord n
  => Bound n
  -> Bound n
  -> Maybe (Interval n)
make lower upper
  | lower <= upper && upper /= Bound.NegInf && lower /= Bound.PosInf =
    Just (NonEmpty {lower, upper})
  | otherwise = Nothing

member :: forall n. Ord n => n -> Interval n -> Boolean
member _ Empty = false
member n (NonEmpty { lower, upper }) =
  n `Bound.greaterThanOrEq` lower && n `Bound.lessThanOrEq` upper

boundBelow :: forall n. Ord n => n -> Openness -> Interval n -> Maybe (Interval n)
boundBelow _ _ Empty = Nothing
boundBelow bound openness i@(NonEmpty { upper })
  | bound `member` i = Just $ NonEmpty { lower: Bound.Finite { bound, openness }, upper }
  | otherwise = Nothing

boundAbove :: forall n. Ord n => n -> Openness -> Interval n -> Maybe (Interval n)
boundAbove _ _ Empty = Nothing
boundAbove bound openness i@(NonEmpty { lower })
  | bound `member` i = Just $ NonEmpty { lower, upper: Bound.Finite { bound, openness } }
  | otherwise = Nothing

lessThanEverywhere :: forall a. Ord a => Interval a -> Interval a -> Boolean
lessThanEverywhere Empty _ = true
lessThanEverywhere _ Empty = true
lessThanEverywhere (NonEmpty { upper }) (NonEmpty { lower }) =
  case compare upper lower of
    GT -> false
    LT -> true
    EQ ->
      case Tuple upper lower of
        Tuple (Bound.Finite u) (Bound.Finite l) -> u.openness == Open || l.openness == Open
        _ -> unsafeCrashWith "lessThanEverywhere"
infix 4 lessThanEverywhere as <!

lessThanOrEqEverywhere :: forall a. Ord a => Interval a -> Interval a -> Boolean
lessThanOrEqEverywhere Empty _ = true
lessThanOrEqEverywhere _ Empty = true
lessThanOrEqEverywhere (NonEmpty { upper }) (NonEmpty { lower }) =
  upper `lessThanOrEq` lower
infix 4 lessThanOrEqEverywhere as <=!

greaterThanOrEqEverywhere :: forall a. Ord a => Interval a -> Interval a -> Boolean
greaterThanOrEqEverywhere = flip lessThanOrEqEverywhere
infix 4 greaterThanOrEqEverywhere as >=!

greaterThanEverywhere :: forall a. Ord a => Interval a -> Interval a -> Boolean
greaterThanEverywhere = flip lessThanEverywhere
infix 4 greaterThanEverywhere as >!

notEqEverywhere :: forall a. Ord a => Interval a -> Interval a -> Boolean
notEqEverywhere l r = null $ meet l r
infix 4 notEqEverywhere as /=!

eqEverywhere :: forall a. Ord a => Interval a -> Interval a -> Boolean
eqEverywhere l r = l <=! r && l >=! r
infix 4 eqEverywhere as ==!

null :: forall a. Interval a -> Boolean
null Empty = true
null _ = false

certainly ::
     forall a.
     Ord a
  => (forall b. Ord b => b -> b -> Boolean)
  -> Interval a
  -> Interval a
  -> Boolean
certainly cmp l r =
  -- So we can share `where` clause across multi-way if
  case unit of
    _
      | lt && eq && gt -> true
      | lt && eq -> l <=! r
      | lt && gt -> l /=! r
      | lt -> l <!  r
      | eq && gt -> l >=! r
      | eq -> l ==! r
      | gt -> l >!  r
      | otherwise      -> false
  where
    lt = cmp false true
    eq = cmp true true
    gt = cmp true false

singleton :: forall n. n -> Interval n
singleton bound
  = NonEmpty
  { lower: Bound.Finite { bound, openness: Closed }
  , upper: Bound.Finite { bound, openness: Closed }
  }

data Infinite n = Finite n | Infinity

derive instance genericInfinite :: Generic n => Generic (Infinite n)
derive instance eqInfinite :: Eq n => Eq (Infinite n)
derive instance ordInfinite :: Ord n => Ord (Infinite n)
instance showInfinite :: Generic n => Show (Infinite n) where
  show = gShow

width :: forall n. Ring n => Interval n -> Infinite n
width Empty = Finite zero
width (NonEmpty { lower, upper }) =
  case Tuple lower upper of
    Tuple Bound.NegInf _ -> Infinity
    Tuple _ Bound.PosInf -> Infinity
    Tuple (Bound.Finite l) (Bound.Finite u) -> Finite $ u.bound - l.bound
    Tuple _ _ -> unsafeCrashWith "width"

-- | Where both exist and are finite, upper bound divided by lower bound
normalizedWidth :: forall n. EuclideanRing n => Ring n => Interval n -> Infinite n
normalizedWidth Empty = Finite zero
normalizedWidth (NonEmpty { lower, upper }) =
  case Tuple lower upper of
    Tuple Bound.NegInf _ -> Infinity
    Tuple _ Bound.PosInf -> Infinity
    Tuple (Bound.Finite l) (Bound.Finite u) -> Finite $ u.bound / l.bound
    Tuple _ _ -> unsafeCrashWith "normalizedWidth"
