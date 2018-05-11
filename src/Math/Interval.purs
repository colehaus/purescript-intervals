module Math.Interval
  ( module Math.Interval
  , module ForReExport
  ) where

import Prelude

import Data.Bifunctor (lmap, rmap)
import Data.Either (Either(..))
import Data.Generic (class Generic, gShow)
import Data.Lattice (meet)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Ord (lessThanOrEq)
import Data.Tuple (Tuple(..))
import Math.Interval.Bound (Finite(MkFinite), Lower(MkLower), Upper(MkUpper), injectLower, injectUpper)
import Math.Interval.Bound as Bound
import Math.Interval.Internal (Empty(..), Interval(..), NonEmpty(..))
import Math.Interval.Internal (Interval) as ForReExport
import Math.Interval.Openness (Openness(..))
import Partial.Unsafe (unsafeCrashWith)

make ::
     forall n. Ord n
  => Lower n
  -> Upper n
  -> Maybe (NonEmpty n)
make lower upper
  | injectLower lower <= injectUpper upper = Just (MkNonEmpty {lower, upper})
  | otherwise = Nothing

member :: forall n. Ord n => n -> Interval n -> Boolean
member n (MkInterval (Left _)) = false
member n (MkInterval (Right (MkNonEmpty { lower, upper }))) =
  n `Bound.greaterThanOrEq` injectLower lower && n `Bound.lessThanOrEq` injectUpper upper

boundBelow :: forall n. Ord n => n -> Openness -> NonEmpty n -> Maybe (Interval n)
boundBelow boundNum openness i@(MkNonEmpty { upper })
  | Left boundNum == (lmap (_.bound <<< unwrap) <<< unwrap) upper && openness == Open =
    Just <<< MkInterval <<< Left $ MkEmpty
  | boundNum `member` MkInterval (Right i) =
    Just <<< MkInterval <<< Right $
    MkNonEmpty { lower: MkLower <<< Right $ MkFinite { bound: boundNum, openness }, upper }
  | otherwise = Nothing

boundAbove :: forall n. Ord n => n -> Openness -> NonEmpty n -> Maybe (Interval n)
boundAbove boundNum openness i@(MkNonEmpty { lower })
  | Right boundNum == (rmap (_.bound <<< unwrap) <<< unwrap) lower && openness == Open =
    Just <<< MkInterval <<< Left $ MkEmpty
  | boundNum `member` MkInterval (Right i) =
    Just <<< MkInterval <<< Right $
    MkNonEmpty { lower, upper: MkUpper <<< Left $ MkFinite { bound: boundNum, openness } }
  | otherwise = Nothing

lessThanEverywhere :: forall a. Ord a => NonEmpty a -> NonEmpty a -> Boolean
lessThanEverywhere (MkNonEmpty {upper}) (MkNonEmpty {lower}) =
  case compare (injectUpper upper) (injectLower lower) of
    GT -> false
    LT -> true
    EQ ->
      case Tuple upper lower of
        Tuple (MkUpper (Left (MkFinite u))) (MkLower (Right (MkFinite l))) ->
          u . openness == Open || l . openness == Open
        _ -> unsafeCrashWith "lessThanEverywhere"
infix 4 lessThanEverywhere as <!

lessThanOrEqEverywhere :: forall a. Ord a => NonEmpty a -> NonEmpty a -> Boolean
lessThanOrEqEverywhere (MkNonEmpty { upper }) (MkNonEmpty { lower }) =
  injectUpper upper `lessThanOrEq` injectLower lower
infix 4 lessThanOrEqEverywhere as <=!

greaterThanOrEqEverywhere :: forall a. Ord a => NonEmpty a -> NonEmpty a -> Boolean
greaterThanOrEqEverywhere = flip lessThanOrEqEverywhere
infix 4 greaterThanOrEqEverywhere as >=!

greaterThanEverywhere :: forall a. Ord a => NonEmpty a -> NonEmpty a -> Boolean
greaterThanEverywhere = flip lessThanEverywhere
infix 4 greaterThanEverywhere as >!

notEqEverywhere :: forall a. Ord a => NonEmpty a -> NonEmpty a -> Boolean
notEqEverywhere l r = null $ meet (MkInterval (Right l)) (MkInterval (Right r))
infix 4 notEqEverywhere as /=!

eqEverywhere :: forall a. Ord a => NonEmpty a -> NonEmpty a -> Boolean
eqEverywhere l r = l <=! r && l >=! r
infix 4 eqEverywhere as ==!

null :: forall a. Interval a -> Boolean
null (MkInterval (Left _)) = true
null _ = false

certainly ::
     forall a.
     Ord a
  => (forall b. Ord b => b -> b -> Boolean)
  -> NonEmpty a
  -> NonEmpty a
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

singleton :: forall n. n -> NonEmpty n
singleton bound
  = MkNonEmpty
  { lower: MkLower <<< Right $ MkFinite { bound, openness: Closed }
  , upper: MkUpper <<< Left $ MkFinite { bound, openness: Closed }
  }

data Infinite n = Finite n | Infinity

derive instance genericInfinite :: Generic n => Generic (Infinite n)
derive instance eqInfinite :: Eq n => Eq (Infinite n)
derive instance ordInfinite :: Ord n => Ord (Infinite n)
instance showInfinite :: Generic n => Show (Infinite n) where
  show = gShow

width :: forall n. Ring n => Interval n -> Infinite n
width (MkInterval (Left MkEmpty)) = Finite zero
width (MkInterval (Right (MkNonEmpty {lower, upper}))) =
  case Tuple lower upper of
    Tuple (MkLower (Left _)) _ -> Infinity
    Tuple _ (MkUpper (Right _)) -> Infinity
    Tuple (MkLower (Right (MkFinite l))) (MkUpper (Left (MkFinite u))) ->
      Finite $ u . bound - l . bound

-- | Where both exist and are finite, upper bound divided by lower bound
normalizedWidth :: forall n. EuclideanRing n => Ring n => Interval n -> Infinite n
normalizedWidth (MkInterval (Left MkEmpty)) = Finite zero
normalizedWidth (MkInterval (Right (MkNonEmpty { lower, upper }))) =
  case Tuple lower upper of
    Tuple (MkLower (Left _)) _ -> Infinity
    Tuple _ (MkUpper (Right _)) -> Infinity
    Tuple (MkLower (Right (MkFinite l))) (MkUpper (Left (MkFinite u))) ->
      Finite $ u . bound / l . bound
