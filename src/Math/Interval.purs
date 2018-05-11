module Math.Interval
  ( module Math.Interval
  , module ForReExport
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Either.Nested (either3)
import Data.Generic (class Generic, gShow)
import Data.Lattice (meet)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Ord (lessThanOrEq)
import Math.Interval.Bound (finCore, finite, injectLower, injectUpper, raw)
import Math.Interval.Bound as Bound
import Math.Interval.Bound.Internal (Lower(..), Upper(..))
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

empty :: forall n. Interval n
empty = MkInterval <<< Left $ MkEmpty

member :: forall n. Ord n => n -> Interval n -> Boolean
member n (MkInterval (Left _)) = false
member n (MkInterval (Right (MkNonEmpty { lower, upper }))) =
  n `Bound.greaterThanOrEq` injectLower lower && n `Bound.lessThanOrEq` injectUpper upper

boundBelow :: forall n. Ord n => n -> Openness -> NonEmpty n -> Maybe (Interval n)
boundBelow boundNum openness i@(MkNonEmpty {upper})
  | Just boundNum == (map (_.bound <<< unwrap) <<< finite) upper &&
      openness == Open = Just empty
  | boundNum `member` MkInterval (Right i) =
    Just <<< MkInterval <<< Right $
    MkNonEmpty { lower: MkLower <<< finCore $ { bound: boundNum, openness }, upper }
  | otherwise = Nothing

boundAbove :: forall n. Ord n => n -> Openness -> NonEmpty n -> Maybe (Interval n)
boundAbove boundNum openness i@(MkNonEmpty {lower})
  | Just boundNum == (map (_.bound <<< unwrap) <<< finite) lower &&
      openness == Open = Just empty
  | boundNum `member` MkInterval (Right i) =
    Just <<< MkInterval <<< Right $
    MkNonEmpty { lower, upper: MkUpper <<< finCore $ { bound: boundNum, openness } }
  | otherwise = Nothing

lessThanEverywhere :: forall a. Ord a => NonEmpty a -> NonEmpty a -> Boolean
lessThanEverywhere (MkNonEmpty {upper}) (MkNonEmpty {lower}) =
  case compare (injectUpper upper) (injectLower lower) of
    GT -> false
    LT -> true
    EQ ->
      either3
        absurd
        (\u ->
           either3
             (\_ -> unsafeCrashWith "lessThanEverywhere")
             (\l -> u.openness == Open || l.openness == Open)
             absurd <<<
           raw $
           lower)
        (\_ -> unsafeCrashWith "lessThanEverywhere") <<<
      raw $
      upper
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
  { lower: MkLower <<< finCore $ { bound, openness: Closed }
  , upper: MkUpper <<< finCore $ { bound, openness: Closed }
  }

data Infinite n = Finite n | Infinity

derive instance genericInfinite :: Generic n => Generic (Infinite n)
derive instance eqInfinite :: Eq n => Eq (Infinite n)
derive instance ordInfinite :: Ord n => Ord (Infinite n)
instance showInfinite :: Generic n => Show (Infinite n) where
  show = gShow

width :: forall n. Ring n => Interval n -> Infinite n
width (MkInterval (Left _)) = Finite zero
width (MkInterval (Right (MkNonEmpty {lower, upper}))) =
  either3
    (const Infinity)
    (\l ->
       either3
         absurd
         (Finite <<< (_ - l . bound) <<< _ . bound)
         (const Infinity) <<<
       raw $
       upper)
    absurd <<<
  raw $
  lower

-- | Where both exist and are finite, upper bound divided by lower bound
normalizedWidth :: forall n. EuclideanRing n => Ring n => Interval n -> Infinite n
normalizedWidth (MkInterval (Left _)) = Finite zero
normalizedWidth (MkInterval (Right (MkNonEmpty { lower, upper }))) =
  either3
    (const Infinity)
    (\l ->
       either3
         absurd
         (Finite <<< (_ / l.bound) <<< _.bound)
         (const Infinity) <<<
       raw $
       upper)
    absurd <<<
  raw $
  lower
