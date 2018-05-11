module Math.Interval.Bound where

import Prelude hiding (eq,join)

import Data.Either (Either(..), either)
import Data.Either.Nested (Either3, at1, at2, at3, either3, in1, in2, in3)
import Data.Generic (class Generic, gShow)
import Data.Lattice (class BoundedJoinSemilattice, class BoundedMeetSemilattice, class JoinSemilattice, class MeetSemilattice, join, meet)
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, unwrap)
import Prelude as Prelude

import Math.Interval.Openness (Openness)

data NegInf = MkNegInf

derive instance genericNegInf :: Generic NegInf
derive instance eqNegInf :: Eq NegInf
derive instance ordNegInf :: Ord NegInf
instance showNegInf :: Show NegInf where show = gShow

newtype Finite n = MkFinite { bound :: n, openness :: Openness }

derive instance genericFinite :: Generic n => Generic (Finite n)
derive instance newtypeFinite :: Newtype (Finite n) _
derive instance eqFinite :: Eq n => Eq (Finite n)
derive instance ordFinite :: Ord n => Ord (Finite n)
instance showFinite :: Generic n => Show (Finite n) where show = gShow

instance joinFinite :: Ord n => JoinSemilattice (Finite n) where
  join (MkFinite l) (MkFinite r) =
    MkFinite case compare l.bound r.bound of
      GT -> l
      LT -> r
      EQ -> { bound: l.bound, openness: l.openness || r.openness }

instance meetFinite :: Ord n => MeetSemilattice (Finite n) where
  meet (MkFinite l) (MkFinite r) =
     MkFinite case compare l.bound r.bound of
       GT -> r
       LT -> l
       EQ -> { bound: l.bound, openness: l.openness || r.openness }

data PosInf = MkPosInf

derive instance genericPosInf :: Generic PosInf
derive instance eqPosInf :: Eq PosInf
derive instance ordPosInf :: Ord PosInf
instance showPosInf :: Show PosInf where show = gShow

newtype Lower n = MkLower (Either NegInf (Finite n))

derive instance genericLower :: Generic n => Generic (Lower n)
derive instance newtypeLower :: Newtype (Lower n) _
derive instance eqLower :: Eq n => Eq (Lower n)
derive instance ordLower :: Ord n => Ord (Lower n)
instance showLower :: Generic n => Show (Lower n) where show = gShow

instance joinLower :: Ord n => JoinSemilattice (Lower n) where
  join (MkLower l) (MkLower r) =
    MkLower $
    either
      (const r)
      (\lf -> either (const <<< Right $ lf) (Right <<< join lf) r)
      l

instance meetLower :: Ord n => MeetSemilattice (Lower n) where
  meet (MkLower l) (MkLower r) =
    MkLower $ either Left (\lf -> either Left (Right <<< meet lf) r) l

instance boundedJoinLower :: Ord n => BoundedJoinSemilattice (Lower n) where
  bottom = MkLower <<< Left $ MkNegInf

newtype Upper n = MkUpper (Either (Finite n) PosInf)

derive instance genericUpper :: Generic n => Generic (Upper n)
derive instance newtypeUpper :: Newtype (Upper n) _
derive instance eqUpper :: Eq n => Eq (Upper n)
derive instance ordUpper :: Ord n => Ord (Upper n)
instance showUpper :: Generic n => Show (Upper n) where show = gShow

instance joinUpper :: Ord n => JoinSemilattice (Upper n) where
  join (MkUpper l) (MkUpper r) =
    MkUpper $ either (\lf -> either (Left <<< join lf) Right r) Right l

instance meetUpper :: Ord n => MeetSemilattice (Upper n) where
  meet (MkUpper l) (MkUpper r) =
    MkUpper $
    either (\lf -> either (Left <<< meet lf) (const <<< Left $ lf) r) (const r) l

instance boundedMeetUpper :: Ord n => BoundedMeetSemilattice (Upper n) where
  top = MkUpper <<< Right $ MkPosInf

newtype Bound n = MkBound (Either3 NegInf (Finite n) PosInf)

derive instance genericBound :: Generic n => Generic (Bound n)
derive instance newtypeBound :: Newtype (Bound n) _
derive instance eqBound :: Eq n => Eq (Bound n)
derive instance ordBound :: Ord n => Ord (Bound n)
instance showBound :: Generic n => Show (Bound n) where show = gShow

instance boundedBound :: Ord n => Bounded (Bound n) where
  top = MkBound (in3 MkPosInf)
  bottom = MkBound (in1 MkNegInf)

instance joinBound :: Ord n => JoinSemilattice (Bound n) where
  join (MkBound l) (MkBound r) =
    MkBound $
    either3
      (const r)
      (\lf -> either3 (const <<< in2 $ lf) (in2 <<< join lf) in3 r)
      in3
      l

instance boundedJoinBound :: Ord n => BoundedJoinSemilattice (Bound n) where
  bottom = Prelude.bottom

instance meetBound :: Ord n => MeetSemilattice (Bound n) where
  meet (MkBound l) (MkBound r) =
    MkBound $
    either3
      in1
      (\lf -> either3 in1 (in2 <<< meet lf) (const <<< in2 $ lf) r)
      (const r)
      l

instance boundedMeetBound :: Ord n => BoundedMeetSemilattice (Bound n) where
  top = Prelude.top

lessThan :: forall n. Ord n => n -> Bound n -> Boolean
lessThan n = either3 (const false) ((n < _) <<< _.bound <<< unwrap) (const true) <<< unwrap

lessThanOrEq :: forall n. Ord n => n -> Bound n -> Boolean
lessThanOrEq n = either3 (const false) ((n <= _) <<< _.bound <<< unwrap) (const true) <<< unwrap

greaterThan :: forall n. Ord n => n -> Bound n -> Boolean
greaterThan n b = not $ lessThanOrEq n b

greaterThanOrEq :: forall n. Ord n => n -> Bound n -> Boolean
greaterThanOrEq n b = not $ lessThan n b

eq :: forall n. Eq n => n -> Bound n -> Boolean
eq n = maybe false ((n == _) <<< _.bound <<< unwrap) <<< finite

notEq :: forall n. Eq n => n -> Bound n -> Boolean
notEq = not <<< eq

negInf :: forall n. Bound n -> Boolean
negInf = at1 false (const true) <<< unwrap

posInf :: forall n. Bound n -> Boolean
posInf = at3 false (const true) <<< unwrap

finite :: forall n. Bound n -> Maybe (Finite n)
finite = at2 Nothing Just <<< unwrap

injectUpper :: forall n. Upper n -> Bound n
injectUpper = MkBound <<< either in2 in3 <<< unwrap

projectUpper :: forall n. Bound n -> Maybe (Upper n)
projectUpper =
  either3
    (const Nothing)
    (Just <<< MkUpper <<< Left)
    (Just <<< MkUpper <<< Right) <<<
  unwrap

injectLower :: forall n. Lower n -> Bound n
injectLower = MkBound <<< either in1 in2 <<< unwrap

projectLower :: forall n. Bound n -> Maybe (Lower n)
projectLower =
  either3
    (Just <<< MkLower <<< Left)
    (Just <<< MkLower <<< Right)
    (const Nothing) <<<
  unwrap
