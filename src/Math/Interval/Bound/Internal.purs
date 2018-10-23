module Math.Interval.Bound.Internal where

import Prelude hiding (join)

import Data.Either.Nested (Either3, either3, in1, in2, in3)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lattice (class BoundedJoinSemilattice, class BoundedLattice, class BoundedMeetSemilattice, class JoinSemilattice, class Lattice, class MeetSemilattice, join, meet)
import Data.Newtype (class Newtype)

import Math.Interval.Openness (Openness)


data NegInf = MkNegInf

derive instance genericNegInf :: Generic NegInf _
derive instance eqNegInf :: Eq NegInf
derive instance ordNegInf :: Ord NegInf
instance showNegInf :: Show NegInf where show = genericShow


data PosInf = MkPosInf

derive instance genericPosInf :: Generic PosInf _
derive instance eqPosInf :: Eq PosInf
derive instance ordPosInf :: Ord PosInf
instance showPosInf :: Show PosInf where show = genericShow


newtype Finite n = MkFinite { bound :: n, openness :: Openness }

derive instance genericFinite :: Generic (Finite n) _
derive instance newtypeFinite :: Newtype (Finite n) _
derive instance eqFinite :: Eq n => Eq (Finite n)
instance ordFinite :: Ord n => Ord (Finite n) where
  compare (MkFinite l) (MkFinite r) = compare l.bound r.bound
instance showFinite :: Show n => Show (Finite n) where show = genericShow

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

instance latticeFinite :: Ord n => Lattice (Finite n)


newtype Core n l r = MkCore (Either3 l (Finite n) r)

derive instance genericCore :: Generic (Core n l r) _
derive instance newtypeCore :: Newtype (Core n l r) _
derive instance eqCore :: (Eq n, Eq l, Eq r) => Eq (Core n l r)
derive instance ordCore :: (Ord n, Ord l, Ord r) => Ord (Core n l r)
instance showCore :: (Show n, Show l, Show r) => Show (Core n l r) where show = genericShow

instance joinCore :: Ord n => JoinSemilattice (Core n l r) where
  join (MkCore l) (MkCore r) =
    MkCore $
    either3
      (const r)
      (\lf -> either3 (const <<< in2 $ lf) (in2 <<< join lf) in3 r)
      in3
      l
instance boundedJoinCore :: Ord n => BoundedJoinSemilattice (Core n NegInf r) where
  bottom = MkCore <<< in1 $ MkNegInf

instance meetCore :: Ord n => MeetSemilattice (Core n l r) where
  meet (MkCore l) (MkCore r) =
    MkCore $
    either3
      in1
      (\lf -> either3 in1 (in2 <<< meet lf) (const <<< in2 $ lf) r)
      (const r)
      l
instance boundedMeetCore :: Ord n => BoundedMeetSemilattice (Core n l PosInf) where
  top = MkCore <<< in3 $ MkPosInf

instance latticeCore :: Ord n => Lattice (Core n l r)
instance boundedLatticeCore :: Ord n => BoundedLattice (Core n NegInf PosInf)


newtype Lower n = MkLower (Core n NegInf Void)

derive instance genericLower :: Generic (Lower n) _
derive instance newtypeLower :: Newtype (Lower n) _
derive instance eqLower :: (Eq n) => Eq (Lower n)
derive instance ordLower :: (Ord n) => Ord (Lower n)
instance showLower :: (Show n) => Show (Lower n) where show = genericShow


newtype Upper n = MkUpper (Core n Void PosInf)

derive instance genericUpper :: Generic (Upper n) _
derive instance newtypeUpper :: Newtype (Upper n) _
derive instance eqUpper :: (Eq n) => Eq (Upper n)
derive instance ordUpper :: (Ord n) => Ord (Upper n)
instance showUpper :: (Show n) => Show (Upper n) where show = genericShow


newtype Bound n = MkBound (Core n NegInf PosInf)

derive instance genericBound :: Generic (Bound n) _
derive instance newtypeBound :: Newtype (Bound n) _
derive instance eqBound :: (Eq n) => Eq (Bound n)
derive instance ordBound :: (Ord n) => Ord (Bound n)
instance showBound :: (Show n) => Show (Bound n) where show = genericShow

instance boundedBound :: Ord n => Bounded (Bound n) where
  top = MkBound (MkCore (in3 MkPosInf))
  bottom = MkBound (MkCore (in1 MkNegInf))


derive newtype instance joinLower :: Ord n => JoinSemilattice (Lower n)
derive newtype instance joinUpper :: Ord n => JoinSemilattice (Upper n)
derive newtype instance joinBound :: Ord n => JoinSemilattice (Bound n)

derive newtype instance boundedJoinLower :: Ord n => BoundedJoinSemilattice (Lower n)
derive newtype instance boundedJoinBound :: Ord n => BoundedJoinSemilattice (Bound n)

derive newtype instance meetLower :: Ord n => MeetSemilattice (Lower n)
derive newtype instance meetUpper :: Ord n => MeetSemilattice (Upper n)
derive newtype instance meenBound :: Ord n => MeetSemilattice (Bound n)

derive newtype instance boundedMeetUpper :: Ord n => BoundedMeetSemilattice (Upper n)
derive newtype instance boundedMeetBound :: Ord n => BoundedMeetSemilattice (Bound n)

derive newtype instance latticeLower :: Ord n => Lattice (Lower n)
derive newtype instance latticeUpper :: Ord n => Lattice (Upper n)
derive newtype instance latticeBound :: Ord n => Lattice (Bound n)

derive newtype instance boundedLatticeBound :: Ord n => BoundedLattice (Bound n)
