module Math.Interval.Internal where

import Prelude hiding (bottom, join, top)

import Data.Generic (class Generic, gShow)
import Data.Lattice
  ( class BoundedJoinSemilattice
  , class BoundedLattice
  , class BoundedMeetSemilattice
  , class JoinSemilattice
  , class Lattice
  , class MeetSemilattice
  , bottom, join, meet, top
  )

import Math.Interval.Bound (Bound)

-- TODO: GADTify so we can convey in types that our interval is `NonEmpty`
data Interval n
  = NonEmpty { lower :: Bound n, upper :: Bound n }
  | Empty

derive instance genericInterval :: Generic n => Generic (Interval n)
derive instance eqInterval :: Eq n => Eq (Interval n)
-- | WARNING: Not a semantic instance. Just so we can put it inside a map.
derive instance ordInterval :: Ord n => Ord (Interval n)
instance showInterval :: Generic n => Show (Interval n) where
  show = gShow

instance joinInterval :: Ord n => JoinSemilattice (Interval n) where
  join Empty r = r
  join l Empty = l
  join (NonEmpty l) (NonEmpty r) =
    NonEmpty { lower: (meet l.lower r.lower), upper: (join l.upper r.upper) }

instance boundedJoinInterval :: Ord n => BoundedJoinSemilattice (Interval n) where
  bottom = Empty

instance meetInterval :: Ord n => MeetSemilattice (Interval n) where
  meet Empty _ = Empty
  meet _ Empty = Empty
  meet (NonEmpty l) (NonEmpty r) =
    NonEmpty { lower: (join l.lower r.lower), upper: (meet l.upper r.upper) }

instance boundedMeetInterval :: Ord n => BoundedMeetSemilattice (Interval n) where
  top = NonEmpty { lower: bottom, upper: top }

instance latticeInterval :: Ord n => Lattice (Interval n)

instance boundedLatticeInterval :: Ord n => BoundedLattice (Interval n)
