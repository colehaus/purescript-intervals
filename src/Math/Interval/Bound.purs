module Math.Interval.Bound where

import Prelude hiding (eq)

import Data.Generic (class Generic, gShow)
import Data.Lattice
  ( class BoundedJoinSemilattice
  , class BoundedMeetSemilattice
  , class JoinSemilattice
  , class MeetSemilattice
  )
import Prelude as Prelude

import Math.Interval.Openness (Openness)

-- TODO: GADT this so that we can encode our requirement that interval lower bounds not be `PosInf` and upper bounds not be `NegInf`
data Bound n = NegInf | Finite { bound :: n, openness :: Openness } | PosInf

derive instance genericBound :: Generic n => Generic (Bound n)
derive instance eqBound :: Eq n => Eq (Bound n)
instance showBound :: Generic n => Show (Bound n) where
  show = gShow

instance ordBound :: Ord n => Ord (Bound n) where
  compare l r | l == r = EQ
  compare NegInf _ = LT
  compare _ NegInf = GT
  compare PosInf _ = GT
  compare _ PosInf = LT
  compare (Finite l) (Finite r) = compare l.bound r.bound

instance boundedBound :: Ord n => Bounded (Bound n) where
  top = PosInf
  bottom = NegInf

instance joinBound :: Ord n => JoinSemilattice (Bound n) where
  join (Finite l) (Finite r) =
    Finite case compare l.bound r.bound of
      GT -> l
      LT -> r
      EQ -> { bound: l.bound, openness: l.openness || r.openness }
  join l r = max l r

instance boundedJoinBound :: Ord n => BoundedJoinSemilattice (Bound n) where
  bottom = Prelude.bottom

instance meetBound :: Ord n => MeetSemilattice (Bound n) where
  meet (Finite l) (Finite r) =
    Finite case compare l.bound r.bound of
      GT -> r
      LT -> l
      EQ -> { bound: l.bound, openness: l.openness || r.openness }
  meet l r = min l r

instance boundedMeetBound :: Ord n => BoundedMeetSemilattice (Bound n) where
  top = Prelude.top

lessThan :: forall n. Ord n => n -> Bound n -> Boolean
lessThan _ NegInf = false
lessThan _ PosInf = true
lessThan n (Finite r) = n < r.bound

lessThanOrEq :: forall n. Ord n => n -> Bound n -> Boolean
lessThanOrEq _ NegInf = false
lessThanOrEq _ PosInf = true
lessThanOrEq n (Finite r) = n <= r.bound

greaterThan :: forall n. Ord n => n -> Bound n -> Boolean
greaterThan n b = not $ lessThanOrEq n b

greaterThanOrEq :: forall n. Ord n => n -> Bound n -> Boolean
greaterThanOrEq n b = not $ lessThan n b

eq :: forall n. Eq n => n -> Bound n -> Boolean
eq _ NegInf = false
eq _ PosInf = false
eq n (Finite r) = n == r.bound

notEq :: forall n. Eq n => n -> Bound n -> Boolean
notEq = not <<< eq
