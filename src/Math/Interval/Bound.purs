module Math.Interval.Bound where

import Prelude hiding (eq,join)

import Data.Either.Nested (Either3, at1, at2, at3, either3, in1, in2, in3)
import Data.Generic (class Generic, gShow)
import Data.Lattice (class BoundedJoinSemilattice, class BoundedLattice, class BoundedMeetSemilattice, class JoinSemilattice, class Lattice, class MeetSemilattice, join, meet)
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, un, unwrap, wrap)
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

instance latticeFinite :: Ord n => Lattice (Finite n) where

data PosInf = MkPosInf

derive instance genericPosInf :: Generic PosInf
derive instance eqPosInf :: Eq PosInf
derive instance ordPosInf :: Ord PosInf
instance showPosInf :: Show PosInf where show = gShow

newtype Core n l r = MkCore (Either3 l (Finite n) r)

derive instance genericCore :: (Generic n, Generic l, Generic r) => Generic (Core n l r)
derive instance newtypeCore :: Newtype (Core n l r) _
derive instance eqCore :: (Eq n, Eq l, Eq r) => Eq (Core n l r)
derive instance ordCore :: (Ord n, Ord l, Ord r) => Ord (Core n l r)
instance showCore :: (Generic n, Generic l, Generic r) => Show (Core n l r) where show = gShow

newtype Lower n = MkLower (Core n NegInf Void)

derive instance genericLower :: (Generic n) => Generic (Lower n)
derive instance newtypeLower :: Newtype (Lower n) _
derive instance eqLower :: (Eq n) => Eq (Lower n)
derive instance ordLower :: (Ord n) => Ord (Lower n)
instance showLower :: (Generic n) => Show (Lower n) where show = gShow

newtype Upper n = MkUpper (Core n Void PosInf)

derive instance genericUpper :: (Generic n) => Generic (Upper n)
derive instance newtypeUpper :: Newtype (Upper n) _
derive instance eqUpper :: (Eq n) => Eq (Upper n)
derive instance ordUpper :: (Ord n) => Ord (Upper n)
instance showUpper :: (Generic n) => Show (Upper n) where show = gShow

newtype Bound n = MkBound (Core n NegInf PosInf)

derive instance genericBound :: (Generic n) => Generic (Bound n)
derive instance newtypeBound :: Newtype (Bound n) _
derive instance eqBound :: (Eq n) => Eq (Bound n)
derive instance ordBound :: (Ord n) => Ord (Bound n)
instance showBound :: (Generic n) => Show (Bound n) where show = gShow

instance boundedBound :: Ord n => Bounded (Bound n) where
  top = MkBound (MkCore (in3 MkPosInf))
  bottom = MkBound (MkCore (in1 MkNegInf))


instance joinCore :: Ord n => JoinSemilattice (Core n l r) where
  join (MkCore l) (MkCore r) =
    MkCore $
    either3
      (const r)
      (\lf -> either3 (const <<< in2 $ lf) (in2 <<< join lf) in3 r)
      in3
      l
derive newtype instance joinLower :: Ord n => JoinSemilattice (Lower n)
derive newtype instance joinUpper :: Ord n => JoinSemilattice (Upper n)
derive newtype instance joinBound :: Ord n => JoinSemilattice (Bound n)

instance boundedJoinCore :: Ord n => BoundedJoinSemilattice (Core n NegInf r) where
  bottom = MkCore <<< in1 $ MkNegInf
derive newtype instance boundedJoinLower :: Ord n => BoundedJoinSemilattice (Lower n)
derive newtype instance boundedJoinBound :: Ord n => BoundedJoinSemilattice (Bound n)

instance meetCore :: Ord n => MeetSemilattice (Core n l r) where
  meet (MkCore l) (MkCore r) =
    MkCore $
    either3
      in1
      (\lf -> either3 in1 (in2 <<< meet lf) (const <<< in2 $ lf) r)
      (const r)
      l
derive newtype instance meetLower :: Ord n => MeetSemilattice (Lower n)
derive newtype instance meetUpper :: Ord n => MeetSemilattice (Upper n)
derive newtype instance meenBound :: Ord n => MeetSemilattice (Bound n)

instance boundedMeetCore :: Ord n => BoundedMeetSemilattice (Core n l PosInf) where
  top = MkCore <<< in3 $ MkPosInf
derive newtype instance boundedMeetUpper :: Ord n => BoundedMeetSemilattice (Upper n)
derive newtype instance boundedMeetBound :: Ord n => BoundedMeetSemilattice (Bound n)

instance latticeCore :: Ord n => Lattice (Core n l r)
derive newtype instance latticeLower :: Ord n => Lattice (Lower n)
derive newtype instance latticeUpper :: Ord n => Lattice (Upper n)
derive newtype instance latticeBound :: Ord n => Lattice (Bound n)

instance boundedLatticeCore :: Ord n => BoundedLattice (Core n NegInf PosInf)
derive newtype instance boundedLatticeBound :: Ord n => BoundedLattice (Bound n)

lessThan :: forall n. Ord n => n -> Bound n -> Boolean
lessThan n = either3 (const false) ((n < _) <<< _.bound <<< unwrap) (const true) <<< unwrap <<< unwrap

lessThanOrEq :: forall n. Ord n => n -> Bound n -> Boolean
lessThanOrEq n = either3 (const false) ((n <= _) <<< _.bound <<< unwrap) (const true) <<< unwrap <<< unwrap

greaterThan :: forall n. Ord n => n -> Bound n -> Boolean
greaterThan n b = not $ lessThanOrEq n b

greaterThanOrEq :: forall n. Ord n => n -> Bound n -> Boolean
greaterThanOrEq n b = not $ lessThan n b

eq :: forall n. Eq n => n -> Bound n -> Boolean
eq n = maybe false ((n == _) <<< _.bound <<< unwrap) <<< finite

notEq :: forall n. Eq n => n -> Bound n -> Boolean
notEq = not <<< eq

negInf :: forall n. Bound n -> Boolean
negInf = at1 false (const true) <<< unwrap <<< unwrap

posInf :: forall n. Bound n -> Boolean
posInf = at3 false (const true) <<< unwrap <<< unwrap

finite :: forall n l r t. Newtype t (Core n l r) => t -> Maybe (Finite n)
finite = at2 Nothing Just <<< un MkCore <<< unwrap

injectUpper :: forall n. Upper n -> Bound n
injectUpper = wrap <<< MkCore <<< either3 absurd in2 in3 <<< un MkCore <<< unwrap

projectUpper :: forall n. Bound n -> Maybe (Upper n)
projectUpper =
  either3
    (const Nothing)
    (Just <<< wrap <<< MkCore <<< in2)
    (Just <<< wrap <<< MkCore <<< in3) <<<
  un MkCore <<< unwrap

injectLower :: forall n. Lower n -> Bound n
injectLower = wrap <<< MkCore <<< either3 in1 in2 absurd <<< un MkCore <<< unwrap

projectLower :: forall n. Bound n -> Maybe (Lower n)
projectLower =
  either3
    (Just <<< wrap <<< MkCore <<< in1)
    (Just <<< wrap <<< MkCore <<< in2)
    (const Nothing) <<<
  un MkCore <<< unwrap

raw ::
     forall l n r t.
     Newtype (t n) (Core n l r)
  => t n
  -> Either3 l { bound :: n, openness :: Openness } r
raw = either3 in1 (in2 <<< unwrap) in3 <<< un MkCore <<< unwrap

finCore :: forall n l r. { bound :: n , openness :: Openness} -> Core n l r
finCore = MkCore <<< in2 <<< MkFinite
