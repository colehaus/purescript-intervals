module Math.Interval.Internal where

import Prelude hiding (bottom,join,top)

import Data.Either (Either(..))
import Data.Generic (class Generic, gShow)
import Data.Lattice (class BoundedJoinSemilattice, class BoundedLattice, class BoundedMeetSemilattice, class JoinSemilattice, class Lattice, class MeetSemilattice, bottom, join, meet, top)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Math.Interval.Bound (Lower, Upper, finite, injectLower, injectUpper)
import Math.Interval.Openness (Openness(..))

data Empty = MkEmpty

derive instance genericEmpty :: Generic Empty
derive instance eqEmpty :: Eq Empty
derive instance ordEmpty :: Ord Empty
instance showEmpty :: Show Empty where show = gShow

newtype NonEmpty n = MkNonEmpty
  { lower :: Lower n
  , upper :: Upper n
  }

derive instance genericNonEmpty :: Generic n => Generic (NonEmpty n)
derive instance newtypeNonEmpty :: Newtype (NonEmpty n) _
derive instance eqNonEmpty :: Eq n => Eq (NonEmpty n)
derive instance ordNonEmpty :: Ord n => Ord (NonEmpty n)
instance showNonEmpty :: Generic n => Show (NonEmpty n) where show = gShow

newtype Interval n = MkInterval (Either Empty (NonEmpty n))

derive instance genericInterval :: Generic n => Generic (Interval n)
derive instance newtypeInterval :: Newtype (Interval n) _
derive instance eqInterval :: Eq n => Eq (Interval n)
-- | WARNING: Not a semantic instance. Just so we can put it inside a map.
derive instance ordInterval :: Ord n => Ord (Interval n)
instance showInterval :: Generic n => Show (Interval n) where show = gShow

instance joinEmpty :: JoinSemilattice Empty where
  join _ _ = MkEmpty
instance joinNonEmpty :: Ord n => JoinSemilattice (NonEmpty n) where
  join (MkNonEmpty l) (MkNonEmpty r) =
    MkNonEmpty { lower: (meet l.lower r.lower), upper: (join l.upper r.upper) }

instance joinInterval :: Ord n => JoinSemilattice (Interval n) where
  join (MkInterval (Left _)) r = r
  join l (MkInterval (Left _)) = l
  join (MkInterval (Right l)) (MkInterval (Right r)) =
   MkInterval <<< Right $ join l r

instance boundedJoinEmpty :: BoundedJoinSemilattice Empty where
  bottom = MkEmpty
instance boundedJoinInterval :: Ord n => BoundedJoinSemilattice (Interval n) where
  bottom = MkInterval $ Left MkEmpty

instance meetEmpty :: MeetSemilattice Empty where
  meet _ _ = MkEmpty
instance meetInterval :: Ord n => MeetSemilattice (Interval n) where
  meet (MkInterval (Left _)) _ = MkInterval $ Left MkEmpty
  meet _ (MkInterval (Left _)) = MkInterval $ Left MkEmpty
  meet (MkInterval (Right (MkNonEmpty l))) (MkInterval (Right (MkNonEmpty r))) =
   -- So we can share the `where` clause
   case unit of
     _
       | injectLower lower < injectUpper upper -> MkInterval <<< Right $ MkNonEmpty {lower, upper}
       | injectUpper upper < injectLower lower -> MkInterval <<< Left $ MkEmpty
       | isOpen (map (_.openness <<< unwrap) <<< finite <<< injectLower $ lower) &&
           isOpen (map (_.openness <<< unwrap) <<< finite <<< injectUpper $ upper) ->
         MkInterval <<< Left $ MkEmpty
       | otherwise -> MkInterval <<< Right $ MkNonEmpty {lower, upper}
    where
      isOpen (Just Open) = true
      isOpen _ = false
      lower =
        join l.lower r.lower
      upper =
        meet l.upper r.upper

instance boundedMeetEmpty :: BoundedMeetSemilattice Empty where
  top = MkEmpty
instance boundedMeetInterval :: Ord n => BoundedMeetSemilattice (Interval n) where
  top = MkInterval <<< Right $ MkNonEmpty { lower: bottom, upper: top }

instance latticeEmpty :: Lattice Empty
instance latticeInterval :: Ord n => Lattice (Interval n)

instance boundedLatticeEmpty :: BoundedLattice Empty
instance boundedLatticeInterval :: Ord n => BoundedLattice (Interval n)
