module Math.Interval.Bound
  ( module Math.Interval.Bound
  , module ForReExport
  ) where

import Prelude hiding (eq,join)

import Data.Either (Either, either)
import Data.Either.Nested (Either3, at1, at2, at3, either3, in1, in2, in3)
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, un, unwrap, wrap)

import Math.Interval.Bound.Internal (Bound(..), Core(..), Finite(..), Lower(..), NegInf, PosInf, Upper(..))
import Math.Interval.Bound.Internal (Bound, Finite(..), Lower, NegInf(..), PosInf(..), Upper) as ForReExport
import Math.Interval.Openness (Openness)


lower :: forall n. Either NegInf (Finite n) -> Lower n
lower = MkLower <<< MkCore <<< either in1 in2

upper :: forall n. Either (Finite n) PosInf -> Upper n
upper = MkUpper <<< MkCore <<< either in2 in3

bound :: forall n. Either3 NegInf (Finite n) PosInf -> Bound n
bound = MkBound <<< MkCore <<< either3 in1 in2 in3

lessThan :: forall n. Ord n => n -> Bound n -> Boolean
lessThan n = either3 (const false) ((n < _) <<< _.bound) (const true) <<< raw

lessThanOrEq :: forall n. Ord n => n -> Bound n -> Boolean
lessThanOrEq n = either3 (const false) ((n <= _) <<< _.bound) (const true) <<< raw

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
