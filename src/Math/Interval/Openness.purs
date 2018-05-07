module Math.Interval.Openness where

import Prelude

import Data.Generic (class Generic, gShow)

data Openness = Closed | Open

derive instance genericOpenness :: Generic Openness
derive instance eqOpenness :: Eq Openness
instance showOpenness :: Show Openness where
  show = gShow

-- It's maybe questionable that `Open` corresponds to `false` rather than vice versa
instance opennessHeyting :: HeytingAlgebra Openness where
  ff = Open
  tt = Closed
  implies a b = not a || b
  conj Closed Closed = Closed
  conj _ _ = Open
  disj Open Open = Open
  disj _ _ = Closed
  not Open = Closed
  not Closed = Open
