module Math.Interval.Openness where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)


data Openness = Closed | Open

derive instance genericOpenness :: Generic Openness _
derive instance eqOpenness :: Eq Openness
instance showOpenness :: Show Openness where
  show = genericShow

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
