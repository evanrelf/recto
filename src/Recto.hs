module Recto
  ( Record
  , (:::) (..)
  , Field
  , RecordHasField
  , RecordFromTuple
  , record
  , empty
  , insert
  , get
  , set
  , modify
  )
where

import Recto.Internal
import Recto.Internal.Instances ()
