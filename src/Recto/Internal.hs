{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Recto.Internal where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.Exts (Any)
import GHC.OverloadedLabels (IsLabel (..))
import GHC.Records (HasField (..))
import GHC.TypeLits (KnownSymbol, Symbol)
import Prelude hiding (any)
import Unsafe.Coerce (unsafeCoerce)

-- | Record field name. Construct using @-XOverloadedLabels@.
--
-- >>> :{
-- example :: FieldName "foo"
-- example = #foo
-- :}
data FieldName :: Symbol -> Type where
  FieldName :: KnownSymbol n => Proxy n -> FieldName n

deriving stock instance Show (FieldName n)

instance (x ~ n, KnownSymbol n) => IsLabel x (FieldName n) where
  fromLabel = FieldName (Proxy @n)

-- | Record field.
data n ::: a = FieldName n := a
  deriving stock (Show)

infix 6 :::, :=

-- | Anonymous record.
type Record :: [Type] -> Type
type role Record nominal
newtype Record xs = Record (Vector Any)

instance Show (Record '[]) where
  show = undefined

instance (Show x, Show (Record xs)) => Show (Record (x : xs)) where
  show = undefined

-- class FieldIndex n a r | n r -> a where
--   fieldIsHead :: FieldName n -> Record r -> Bool

-- instance {-# OVERLAPPING #-} FieldIndex n a (n ::: a : r) where
--   fieldIsHead _ _ = True

-- instance FieldIndex n a r => FieldIndex n a (x : r) where
--   fieldIsHead _ _ = False

-- instance FieldIndex n a '[] => FieldIndex n a '[] where
--   fieldIsHead _ _ = False

-- fieldIndex :: FieldIndex n a r => FieldName n -> Record r -> Maybe Int
-- fieldIndex = go 0
--   where
--   go :: Int -> FieldName n -> Record r -> Maybe Int
--   go i n r@(Record v)
--     | Vector.null v = Nothing
--     | fieldIsHead n r = Just i
--     | otherwise =
--         let
--           r' :: Record
--         in
--           go (i + 1) n r'

-- | Whether a record has a field.
class RecordHasField n a r | n r -> a where
  recordHasField :: FieldName n -> Record r -> (a -> Record r, a)

instance {-# OVERLAPPING #-} RecordHasField n a (n ::: a : r) where
  recordHasField _ (Record v) =
    (\a' ->
      let
        any = (unsafeCoerce :: a -> Any) a'
        updates = Vector.singleton (0, any)
      in
        Record (Vector.unsafeUpdate v updates)
    , (unsafeCoerce :: Any -> a) (Vector.unsafeHead v)
    )

instance RecordHasField n a r => RecordHasField n a (x : r) where
  recordHasField n (Record v) = undefined

instance (RecordHasField n a r, KnownSymbol n) => HasField n (Record r) a where
  getField r = case recordHasField (FieldName (Proxy @n)) r of (_, a) -> a

-- | Whether a record has one or more fields.
--
-- >>> :{
-- fullName
--   :: RecordHasFields ["firstName" ::: String, "lastName" ::: String] r
--   => Record r
--   -> String
-- fullName r = r.firstName <> " " <> r.lastName
-- >>>
type RecordHasFields :: k -> [Type] -> Constraint
type family RecordHasFields fs r where
  RecordHasFields '[] r = ()
  RecordHasFields (n ::: a) r = RecordHasField n a r
  -- Treat list types like type-level lists with one element.
  RecordHasFields [n ::: a] r = RecordHasField n a r
  RecordHasFields (n ::: a : fs) r = (RecordHasField n a r, RecordHasFields fs r)

-- | Operator version of `RecordHasFields`.
type fs :| r = RecordHasFields fs r

infixl 1 :|

-- | Convert between tuples and records. Enables construction of records using
-- tuple syntax.
class RecordFromTuple t r | t -> r, r -> t where
  -- | Convert a tuple to a record. `record` is recommended over
  -- `tupleToRecord`.
  tupleToRecord :: t -> Record r

  -- | Convert a record to a tuple.
  recordToTuple :: Record r -> t

-- | Construct a record using tuple syntax.
--
-- >>> :{
-- example :: Record '["greeting" ::: String, "answer" ::: Int]
-- example =
--   record
--     ( #greeting := "Hello, world!"
--     , #answer := 42
--     )
-- :}
record :: RecordFromTuple t r => t -> Record r
record = tupleToRecord

-- | Empty record.
--
-- >>> :{
-- example :: Record '[]
-- example = empty
-- :}
empty :: Record '[]
empty = Record Vector.empty

-- | Insert field into record.
--
-- >>> :{
-- example :: Record '["greeting" ::: String, "answer" ::: Int]
-- example =
--     insert #greeting "Hello, world!"
--   $ insert #answer 42
--   $ empty
-- :}
insert :: forall n a r. FieldName n -> a -> Record r -> Record (n ::: a : r)
insert _ a (Record v) = Record (Vector.cons ((unsafeCoerce :: a -> Any) a) v)

-- | Get field from record. Using @-XOverloadedRecordDot@ is recommended over
-- using `get`.
--
-- >>> :{
-- example :: Record '["answer" ::: Int] -> Int
-- example = get #answer
-- :}
get :: n ::: a :| r => FieldName n -> Record r -> a
get n r = case recordHasField n r of (_, a) -> a

-- | Set field in record.
--
-- >>> :{
-- example
--   :: Record '["enabled" ::: Bool]
--   -> Record '["enabled" ::: Bool]
-- example = set #enabled True
-- :}
set :: n ::: a :| r => FieldName n -> a -> Record r -> Record r
set n a r = case recordHasField n r of (s, _) -> s a

-- | Modify field in record.
--
-- >>> :{
-- example
--   :: Record '["enabled" ::: Bool]
--   -> Record '["enabled" ::: Bool]
-- example = modify #enabled not
-- :}
modify :: n ::: a :| r => FieldName n -> (a -> a) -> Record r -> Record r
modify n f r = case recordHasField n r of (s, a) -> s (f a)
