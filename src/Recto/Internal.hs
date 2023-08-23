{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds #-}
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
import GHC.OverloadedLabels (IsLabel (..))
import GHC.Records (HasField (..))
import GHC.TypeLits (KnownSymbol, Symbol)

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

data n ::: a = FieldName n := a
  deriving stock (Show)

infix 6 :::, :=

-- | Anonymous record.
data Record :: [Type] -> Type where
  RNil :: Record '[]
  RCons :: x -> Record xs -> Record (x : xs)

infixr 5 `RCons`

deriving stock instance Show (Record '[])

deriving stock instance (Show x, Show (Record xs)) => Show (Record (x : xs))

-- | Whether a record has a field.
class RecordHasField n a r | n r -> a where
  recordHasField :: FieldName n -> Record r -> (a -> Record r, a)

instance {-# OVERLAPPING #-} KnownSymbol n
  => RecordHasField n a (n ::: a : r) where
  recordHasField n r@(_ `RCons` xs) =
    case recordHasField n r of (_, a) -> (\a' -> n := a' `RCons` xs, a)

instance RecordHasField n a r => RecordHasField n a (x : r) where
  recordHasField n (x `RCons` xs) =
    case recordHasField n xs of (s, a) -> (\a' -> x `RCons` s a', a)

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
  RecordHasFields [n ::: a] r = RecordHasField n a r
  RecordHasFields (n ::: a : fs) r = (RecordHasField n a r, RecordHasFields fs r)

type fs :| r = RecordHasFields fs r

infixl 1 :|

class RecordFromTuple t r | t -> r, r -> t where
  tupleToRecord :: t -> Record r
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
empty = RNil

-- | Insert field into record.
--
-- >>> :{
-- example :: Record '["greeting" ::: String, "answer" ::: Int]
-- example =
--     insert #greeting "Hello, world!"
--   $ insert #answer 42
--   $ empty
-- :}
insert :: FieldName n -> a -> Record r -> Record (n ::: a : r)
insert n a r = n := a `RCons` r

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
