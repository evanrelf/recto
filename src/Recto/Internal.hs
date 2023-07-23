{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Recto.Internal where

import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import GHC.OverloadedLabels (IsLabel (..))
import GHC.Records (HasField (..))
import GHC.TypeLits (Symbol, KnownSymbol)

-- | Record field. Construct using @-XOverloadedLabels@.
--
-- >>> :{
-- example :: Field "foo"
-- example = #foo
-- :}
data Field :: Symbol -> Type where
  Field :: KnownSymbol n => Proxy n -> Field n

deriving stock instance Show (Field n)

instance (x ~ n, KnownSymbol n) => IsLabel x (Field n) where
  fromLabel = Field (Proxy @n)

data n ::: a = Field n := a
  deriving stock (Show)

infix 6 :::, :=

-- | Anonymous record.
data Record :: [Type] -> Type where
  Nil :: Record '[]
  (:>) :: x -> Record xs -> Record (x : xs)

infixr 5 :>

deriving stock instance Show (Record '[])

deriving stock instance (Show x, Show (Record xs)) => Show (Record (x : xs))

-- | Whether a record has a field.
class RecordHasField n r a | n r -> a where
  recordHasField :: Field n -> Record r -> (a -> Record r, a)

instance {-# OVERLAPPING #-} KnownSymbol n
  => RecordHasField n (n ::: a : r) a where
  recordHasField n r@(_ :> xs) =
    case recordHasField n r of (_, a) -> (\a' -> n := a' :> xs, a)

instance RecordHasField n r a => RecordHasField n (any : r) a where
  recordHasField n (x :> xs) =
    case recordHasField n xs of (s, a) -> (\a' -> x :> s a', a)

instance (RecordHasField n r a, KnownSymbol n) => HasField n (Record r) a where
  getField r = case recordHasField (Field (Proxy @n)) r of (_, a) -> a

-- | Empty record.
--
-- >>> :{
-- example :: Record '[]
-- example = empty
-- :}
empty :: Record '[]
empty = Nil

-- | Insert field into record.
--
-- >>> :{
-- example :: Record '["greeting" ::: String, "answer" ::: Int]
-- example =
--     insert #greeting "Hello, world!"
--   $ insert #answer 42
--   $ empty
-- :}
insert :: Field n -> a -> Record r -> Record (n ::: a : r)
insert n a r = n := a :> r

-- | Get field from record.
--
-- >>> :{
-- example :: Record '["answer" ::: Int] -> Int
-- example = get #answer
-- :}
get :: RecordHasField n r a => Field n -> Record r -> a
get n r = case recordHasField n r of (_, a) -> a

-- | Set field in record.
--
-- >>> :{
-- example
--   :: Record '["enabled" ::: Bool]
--   -> Record '["enabled" ::: Bool]
-- example = set #enabled True
-- :}
set :: RecordHasField n r a => Field n -> a -> Record r -> Record r
set n a r = case recordHasField n r of (s, _) -> s a

-- | Modify field in record.
--
-- >>> :{
-- example
--   :: Record '["enabled" ::: Bool]
--   -> Record '["enabled" ::: Bool]
-- example = modify #enabled not
-- :}
modify :: RecordHasField n r a => Field n -> (a -> a) -> Record r -> Record r
modify n f r = case recordHasField n r of (s, a) -> s (f a)
