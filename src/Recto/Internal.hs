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
  RNil :: Record '[]
  RCons :: x -> Record xs -> Record (x : xs)

infixr 5 `RCons`

deriving stock instance Show (Record '[])

deriving stock instance (Show x, Show (Record xs)) => Show (Record (x : xs))

-- | Whether a record has a field.
class RecordHasField n r a | n r -> a where
  recordHasField :: Field n -> Record r -> (a -> Record r, a)

instance {-# OVERLAPPING #-} KnownSymbol n
  => RecordHasField n (n ::: a : r) a where
  recordHasField n r@(_ `RCons` xs) =
    case recordHasField n r of (_, a) -> (\a' -> n := a' `RCons` xs, a)

instance RecordHasField n r a => RecordHasField n (any : r) a where
  recordHasField n (x `RCons` xs) =
    case recordHasField n xs of (s, a) -> (\a' -> x `RCons` s a', a)

instance (RecordHasField n r a, KnownSymbol n) => HasField n (Record r) a where
  getField r = case recordHasField (Field (Proxy @n)) r of (_, a) -> a

class RecordFromTuple t r | t -> r, r -> t where
  recordFromTuple :: t -> Record r

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
record = recordFromTuple

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
insert :: Field n -> a -> Record r -> Record (n ::: a : r)
insert n a r = n := a `RCons` r

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

instance RecordFromTuple () '[] where
  recordFromTuple () = RNil

instance RecordFromTuple (n ::: a) '[n ::: a] where
  recordFromTuple x = x `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2) '[n1 ::: a1, n2 ::: a2] where
  recordFromTuple (x1, x2) = x1 `RCons` x2 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3) '[n1 ::: a1, n2 ::: a2, n3 ::: a3] where
  recordFromTuple (x1, x2, x3) = x1 `RCons` x2 `RCons` x3 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4] where
  recordFromTuple (x1, x2, x3, x4) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5] where
  recordFromTuple (x1, x2, x3, x4, x5) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6] where
  recordFromTuple (x1, x2, x3, x4, x5, x6) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` x23 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` x23 `RCons` x24 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` x23 `RCons` x24 `RCons` x25 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` x23 `RCons` x24 `RCons` x25 `RCons` x26 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` x23 `RCons` x24 `RCons` x25 `RCons` x26 `RCons` x27 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` x23 `RCons` x24 `RCons` x25 `RCons` x26 `RCons` x27 `RCons` x28 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` x23 `RCons` x24 `RCons` x25 `RCons` x26 `RCons` x27 `RCons` x28 `RCons` x29 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` x23 `RCons` x24 `RCons` x25 `RCons` x26 `RCons` x27 `RCons` x28 `RCons` x29 `RCons` x30 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30, n31 ::: a31) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30, n31 ::: a31] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` x23 `RCons` x24 `RCons` x25 `RCons` x26 `RCons` x27 `RCons` x28 `RCons` x29 `RCons` x30 `RCons` x31 `RCons` RNil

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30, n31 ::: a31, n32 ::: a32) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30, n31 ::: a31, n32 ::: a32] where
  recordFromTuple (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32) = x1 `RCons` x2 `RCons` x3 `RCons` x4 `RCons` x5 `RCons` x6 `RCons` x7 `RCons` x8 `RCons` x9 `RCons` x10 `RCons` x11 `RCons` x12 `RCons` x13 `RCons` x14 `RCons` x15 `RCons` x16 `RCons` x17 `RCons` x18 `RCons` x19 `RCons` x20 `RCons` x21 `RCons` x22 `RCons` x23 `RCons` x24 `RCons` x25 `RCons` x26 `RCons` x27 `RCons` x28 `RCons` x29 `RCons` x30 `RCons` x31 `RCons` x32 `RCons` RNil
