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
  Cons :: x -> Record xs -> Record (x : xs)

infixr 5 `Cons`

deriving stock instance Show (Record '[])

deriving stock instance (Show x, Show (Record xs)) => Show (Record (x : xs))

-- | Whether a record has a field.
class RecordHasField n r a | n r -> a where
  recordHasField :: Field n -> Record r -> (a -> Record r, a)

instance {-# OVERLAPPING #-} KnownSymbol n
  => RecordHasField n (n ::: a : r) a where
  recordHasField n r@(_ `Cons` xs) =
    case recordHasField n r of (_, a) -> (\a' -> n := a' `Cons` xs, a)

instance RecordHasField n r a => RecordHasField n (any : r) a where
  recordHasField n (x `Cons` xs) =
    case recordHasField n xs of (s, a) -> (\a' -> x `Cons` s a', a)

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
insert n a r = n := a `Cons` r

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
  recordFromTuple () = empty

instance RecordFromTuple (n1 ::: a1) '[n1 ::: a1] where
  recordFromTuple (n1 := a1) = insert n1 a1 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2) '[n1 ::: a1, n2 ::: a2] where
  recordFromTuple (n1 := a1, n2 := a2) = insert n1 a1 $ insert n2 a2 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3) '[n1 ::: a1, n2 ::: a2, n3 ::: a3] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22, n23 := a23) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 $ insert n23 a23 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22, n23 := a23, n24 := a24) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 $ insert n23 a23 $ insert n24 a24 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22, n23 := a23, n24 := a24, n25 := a25) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 $ insert n23 a23 $ insert n24 a24 $ insert n25 a25 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22, n23 := a23, n24 := a24, n25 := a25, n26 := a26) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 $ insert n23 a23 $ insert n24 a24 $ insert n25 a25 $ insert n26 a26 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22, n23 := a23, n24 := a24, n25 := a25, n26 := a26, n27 := a27) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 $ insert n23 a23 $ insert n24 a24 $ insert n25 a25 $ insert n26 a26 $ insert n27 a27 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22, n23 := a23, n24 := a24, n25 := a25, n26 := a26, n27 := a27, n28 := a28) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 $ insert n23 a23 $ insert n24 a24 $ insert n25 a25 $ insert n26 a26 $ insert n27 a27 $ insert n28 a28 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22, n23 := a23, n24 := a24, n25 := a25, n26 := a26, n27 := a27, n28 := a28, n29 := a29) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 $ insert n23 a23 $ insert n24 a24 $ insert n25 a25 $ insert n26 a26 $ insert n27 a27 $ insert n28 a28 $ insert n29 a29 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22, n23 := a23, n24 := a24, n25 := a25, n26 := a26, n27 := a27, n28 := a28, n29 := a29, n30 := a30) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 $ insert n23 a23 $ insert n24 a24 $ insert n25 a25 $ insert n26 a26 $ insert n27 a27 $ insert n28 a28 $ insert n29 a29 $ insert n30 a30 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30, n31 ::: a31) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30, n31 ::: a31] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22, n23 := a23, n24 := a24, n25 := a25, n26 := a26, n27 := a27, n28 := a28, n29 := a29, n30 := a30, n31 := a31) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 $ insert n23 a23 $ insert n24 a24 $ insert n25 a25 $ insert n26 a26 $ insert n27 a27 $ insert n28 a28 $ insert n29 a29 $ insert n30 a30 $ insert n31 a31 empty

instance RecordFromTuple (n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30, n31 ::: a31, n32 ::: a32) '[n1 ::: a1, n2 ::: a2, n3 ::: a3, n4 ::: a4, n5 ::: a5, n6 ::: a6, n7 ::: a7, n8 ::: a8, n9 ::: a9, n10 ::: a10, n11 ::: a11, n12 ::: a12, n13 ::: a13, n14 ::: a14, n15 ::: a15, n16 ::: a16, n17 ::: a17, n18 ::: a18, n19 ::: a19, n20 ::: a20, n21 ::: a21, n22 ::: a22, n23 ::: a23, n24 ::: a24, n25 ::: a25, n26 ::: a26, n27 ::: a27, n28 ::: a28, n29 ::: a29, n30 ::: a30, n31 ::: a31, n32 ::: a32] where
  recordFromTuple (n1 := a1, n2 := a2, n3 := a3, n4 := a4, n5 := a5, n6 := a6, n7 := a7, n8 := a8, n9 := a9, n10 := a10, n11 := a11, n12 := a12, n13 := a13, n14 := a14, n15 := a15, n16 := a16, n17 := a17, n18 := a18, n19 := a19, n20 := a20, n21 := a21, n22 := a22, n23 := a23, n24 := a24, n25 := a25, n26 := a26, n27 := a27, n28 := a28, n29 := a29, n30 := a30, n31 := a31, n32 := a32) = insert n1 a1 $ insert n2 a2 $ insert n3 a3 $ insert n4 a4 $ insert n5 a5 $ insert n6 a6 $ insert n7 a7 $ insert n8 a8 $ insert n9 a9 $ insert n10 a10 $ insert n11 a11 $ insert n12 a12 $ insert n13 a13 $ insert n14 a14 $ insert n15 a15 $ insert n16 a16 $ insert n17 a17 $ insert n18 a18 $ insert n19 a19 $ insert n20 a20 $ insert n21 a21 $ insert n22 a22 $ insert n23 a23 $ insert n24 a24 $ insert n25 a25 $ insert n26 a26 $ insert n27 a27 $ insert n28 a28 $ insert n29 a29 $ insert n30 a30 $ insert n31 a31 $ insert n32 a32 empty
