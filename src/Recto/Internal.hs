{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Recto.Internal where

import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import GHC.OverloadedLabels (IsLabel (..))
import GHC.Records (HasField (..))
import GHC.TypeLits (Symbol, KnownSymbol)

-- | Anonymous product type.
data Product :: (k -> Type) -> [k] -> Type where
  Nil :: Product f '[]
  Cons :: f x -> Product f xs -> Product f (x : xs)

deriving stock instance Show (Product f '[])

deriving stock instance (Show (f x), Show (Product f xs))
  => Show (Product f (x : xs))

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

data (:::) n a = (:=) (Field n) a
  deriving stock (Show)

-- | Anonymous record.
newtype Record r = MkRecord (Product Identity r)

deriving stock instance Show (Product Identity r) => Show (Record r)

-- | Whether a record has a field.
class RowHasField n r a | n r -> a where
  rowHasField :: Field n -> Record r -> (a -> Record r, a)

instance {-# OVERLAPPING #-} KnownSymbol n
  => RowHasField n (n ::: a : r) a where
  rowHasField :: Field n -> Record (n ::: a : r) -> (a -> Record (n ::: a : r), a)
  rowHasField _ r@(MkRecord (Cons _ xs)) =
    ( \a -> MkRecord (Cons (Identity ((Field (Proxy @n)) := a)) xs)
    , getField @n r
    )

instance RowHasField n r a
  => RowHasField n (any : r) a where
  rowHasField :: Field n -> Record (any : r) -> (a -> Record (any : r), a)
  rowHasField n (MkRecord (Cons x xs)) =
    case rowHasField n (MkRecord xs) of
      (s, a) -> (\a' -> case s a' of MkRecord p -> MkRecord (Cons x p), a)

instance (RowHasField n r a, KnownSymbol n) => HasField n (Record r) a where
  getField :: Record r -> a
  getField r = case rowHasField (Field (Proxy @n)) r of (_, a) -> a

-- | Empty record.
--
-- >>> :{
-- example :: Record '[]
-- example = empty
-- :}
empty :: Record '[]
empty = MkRecord Nil

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
insert n a (MkRecord p) = MkRecord $ Cons (Identity (n := a)) p

-- | Get field from record.
--
-- >>> :{
-- example :: Record '["answer" ::: Int] -> Int
-- example = get #answer
-- :}
get :: RowHasField n r a => Field n -> Record r -> a
get n r = case rowHasField n r of (_, a) -> a

-- | Set field in record.
--
-- >>> :{
-- example
--   :: Record '["enabled" ::: Bool]
--   -> Record '["enabled" ::: Bool]
-- example = set #enabled True
-- :}
set :: RowHasField n r a => Field n -> a -> Record r -> Record r
set n a r = case rowHasField n r of (s, _) -> s a

-- | Modify field in record.
--
-- >>> :{
-- example
--   :: Record '["enabled" ::: Bool]
--   -> Record '["enabled" ::: Bool]
-- example = modify #enabled not
-- :}
modify :: RowHasField n r a => Field n -> (a -> a) -> Record r -> Record r
modify n f r = case rowHasField n r of (s, a) -> s (f a)
