{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Recto

main :: IO ()
main = pure ()

type Person = Record
  [ "firstName" ::: String
  , "lastName" ::: String
  , "likesDogs" ::: Bool
  ]

evan :: Person
evan = record
  ( #firstName := "Evan"
  , #lastName := "Relf"
  , #likesDogs := True
  )

greet :: Person -> IO ()
greet person = putStrLn $ "Hello, " <> person.firstName <> "!"
