# recto

Toy anonymous records. See [verso] for anonymous variants.

## Example

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}

import Recto

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

fullName
  :: ["firstName" ::: String, "lastName" ::: String] :| r
  => Record r
  -> String
fullName r = r.firstName <> " " <> r.lastName

greet :: Person -> IO ()
greet person = putStrLn $ "Hello, " <> fullName person <> "!"
```

[verso]: https://github.com/evanrelf/verso
