# recto

Simple anonymous records.

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
  ( "firstName" .= "Evan"
  , "lastName" .= "Relf"
  , "likesDogs" .= True
  )

fullName
  :: ["firstName" ::: String, "lastName" ::: String] :| r
  => Record r
  -> String
fullName r = r.firstName <> " " <> r.lastName

greet :: Person -> IO ()
greet person = putStrLn $ "Hello, " <> fullName person <> "!"
```

I think this library is quite simple compared to more industrial strength
options like [large-anon](https://hackage.haskell.org/package/large-anon). But
you can get even simpler; you could have invented anonymous records on your own!

[Here](https://gist.github.com/evanrelf/45a7cba9f09f9ebef5c7429a3c2d779f) is
what I would consider a minimum viable implementation. And then with a few
syntax tricks, you can make something like [this](https://gist.github.com/evanrelf/d6f55a6db6230f4f30b157ad1fb1b61c).
