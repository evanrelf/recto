# recto

Toy anonymous records. See [verso] for anonymous variants.

## Example

```haskell
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
```

[verso]: https://github.com/evanrelf/verso
