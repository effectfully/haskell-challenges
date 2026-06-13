# Lazy `foldrM`

This is a challenge to solve with Haskell. Check out the [readme](../README.md) of the whole project.

Your task is to define a monadic version of `foldr` in [src/Lib.hs](./src/Lib.hs):

```haskell
foldrM :: (Foldable t, Monad m) => (a -> b -> m b) -> b -> t a -> m b
```

such that

```haskell
foldrM f z [a ... x, y]
```

evaluates as

```haskell
do
    zY <- f y z
    zX <- f x zY
    ...
    zA <- f a zB
    return zA
```

`foldrM` must

1. short-circuit if `>>=` does for the given `m`
2. not force the elements of the list unless `f` and/or `>>=` do that
3. have O(n*m) time and space complexity for O(m) `f` and `>>=`

For example, given `u = undefined`, all of these need to evaluate to `True`:

```haskell
foldrM (\_ _ -> Nothing) 3 []      == Just 3
foldrM (\_ _ -> Nothing) u (u : u) == Nothing
foldrM (\_ z -> Left  z) 3 (u : u) == Left  3
foldrM (\i _ -> Left  i) u [u, 2]  == Left  2
foldrM (\_ z -> Right z) 3 [u, u]  == Right 3
foldrM (\i _ -> Right i) u [1, u]  == Right 1
```

There's a small test suite. I run it with `stack test`. On my machine it takes less than a second and less than 64 MB of RAM to run the test suite, on yours it's going to be different, but if any of the tests takes longer than 10 seconds or more than 256 MB to run, it'll fail.
