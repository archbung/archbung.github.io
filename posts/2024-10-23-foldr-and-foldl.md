---
title: Folding Left and Right
---

Many moons ago, while I was reading the venerable [Real-World Haskell](https://book.realworldhaskell.org/),
I came across a problem of defining right fold in terms of left fold (and vice-versa)
without reversing the input list. This post aims to provide just that.

## Folding Revisited

Folding (also known as reducing) is essentially summarizing a collection
of values into a result. For lists, a fold is a higher-order function that
takes a binary function, an initial accumulator value, and a list. It then
iterate over the list, updating the accumulator with the given binary function
along the way.

Since some binary functions are not associative, the direction of the evaluation
matters. As such, there are two kinds of folds: *right fold*, which evaluates from
the right, and *left fold*, which evaluates from the left.

```haskell
-- left foldl
foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f z [] = z
foldl f z (x : xs) = foldl f (f z x) xs

-- right foldl
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z [] = z
foldr f z (x : xs) = f x (foldr f z xs)
```

Note that

- Both folds iterate the list from the left.
- `foldl` is tail-recursive, which combined with strictness annotations could be
  very efficient.
- Since Haskell is lazy, `foldr` can be productive even if the input list is infinite.
  For example, `foldr const 0 [1..]` would evaluate immediately to `1` since `const` 
  ignores its second argument.

As mentioned previously, the order of the evaluation matters for non-associative
binary functions. For example,

```haskell
foldr (-) 0 [1,2,3] -- 1-(2-(3-0)) = 2
foldl (-) 0 [1,2,3] -- ((0-1)-2)-3 = -6
```

## Folding Left and Right

Since `foldr` evaluates from the right whereas `foldl` evaluates from the left,
to define one using the other (and vice-versa) one needs to deal with this
fundamental difference somehow. The key insight here is to:

- delay evaluation via function calls,
- build up a chain of function compositions by partially applying the
  supplied function in the correct order, and
- apply the resulting function to the initial accumulator.

### `foldl` from `foldr`

Using the insight above, we arrive at the following definition:

```haskell
foldl f z xs = foldr step accum xs z
```

What remains is to correctly define `step` and `accum`. To derive `accum`,
recall that `foldl f z [] = z`. Since `foldr step accum [] z = accum z`,
this means that `accum = id`.

Deriving `step` is more involved. Thankfully `GHCi` is there to tell us
that its type is `step :: a -> (b -> b) -> (b -> b)`. Note that it is
just a higher-order version of the usual function argument to `foldr`,
which is `a -> b -> b`.

We thus arrive at the following definition:

```haskell
step :: a -> (b -> b) -> (b -> b)
step x g y = g (f y x)
  ```

Intuitively, `g` is the current chain of function composition, which
will be composed with a suitable application of `f` with the current
list element `x`.

With the definition of `step` sorted, we now have the complete definition
of `foldl` in terms of `foldr`:

```haskell
foldl f z xs = foldr step id xs z
```

To show that the above definition is correct, we may proceed with
[structural induction](/posts/2024-10-23-structural-induction.html) on `xs`.

- Base case `xs = []`

  ```haskell
    foldr step id [] z
  = id z
  = z
  = foldl f z []
  ```

- Inductive case `xs = x : xs` with the inductive hypothesis

  ```haskell
  forall f z xs. foldl f z xs = foldr step id xs z
  ```

  ```haskell
    foldr step id (x : xs) z
      -- definition of foldr
  = step x (foldr step id xs) z
      -- definition of step
  = foldr step id xs (f z x)
      -- inductive hypothesis with z = f z x
  = foldl f (f z x) xs
      -- definition of foldl
  = foldl f z (x : xs)
  ```

### `foldr` from `foldl`

Similarly, we have

```haskell
foldr f z xs = foldl step accum xs z
```

where `accum = id` as before. In this case, `GHCi` tells us that the type
of `step` is `(b -> b) -> a -> (b -> b)`, which is again just the higher-order
version of the function argument to `foldl`, namely `b -> a -> b`. Also
similarly to before, following the types would allow us to arrive at the
following definition of `step` and consequently, `foldr` in terms of `foldl`.

```haskell
step :: (b -> b) -> a -> (b -> b)
step g x = g . f x

foldr f z xs = foldl step id xs z
```

To show the correctness of the above definition, we may also proceed with
structural induction on `xs`. Note that, in contrast to `foldr`, `foldl`
updates the accumulator at each recursive calls.

```haskell
foldl f z (x : xs) = foldl f (f z x) xs
```

Since we start with the function `id` as our initial accumulator, for the
proof to go through we have to abstract it away. As such, we instead
need to show the stronger statement below:

```haskell
forall f g z xs. g (foldr f z xs) = foldl step g xs z
```

The desired result can then be shown by instantiating `g` with `id`.

- Base case `xs = []`
  
  ```haskell
    foldl step g [] z
  = g z
  = g (foldr f z [])
  ```

- Inductive case `xs = x : xs` with the inductive hypothesis

  ```haskell
  forall f g z xs. g (foldr f z xs) = foldl step g xs z 
  ```

  ```haskell
    foldl step g (x : xs) z
      -- definition of foldl
  = foldl step (step g x) xs z
      -- definition of step
  = foldl step (g . f x) xs z
      -- inductive hypothesis with g = g . f x
  = (g . f x) (foldr f z xs)
      -- definition of function composition
  = g (f x (foldr f z xs))
      -- definition of foldr
  = g (foldr f z (x : xs))
  ```
