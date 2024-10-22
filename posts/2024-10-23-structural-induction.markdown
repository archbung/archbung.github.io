---
title: Structural Induction
---

Equational reasoning is a reasoning approach where one substitutes
equals for equals. In Haskell, this is justified by its referential
transparency.

In this post, let us embark on a journey of structural induction, which is
an important technique in equational reasoning. Structural induction is so-named
because it is an induction based on structures of data types.

Take lists, for example. A list in Haskell is either

- an empty list `[]`, or
- an element `x` prepended into another list `xs`, written as `(x:xs)`.

Using structural induction, one may prove properties about lists by

- showing that the property holds for empty lists, and
- assuming that the property holds for `xs`, show that the property holds for
  `(x:xs)`.

Let us now work through an example.

## `map` from `foldr`

Working with lists in Haskell, one would soon run across the higher-order
functions `map`.

```haskell
map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x : xs) = f x : map f xs
```

Clearly, `map f xs` applies `f` uniformly to each element of `xs`, if any.
What is perhaps less well-known, however, is that folds (both `foldr` and `foldl`)
are strictly more expressive than `map`:

- One cannot define `foldl` or `foldr` via `map` since the latter always returns
  a list, whereas folds can return any type:

  ```haskell
  foldr (+) 0 [1,2,3] -- returns an integer
  foldl (&&) True []  -- returns a boolean
  ```

- On the other hand, one can easily derive `map` using `foldr` and `foldl`, as we
  will show shortly. Furthermore, since `foldr` and `foldl`
  [are functionally equivalent](/posts/2024-10-21-foldr-and-foldl.html), we will
  use `foldr` here.

Recall the definition of `foldr`:

```haskell
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z [] = z
foldr f z (x : xs) = f x (foldr f z xs)
```

Notice that the return type of `foldr` is dictated by the type of its initial
accumulator `z`. Since `map` returns a list, a reasonable choice for the initial
accumulator is the empty list `[]`.

With that in mind, the definition of `map` in terms of `foldr` is straightforward:

```haskell
map f xs = foldr (\x acc -> f x : acc) [] xs
```

Let's verify that the above definition is correct by structural induction on `xs`.

- Base case `xs = []`

  ```haskell
    foldr (\x acc -> f x : acc) [] []
  = []
  = map f []
  ```

- Inductive case `xs = x : xs` with the inductive hypothesis:

  ```haskell
  forall f xs. map f xs = foldr (\x acc -> f x : acc) [] xs
  ```

  ```haskell
    foldr (\x acc -> f x : acc) [] (x : xs)
      -- definition of foldr
  = (\x acc -> f x : acc) x (foldr (\x acc -> f x : acc) [] xs)
      -- lambda application
  = f x : foldr (\x acc -> f x : acc) [] xs
      -- inductive hypothesis
  = f x : map f xs
      -- definition of map
  = map f (x : xs)
  ```

## Exercises

1. Define `filter` in terms of `foldr` and show that your definition is correct
   by structural induction. Recall that the definition of `filter` is

   ```haskell
   filter :: (a -> Bool) -> [a] -> [a]
   filter p [] = []
   filter p (x : xs) =
     if p x then x : filter p xs else filter p xs
   ```

2. Structural induction works on any inductively-defined data structure. For example,
   one may define binary trees as:

   ```haskell
   data Tree a = Leaf | Node a (Tree a) (Tree a)

   ```

   Analoguously to lists, one can define `map` and `foldr` for binary trees as follows:

   ```haskell
   mapTree :: (a -> b) -> Tree a -> Tree b
   mapTree f Leaf = Leaf
   mapTree f (Node x left right) =
     Node (f x) (mapTree f left) (mapTree f right)

   foldrTree :: (a -> b -> b -> b) -> b -> Tree a -> b
   foldrTree f z Leaf = z
   foldrTree f z (Node x left right) =
     f x (foldrTree f z left) (foldrTree f z right)
   ```

   Define `mapTree` in terms of `foldrTree` and show its correctness by structural
   induction.
