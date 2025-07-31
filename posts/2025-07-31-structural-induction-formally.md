---
date: 2025-07-30
id: 9410b8be-2982-4529-be3b-e92f2b5205ae
title: "Structural Induction, Formally: an Introduction to Agda"
---

```{=org}
#+updated: 2025-07-31
```
```{=org}
#+filetags: :writing:
```
In our [previous](./2024-10-23-structural-induction.html) [posts](./2024-10-25-folding-left-and-right.html), we used pen-and-paper equational reasoning to prove properties about Haskell programs.
While this works well, wouldn\'t it be nice if a computer could check our proofs for us, catching any mistakes we might make?

This is where dependently-typed languages like Agda come in.
By encoding our propositions as types and proofs as programs, we can have the compiler verify our reasoning is sound.
In this post, let us define [structural induction](./2024-10-23-structural-induction.html) more formally and then use it to show several results that we have seen previously.

## Proposition as Types

While a more extensive treatment of dependent types is beyond the scope of this post, for now it is enough to know that one may encode propositions (i.e. things to prove) as types, due to a well-known result called the [Curry-Howard isomorphism](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence).
Proving those propositions, in turn, amounts to constructing elements of the types that correspond to said propositions.

## Equality Types

Perhaps the most important proposition to define is equality, that is, expressing whether two values are equal to one another.
Since it is categorical error to ask whether two values of different types are equal or not, equality is necessarily parameterized by the type of the values.

``` agda
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
infix 4 _≡_
```

Some remarks regarding the definition above:

- In Agda, enclosing a definition with `_` turns it into an operator (infix with precedence 4 in this case), which means that one may write something like `1 + 2 ≡ 3`.
- Indeed `≡` is parameterized by type `A`, which is also made implicit (note the curly braces) since `A` can often be deduced from `x`.
- It has only one constructor, `refl`, which one may pattern-match as usual.

Additionally, it is also symmetric, transitive, and congruent.

``` agda
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl
```

The readers are encouraged to pause and take a few moments to think why the above proofs go through.

The key insight is that `refl` is the only way to construct a proof of equality, and it only works when both sides are *definitionally* equal.
When Agda accepts `refl` as a proof of `map f [] ≡ []`, it is because both sides reduce to the same value by the definitions of the functions involved.

Similarly, when we pattern match on a proof of type `x ≡ y`, Agda learns that `x` and `y` must be the same, allowing us to substitute one for the other.

## Structural Induction on List

Recall the definition of lists:

``` agda
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A
infixr 5 _::_
```

As before, to show that a property holds for any list, one must show that it holds for both the `[]` case and the `_::_` case.
Let us work on a couple of examples.

### `map` as `foldr`

``` agda
map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f z [] = z
foldr f z (x :: xs) = f x (foldr f z xs)
```

And here is the result that we have previously:

``` agda
foldr-as-map : {A B : Set} → (f : A → B) → (xs : List A) →
  map f xs ≡ foldr (λ x acc → f x :: acc) [] xs
foldr-as-map f [] = refl
foldr-as-map f (x :: xs) = cong (λ c → f x :: c) (foldr-as-map f xs)
```

Like before, the `[]` case is trivial (both sides are definitionally equal) so one may construct the equality directly with `refl`.
On the other hand, the `x :: xs` case is a bit more involved that needs the congruence property of equality to go through.
Here we also see that induction really is recursion: the inductive hypothesis is exactly the recursive call to `xs`.

### `foldl` as `foldr`

``` agda
foldl : {A B : Set} → (B → A → B) → B → List A → B
foldl f z [] = z
foldl f z (x :: xs) = foldl f (f z x) xs
```

As we have seen [previously](./2024-10-25-folding-left-and-right.html), to show that one can define `foldl` and `foldr` it is necessary to generalize the property.

``` agda
foldl-as-foldr' : {A B : Set} → (g : B → B) → (f : A → B → B) → (z : B) → (xs : List A) →
  g (foldr f z xs) ≡ foldl (λ g x y → g (f x y)) g xs z
foldl-as-foldr' g f z [] = refl
foldl-as-foldr' g f z (x :: xs) = foldl-as-foldr' (λ y → g (f x y)) f z xs

foldl-as-foldr : {A B : Set} → (f : A → B → B) → (z : B) → (xs : List A) →
  foldr f z xs ≡ foldl (λ g x y → g (f x y)) (λ x → x) xs z
foldl-as-foldr f z xs = foldl-as-foldr' (λ x → x) f z xs
```

Note that the proof turns out to be simpler since we are really just updating the `g` on each recursive calls in `foldl-as-foldr'` above.
