---
date: 2025-08-04
id: a7dc9417-9847-43b2-a880-c98cc4d2b44c
title: Building Arithmetic from Scratch
---

```{=org}
#+updated: 2025-08-04
```
```{=org}
#+filetags: :writing:
```
In our everyday mathematics, we take for granted that addition is commutative and associative, that multiplication distributes over addition, and so on.
But what if we had to build arithmetic from nothing but the concept of \"next number\"?
In this post, let us construct natural numbers and their operations in Agda, proving each arithmetic property step by step using [structural induction](./2025-07-31-structural-induction-formally.html).

## Natural Numbers

We can inductively define natural numbers in Agda like so:

``` agda
data Nat : Set where
  zero : Nat
  succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}
```

The `BUILTIN NATURAL` pragma tells Agda to treat Haskell integers as natural numbers, allowing us to write `3` instead of `succ (succ (succ zero))`.
More importantly, this makes operations efficient---without this pragma, each natural number `n` would take $O(n)$ memory instead of $O(\log n)$.

Note that this definition captures exactly what natural numbers are: either zero, or the successor of some other natural number.

## Proving vs Testing

Before we dive into the proofs, it\'s worth emphasizing what we mean by \"proving\" here.
Unlike testing, which can only show that a property holds for specific examples, our proofs in Agda establish that properties hold for **all** natural numbers.
When we prove `+-comm`, we\'re not just checking that `2 + 3 ≡ 3 + 2`, but that addition is commutative for every possible pair of natural numbers.

This is made possible by Agda\'s equality type and the proof techniques we established in our [previous post](./2025-07-31-structural-induction-formally.html), where we saw how `refl`, `sym`, `trans`, and `cong` work together to enable equational reasoning.

## Addition

Addition is defined recursively on the first argument:

``` agda
_+_ : Nat → Nat → Nat
0 + m = m
(succ n) + m = succ (n + m)
```

This definition embodies the intuition that adding `m` to the successor of `n` is the same as taking the successor of `n + m`.

### Associativity

One of the most basic properties of addition is associativity:

``` agda
+-assoc : ∀ (n m o : Nat) → n + (m + o) ≡ (n + m) + o
+-assoc zero m o = refl
+-assoc (succ n) m o = cong succ (+-assoc n m o)
```

The proof proceeds by structural induction on `n`:

- Base case `n = 0`: We need to show `0 + (m + o) ≡ (0 + m) + o`, which simplifies to `m + o ≡ m + o` by the definition of addition.
- Inductive case `n = succ n`: We need to show `succ n + (m + o) ≡ (succ n + m) + o`.
  By the definition of addition, this becomes `succ (n + (m + o)) ≡ succ ((n + m) + o)`.
  Using congruence and the inductive hypothesis, this follows immediately.

### Right Identity and Successor Lemmas

To prove commutativity, we first need two helper lemmas that aren\'t immediately obvious from our definition:

``` agda
+-m-z : ∀ (m : Nat) → m ≡ m + 0
+-m-z zero = refl
+-m-z (succ m) = cong succ (+-m-z m)

+-m-s : ∀ (n m : Nat) → succ n + m ≡ n + succ m
+-m-s zero m = refl
+-m-s (succ n) m = cong succ (+-m-s n m)
```

The first lemma shows that `0` is a right identity for addition (not just a left identity as our definition makes obvious).
The second shows that we can \"move\" a successor from the first argument to the second.
Both require induction to prove, highlighting how even simple properties need careful justification when building from first principles.

### Commutativity

With these lemmas in hand, we can prove commutativity:

``` agda
+-comm : ∀ (n m : Nat) → n + m ≡ m + n
+-comm zero m = +-m-z m
+-comm (succ n) m = trans (cong succ (+-comm n m)) (+-m-s m n)
```

The proof again proceeds by induction on `n`:

- Base case `n = 0`: We need `0 + m ≡ m + 0`, which follows from our right identity lemma.
- Inductive case `n = succ n`: We need `succ n + m ≡ m + succ n`.
  This becomes `succ (n + m) ≡ m + succ n`.
  By the inductive hypothesis, `n + m ≡ m + n`, so `succ (n + m) ≡ succ (m + n)`.
  Finally, our successor lemma gives us `succ (m + n) ≡ m + succ n`.

## Multiplication

As expected, multiplication is defined in terms of addition:

``` agda
_*_ : Nat → Nat → Nat
0 * m = 0
(succ n) * m = m + (n * m)
```

This captures the idea that multiplying by the successor of `n` means adding `m` to the result of multiplying by `n`.

### Distributivity

Multiplication distributes over addition:

``` agda
*-+-dist : ∀ (n m o : Nat) → (n * o) + (m * o) ≡ (n + m) * o
*-+-dist zero m o = refl
*-+-dist (succ n) m o = trans (sym (+-assoc o (n * o) (m * o))) (cong (λ c → o + c) (*-+-dist n m o))
```

The proof is by induction on `n`:

- Base case `n = 0`: We need `(0 * o) + (m * o) ≡ (0 + m) * o`, which simplifies to `0 + (m * o) ≡ m * o`.
- Inductive case: We need `(succ n * o) + (m * o) ≡ (succ n + m) * o`.
  This becomes `(o + (n * o)) + (m * o) ≡ o + ((n + m) * o)`.
  Using associativity of addition and the inductive hypothesis, this follows.

### Associativity

Finally, multiplication is associative:

``` agda
*-assoc : ∀ (n m o : Nat) → n * (m * o) ≡ (n * m) * o
*-assoc zero m o = refl
*-assoc (succ n) m o = trans (cong (λ c → (m * o) + c) (*-assoc n m o)) (*-+-dist m (n * m) o)
```

The proof combines our previous results:

- Base case `n = 0`: Trivial by definition.
- Inductive case: We need `succ n * (m * o) ≡ (succ n * m) * o`.
  This becomes `(m * o) + (n * (m * o)) ≡ (m + (n * m)) * o`.
  Using the inductive hypothesis and distributivity, this follows.

## Exercises

1.  Prove that `0` is a right identity for multiplication: `∀ (m : Nat) → m * 0 ≡ 0`.
2.  Prove that multiplication is commutative: `∀ (n m : Nat) → n * m ≡ m * n`.
    (Hint: You\'ll need helper lemmas similar to those we used for addition.)
3.  Define exponentiation and prove that `(n ^ m) ^ o ≡ n ^ (m * o)`.

## Conclusions

The beauty of this approach is that every property we \"obviously know\" about arithmetic must be carefully justified.
In building mathematics from the ground up, we see exactly which assumptions we need and how they combine to give us the rich structure of arithmetic.
