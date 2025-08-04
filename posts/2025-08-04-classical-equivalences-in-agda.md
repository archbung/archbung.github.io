---
date: 2025-08-04
id: 9643e135-25aa-4c8d-83e6-e4943bdfb8f6
title: Classical Equivalences in Agda
---

```{=org}
#+updated: 2025-08-04
```
```{=org}
#+filetags: :writing:
```
In the [previous post](./2025-07-31-structural-induction-formally.html), we briefly saw that in [Agda](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html) we can encode propositions as types and prove those propositions by showing that they are inhabited.
Today we will see that there are logical principles that we often take for granted but turn out to be unprovable in Agda, which suggest that indeed there are fundamental differences between classical logic that we are familiar with, and the so-called constructive logic in Agda.

## More Propositions as Types

### Falsity

The empty type `⊥` represents logical falsity, as it has no constructors and thus cannot be inhabited.

``` agda
data ⊥ : Set where

absurd : {A : Set} → ⊥ → A
absurd ()
```

The `absurd` function expresses the principle of explosion: from a contradiction, anything follows.
Note that we can pattern match on the empty pattern `()` since there are no constructors for `⊥`.

### Sum Types

Disjunction (logical or) is represented by sum types:

``` agda
data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B
```

To prove `A ∨ B`, we must either provide a proof of `A` (via `left`) or a proof of `B` (via `right`).

### Negation

Negation is defined in terms of implication to falsity:

``` agda
¬_ : Set → Set
¬ A = A → ⊥
```

That is, `¬ A` means \"assuming `A` leads to a contradiction.\"

## Classical Logic

Simply put, we are in classical logic if we assume the Law of Excluded Middle (LEM):

``` agda
lem : ∀ (p : Set) → Either p (p → ⊥)
```

stating that either a proposition `p` is true or its negation is true.
However, it is impossible to prove it in Agda since we would either need to construct an element of an arbitrary proposition `p` or show that `p` leads to a contradiction---but we know nothing about `p`!

It turns out that there are other principles in classical logic that are equivalent to LEM.

### Double Negation Elimination (DNE)

In classical logic, double negation elimination states that `¬¬p` implies `p`:

``` agda
dne : ∀ (p : Set) → ((p → ⊥) → ⊥) → p
```

Note that the other direction, double negation introduction, is provable in Agda:

``` agda
dni : ∀ (p : Set) → p → (p → ⊥) → ⊥
dni x f = f x
```

This simply says that if we have `p` and also `¬p`, we get a contradiction.

It turns out that DNE is equivalent to LEM:

``` agda
dne-lem : (∀ (p : Set) → ((p → ⊥) → ⊥) → p) → (∀ (p : Set) → Either p (p → ⊥))
dne-lem f p = f (Either p (p → ⊥)) (λ g → g (right (λ x → g (left x))))

lem-dne : (∀ (p : Set) → Either p (p → ⊥)) → (∀ (p : Set) → ((p → ⊥) → ⊥) → p)
lem-dne f p h with f p
... | left x = x
... | right x = absurd (h x)
```

- To show that DNE implies LEM, we instantiate DNE with `p := Either p (p → ⊥)` (i.e., LEM itself) and construct the required double negation.
  The key insight is that if we assume `¬(p ∨ ¬p)`, then we can derive both `p` and `¬p`, leading to a contradiction.
- To show that LEM implies DNE, we simply instantiate LEM with the given proposition `p` and pattern match on the result.
  If we get `p` directly, we\'re done. If we get `¬p` but also know `¬¬p`, we have a contradiction.

### Peirce\'s Law

Peirce\'s law is another classical principle:

``` agda
peirce : ∀ (p q : Set) → ((p → q) → p) → p
```

It states that if assuming `p → q` gives us `p`, then `p` must be true.

``` agda
peirce-lem : (∀ (p q : Set) → ((p → q) → p) → p) → (∀ (p : Set) → Either p (p → ⊥))
peirce-lem h p = h (Either p (p → ⊥)) ⊥ (λ f → right (λ x → f (left x)))

lem-peirce : (∀ (p : Set) → Either p (p → ⊥)) → (∀ (p q : Set) → ((p → q) → p) → p)
lem-peirce h p q f with h p
... | left x = x
... | right x = f (λ y → absurd (x y))
```

- To show that Peirce\'s Law implies LEM, we again instantiate with LEM and construct the required function.
  If we assume `(p ∨ ¬p) → ⊥`, we can derive `¬p` and thus `p ∨ ¬p`, giving us a contradiction.
- To show that LEM implies Peirce\'s Law, we instantiate LEM with the given proposition `p` and pattern match.
  If we get `p` directly, we\'re done. If we get `¬p`, we can use the assumption `(p → q) → p` by providing a function that derives `p` from `¬p` (via contradiction).

## Conclusion

What we\'ve seen is that several logical principles that seem \"obviously true\" in classical logic are actually all equivalent to each other---and none of them are provable in Agda\'s constructive logic.
This highlights a fundamental philosophical difference: constructive logic requires that we can actually construct witnesses for our proofs, while classical logic allows for reasoning by contradiction and excluded middle.

The beauty of these equivalences is that they show how deeply interconnected these classical principles are.
They all represent the same fundamental leap: from \'we cannot prove ¬p\' to \'therefore p must be true.\'
Constructive logic rejects this leap, insisting that to establish p, we must construct an actual proof of p.
