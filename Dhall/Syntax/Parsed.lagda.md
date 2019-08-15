# Parser Syntax

```
module Dhall.Syntax.Parsed where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_)
```

This module contains the definition of Dhall's syntax, as a result of the
parsing stage. Note that parsing results in well scoped syntax, though
expressions may not be closed (that is, expressions may contain free variables).
This syntax retains all original names, though variables are uniformly referred
to with @ notation (so `x` is viewed as `x@0`).

## Proving Scope

The `_at_∈_` judgement captures the notion that a variable reference occurs in
a list of variable bindings.::

```
data _at_∈_ : String → ℕ → List String → Set where
```

`x-at-0` proves that `x@0` (or just `x`) is valid in any list of names
where `x` is the most recent binding.::

```
  zero : ∀ {xs} → (x : String) → x at 0 ∈ (x ∷ xs)
```

`x-at-suc` proves that if know `x@n` is valid in the list of bindings
`xs`, then `x@n+1` is valid in the list of bindings `[ x, xs ]`::

```
  suc : ∀ {x xs n} → x at n ∈ xs → x at (suc n) ∈ (x ∷ xs)
```

Finally, the `skip` proof can be used if you know `x@n` is valid in `xs`,
then you can show `x@n` is also valid in `[y, xs]`:

```
  skip : ∀ {x y n xs} → x at n ∈ xs → x at n ∈ (y ∷ xs)
```

This small lemma shows that if you know `x@n+1` is in `xs`, then we can show
that `x@n` is also in `xs`.

```
foo : ∀{x n xs} → x at (suc n) ∈ xs → x at n ∈ xs
foo (suc p) = skip p
foo (skip p) = skip (foo p)
```

## Expr

```
data Expr : Set where
  _at_ : (v : String) → (i : ℕ) → Expr
  Lambda : (x : String) → (A : Expr) → Expr → Expr
```
