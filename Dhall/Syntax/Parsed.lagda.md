# Parser Syntax

```
{-# OPTIONS --sized #-}

module Dhall.Syntax.Parsed where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; suc)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Size
```

This module contains the definition of Dhall's syntax, as a result of the
parsing stage. This syntax retains all original names, though variables are
uniformly referred to with @ notation (so `x` is viewed as `x@0`).

## Expr

```
data Expr : {i : Size} → Set where
  _at_ : {s : Size} → (v : String) → (i : ℕ) → Expr {s}
  Lambda : ∀{s} → (x : String) → (A : Expr {s}) → Expr {s} → Expr {↑ s}
  Pi : ∀{s} → (x : String) → (A₀ : Expr {s}) → Expr {s} → Expr {↑ s}
  Let : ∀{s} → (x : String) → (A₀ : Maybe (Expr {s})) → (a₀ : Expr {s}) → (b₀ : Expr {s}) → Expr {↑ s}
```
