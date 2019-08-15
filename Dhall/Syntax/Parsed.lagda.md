# Parser Syntax

```
module Dhall.Syntax.Parsed where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_)
```

This module contains the definition of Dhall's syntax, as a result of the
parsing stage. This syntax retains all original names, though variables are
uniformly referred to with @ notation (so `x` is viewed as `x@0`).

## Expr

```
data Expr : Set where
  _at_ : (v : String) → (i : ℕ) → Expr
  Lambda : (x : String) → (A : Expr) → Expr → Expr
```
