# α-normalization

```
module Dhall.Alpha where

open import Dhall.Syntax.Parsed
open import Dhall.Substitution
open import Dhall.Shift
import Relation.Binary.PropositionalEquality as Prop
open import Relation.Binary.HeterogeneousEquality
open import Data.Maybe using (nothing; just)
```

α-normalization is a function of the following form:

```
alpha : ∀{i} → (t₀ : Expr {i}) → Expr {i}
```

... where:

* `t₀` (the input) is the expression to α-normalize
* `t₁` (the output) is the α-normalized expression

α-normalization renames all bound variables within an expression to use De
Bruijn indices.  For example, the following expression:

    λ(a : Type) → λ(b : Type) → λ(x : a) → λ(y : b) → x

... α-normalizes to:

    λ(_ : Type) → λ(_ : Type) → λ(_ : _@1) → λ(_ : _@1) → _@1

In other words, all bound variables are renamed to `_` and they used the
variable index to disambiguate which variable they are referring to.  This is
equivalent to De Bruijn indices:

    alpha(λ(a : Type) → λ(b : Type) → a) ≡ λ(_ : Type) → λ(_ : Type) → _@1

    alpha(λ(x : Type) → _) ≡ λ(_ : Type) → _@1

If two expressions are α-equivalent then they will be identical after
α-normalization.  For example:

    alpha(λ(a : Type) → a) ≡ λ(_ : Type) → _

    alpha(λ(b : Type) → b) ≡ λ(_ : Type) → _

Note that free variables are not transformed by α-normalization.  For
example:

    alpha(λ(x : Type) → y) ≡ λ(_ : Type) → y

## Bound variables

The only interesting part of α-normalization is expressions with bound
variables.  Each of the following normalization rules renames the bound variable
to `_`, substituting and shifting as necessary in order to avoid variable
capture:


```
alpha (Lambda "_" A₀ b₀) =
  let A₁ = alpha A₀
      b₁ = alpha b₀
  in Lambda "_" A₁ b₁

alpha (Lambda x A₀ b₀) =
  let A₁ = alpha A₀
      b₁ = shift ↑ "_" 0 b₀
      b₂ = var-substition-preserves-size b₁ (b₁ [ x at 0 ≔ "_" at 0 ]) refl
      b₃ = shift ↓ x 0 b₂
      b₄ = alpha b₃
  in Lambda "_" A₁ b₄

alpha (Pi "_" A₀ B₀) =
  let A₁ = alpha A₀
      B₁ = alpha B₀
  in Pi "_" A₁ B₁

alpha (Pi x A₀ B₀) =
  let A₁ = alpha A₀
      B₁ = shift ↑ "_" 0 B₀
      B₂ = var-substition-preserves-size B₁ (B₁ [ x at 0 ≔ "_" at 0 ]) refl
      B₃ = shift ↓ x 0 B₂
      B₄ = alpha B₃
  in Pi "_" A₁ B₄

alpha (Let "_" (just A₀) a₀ b₀) =
  let a₁ = alpha a₀
      A₁ = alpha A₀
      b₁ = alpha b₀
  in Let "_" (just A₁) a₁ b₁

alpha (Let x (just A₀) a₀ b₀) =
  let a₁ = alpha a₀
      A₁ = alpha A₀
      b₁ = shift ↑ "_" 0 b₀
      b₂ = var-substition-preserves-size b₁ (b₁ [ x at 0 ≔ "_" at 0 ]) refl
      b₃ = shift ↓ "_" 0 b₂
      b₄ = alpha b₃
  in Let "_" (just A₁) a₁ b₄

alpha (Let "_" nothing a₀ b₀) =
  let a₁ = alpha a₀
      b₁ = alpha b₀
  in Let "_" nothing a₁ b₁

alpha (Let x nothing a₀ b₀) =
  let a₁ = alpha a₀
      b₁ = shift ↑ "_" 0 b₀
      b₂ = var-substition-preserves-size b₁ (b₁ [ x at 0 ≔ "_" at 0 ]) refl
      b₃ = shift ↓ "_" 0 b₂
      b₄ = alpha b₃
  in Let "_" nothing a₁ b₄
```

## Variables

Variables are already in α-normal form:

```
alpha (x at n) = x at n
```

If they are free variables then there is nothing to do because α-normalization
does not affect free variables.  If they were originally bound variables there
is still nothing to do because would have been renamed to `_` along the way by
one of the preceding rules.

## Imports

An expression with unresolved imports cannot be α-normalized.
