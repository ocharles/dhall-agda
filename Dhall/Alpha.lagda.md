# α-normalization

```
module Dhall.Alpha where

open import Dhall.Syntax.Parsed
open import Dhall.Substitution
open import Dhall.Shift
```

α-normalization is a function of the following form:

```
alpha : (t₀ : Expr) → Expr
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
      b₂ = b₁ [ x at 0 ≔ ("_" at 0) ]
      b₃ = shift ↓ x 0 b₂
      b₄ = alpha b₃
  in Lambda "_" A₁ b₄

alpha (v at i) = {!!}
alpha (Pi x e e₁) = {!!}
alpha (Let x A₀ e e₁) = {!!}
```
