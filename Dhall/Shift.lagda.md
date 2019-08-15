# Shift

<!--
```
module Dhall.Shift where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; _≤?_; _+_; suc)
open import Data.String using (String; _≟_)
open import Dhall.Syntax.Parsed
```
-->

Dhall uses a shift function internally to avoid variable capture in the
implementation of De Bruijn indices.  This function increases or decreases the
indices of free variables within an expression.

This shift function has the form:

```
data Direction : Set where
  ↑ ↓ : Direction

shift : (d : Direction) → (x : String) → (m : ℕ) → (e₀ : Expr) → Expr
```
... where:

* `d` the direction to shift, either ↑ or ↓.
* `x` (an input variable name) is the name of the free variable(s) to shift
    * variables with a different name are unaffected by the shift function
* `m` (an input natural number) is the minimum index to shift
    * `m` always starts out at `0`
    * `m` increases by one when descending past a bound variable named `x`
    * variables with an index lower than `m` are unaffected by the shift
      function
* `e₀` (an input expression) is the expression to shift

The result of `shift` is a new expression `e₁` - the shifted expression.

## Variables

The first rule is that the shift function will increase the index of any
variable if the variable name matches and the variable's index is greater than
or equal to the minimum index to shift.  For example:

    shift(↑, x, 0, x) = x@1   ; `x = x@0` and increasing the index by 1 gives `x@1`

    shift(↑, x, 1, x) = x     ; No shift, because the index was below the cutoff

    shift(↑, x, 0, y) = y     ; No shift, because the variable name did not match

    shift(↓, x, 0, x@1) = x   ; Example of negative shift

Formally, shift the variable if the name matches and the index is at least as
large as the lower bound:

```
shift _ x _ (v at _) with x ≟ v
shift d x m (.x at n)     | yes refl with m ≤? n
shift ↑ x _ (.x at n)     | yes refl | yes _ = x at (n + 1)
shift ↓ x _ (.x at 0)     | yes refl | yes _ = x at ℕ.zero
shift ↓ x _ (.x at suc n) | yes refl | yes _ = x at n
```

Don't shift the index if the index falls short of the lower bound:

```
shift _ x _ (.x at n) | yes refl | no n>m = x at n
```

Also, don't shift the index if the variable name does not match:

```
shift _ x _ (y at n) | no x≠y = y at n
```

## Bound variables

The shift function is designed to shift only free variables when `m = 0`.  For
example, the following shift usage has no effect because `m = 0` and the
expression is "closed" (i.e. no free variables):

    shift(↑, x, 0, λ(x : Type) → x) = λ(x : Type) → x

    shift(↑, x, 0, ∀(x : Type) → x) = ∀(x : Type) → x

    shift(↑, x, 0, let x = 1 in x) = let x = 1 in x

... whereas the following shift usage has an effect on expressions with free
variables:

    shift(↑, x, 0, λ(y : Type) → x) = λ(y : Type) → x@1

    shift(↑, x, 0, ∀(y : Type) → x) = ∀(y : Type) → x@1

    shift(↑, x, 0, let y = 1 in x) = let y = 1 in x@1

Increment the minimum bound when descending into a λ-expression that binds a
variable of the same name in order to avoid shifting the bound variable:

```
shift _ x _ (Lambda y _ _) with x ≟ y
shift d x m (Lambda .x A₀ b₀) | yes refl =
  let A₁ = shift d x m A₀
      b₁ = shift d x (m + 1) b₀
  in Lambda x A₁ b₁
```

Note that the bound variable, `x`, is not in scope for its own type, `A₀`, so
do not increase the lower bound, `m`, when shifting the bound variable's type.

Descend as normal if the bound variable name does not match:

```
shift d x m (Lambda y A₀ b₀) | no x≠y =
  let A₁ = shift d x m A₀
      b₁ = shift d x m b₀
  in Lambda y A₁ b₁
```

Function types also introduce bound variables, so increase the minimum bound
when descending past such a bound variable:

```
shift d x m (Pi y e e₁) with x ≟ y
shift d x m (Pi .x A₀ B₀) | yes refl =
  let A₁ = shift d x m A₀
      B₁ = shift d x (m + 1) B₀
  in Pi x A₁ B₁
```

Again, the bound variable, `x`, is not in scope for its own type, `A₀`, so do
not increase the lower bound, `m`, when shifting the bound variable's type.

Descend as normal if the bound variable name does not match:


```
shift d x m (Pi y A₀ B₀) | no x≠y =
  let A₁ = shift d x m A₀
      B₁ = shift d x m B₀
  in Pi x A₁ B₁
```
