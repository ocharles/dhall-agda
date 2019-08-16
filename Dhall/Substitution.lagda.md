<!--
```
module Dhall.Substitution where

open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ) using (_+_) renaming (_≟_ to _≟-ℕ_)
open import Data.String using (String) renaming(_≟_ to _≟-String_)
open import Dhall.Syntax.Parsed
open import Dhall.Shift
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
```
-->

# Substitution

β-reduction requires support for substitution, which has the following form:

    e₀[x@n ≔ a] = e₁

... where:

* `e₀` (an input expression) is the expression that you want to transform
* `x@n` (an input variable) is the variable that you want to substitute with
  another expression
* `a` (an input expression) is the expression that you want to substitute `x@n`
  with
* `e₁` (the output expression) is transformed expression where all occurrences
  of `x@n` have been replaced with `a`

```
_[_at_≔_] : (e₀ : Expr) → (x : String) → (n : ℕ) → (a : Expr) → Expr
```

For example:

    x[x ≔ Bool] = Bool

    y[x ≔ Bool] = y

    x[x@1 ≔ Bool] = x

    (List x)[x ≔ Bool] = List Bool

Note that `e[x ≔ a]` is short-hand for `e[x@0 ≔ a]`

## Table of contents

* [Variables](#variables)
* [Bound variables](#bound-variables)
* [Imports](#imports)
* [Other](#other)

## Variables

Like shifting, pay special attention to the cases that bind variables or
reference variables.

The first two rules govern when to substitute a variable with the specified
expression:

```
(x at n) [ y at m ≔ e ] with x ≟-String y
(x at n) [ y at m ≔ e ] | x≡y? with n ≟-ℕ m
((x at n) [ .x at .n ≔ e ]) | yes refl | yes refl = e
((_ at _) [ y at m ≔ _ ]) | yes refl | no _ = y at m
((_ at _) [ y at m ≔ _ ]) | no _ | yes refl = y at m
((_ at _) [ y at m ≔ _ ]) | no _ | no _ = y at m
-- (v₁ at i) [ v at n ≔ x ] = {!!}
```

In other words, substitute the expression if the variable name and index exactly
match, but otherwise do not substitute and leave the variable as-is.

## Bound variables

The substitution function is designed to only substitute free variables and
ignore bound variables.  The following few examples can help build an intuition
for how substitution uses the numeric index of the variable to substitute:

    ; Substitution has no effect on closed expressions without free variables
    (λ(x : Text) → x)[x ≔ True] = λ(x : Text) → x

    ; Substitution can replace free variables
    (λ(y : Text) → x)[x ≔ True] = λ(y : Text) → True

    ; A variable can be still be free if the DeBruijn index is large enough
    (λ(x : Text) → x@1)[x ≔ True] = λ(x : Text) → True

    ; Descending past a matching bound variable increments the index to
    ; substitute
    (λ(x : Text) → x@2)[x@1 ≔ True] = λ(x : Text) → True

Substitution avoids bound variables by increasing the index when a new bound
variable of the same name is in scope, like this:

    …   b₀[x@(1 + n) ≔ e₁] = b₁   …
    ───────────────────────────────
    …


Substitution also avoids variable capture, like this:

    (λ(x : Type) → y)[y ≔ x] = λ(x : Type) → x@1

Substitution prevents variable capture by shifting the expression to substitute
in when *any* new bound variable (not just the variable to substitute) is in
scope, like this:


    …   ↑(1, y, 0, e₀) = e₁   …
    ───────────────────────────
    …


All of the following rules cover expressions that can bind variables:

```
Lambda x A₀ b₀ [ y at n ≔ e ] with x ≟-String y
Lambda x A₀ b₀ [ .x at n ≔ e₀ ] | yes refl =
  let A₁ = A₀ [ x at n ≔ e₀ ]
      e₁ = shift ↑ x 0 e₀
      b₁ = b₀ [ x at (1 + n) ≔ e₁ ]
  in Lambda x A₁ b₁

Lambda x A₀ b₀ [ y at n ≔ e₀ ] | no x≠y =
  let A₁ = A₀ [ x at n ≔ e₀ ]
      e₁ = shift ↑ y 0 e₀
      b₁ = b₀ [ x at n ≔ e₁ ]
  in Lambda x A₁ b₁

Pi x A₀ b₀ [ y at n ≔ e ] with x ≟-String y
Pi x A₀ b₀ [ .x at n ≔ e₀ ] | yes refl =
  let A₁ = A₀ [ x at n ≔ e₀ ]
      e₁ = shift ↑ x 0 e₀
      b₁ = b₀ [ x at (1 + n) ≔ e₁ ]
  in Pi x A₁ b₁

Pi x A₀ b₀ [ y at n ≔ e₀ ] | no x≠y =
  let A₁ = A₀ [ x at n ≔ e₀ ]
      e₁ = shift ↑ y 0 e₀
      b₁ = b₀ [ x at n ≔ e₁ ]
  in Pi x A₁ b₁

Let x (just A₀) a₀ b₀ [ y at n ≔ e₀ ] with x ≟-String y
Let x (just A₀) a₀ b₀ [ .x at n ≔ e₀ ] | yes refl =
  let A₁ = A₀ [ x at n ≔ e₀ ]
      a₁ = a₀ [ x at n ≔ e₀ ]
      e₁ = shift ↑ x 0 e₀
      b₁ = b₀ [ x at (1 + n) ≔ e₁ ]
  in Let x (just A₁) a₁ b₁

Let x (just A₀) a₀ b₀ [ y at n ≔ e₀ ] | no x≠y =
  let A₁ = A₀ [ x at n ≔ e₀ ]
      a₁ = a₀ [ x at n ≔ e₀ ]
      e₁ = shift ↑ y 0 e₀
      b₁ = b₀ [ x at (1 + n) ≔ e₁ ]
  in Let y (just A₁) a₁ b₁

Let x nothing a₀ b₀ [ y at n ≔ e₀ ] with x ≟-String y
Let x nothing a₀ b₀ [ .x at n ≔ e₀ ] | yes refl =
  let a₁ = a₀ [ x at n ≔ e₀ ]
      e₁ = shift ↑ x 0 e₀
      b₁ = b₀ [ x at (1 + n) ≔ e₁ ]
  in Let x nothing a₁ b₁
Let x nothing a₀ b₀ [ y at n ≔ e₀ ] | no x≠y =
  let a₁ = a₀ [ x at n ≔ e₀ ]
      e₁ = shift ↑ y 0 e₀
      b₁ = b₀ [ x at (1 + n) ≔ e₁ ]
  in Let y nothing a₁ b₁
```

## Imports

You can substitute expressions with unresolved imports because the language
enforces that imported values must be closed (i.e. no free variables) and
substitution of a closed expression has no effect:


    ────────────────────────────────
    (path file)[x@n ≔ e] = path file


    ────────────────────────────────────
    (. path file)[x@n ≔ e] = . path file


    ──────────────────────────────────────
    (.. path file)[x@n ≔ e] = .. path file


    ────────────────────────────────────
    (~ path file)[x@n ≔ e] = ~ path file


    ────────────────────────────────────────────────────────────────────
    (https://authority path file)[x@n ≔ e] = https://authority path file


    ────────────────────────
    (env:x)[x@n ≔ e] = env:x

## Other

No other Dhall expressions bind variables, so the substitution function descends
into sub-expressions in those cases, like this:

    (List x)[x ≔ Bool] = List Bool

The remaining rules are:
