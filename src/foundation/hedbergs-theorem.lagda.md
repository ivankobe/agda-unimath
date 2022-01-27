---
title: Univalent Mathematics in Agda
---

# Hedberg's Theorem

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.hedbergs-theorem where

open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-equality using
  ( has-decidable-equality; has-decidable-equality-equiv';
    has-decidable-equality-is-prop)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-iff; is-decidable-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-type using (empty; is-prop-empty; ex-falso)
open import foundation.equality-dependent-pair-types using
  ( eq-pair-Σ'; pair-eq-Σ)
open import foundation.fibers-of-maps using
  ( equiv-fib-pr1; equiv-total-fib)
open import foundation.identity-types using (Id; refl; ap; tr)
open import foundation.injective-maps using (is-prop-map-is-injective)
open import foundation.propositions using
  ( is-prop; is-proof-irrelevant-is-prop)
open import foundation.sections using (map-section; is-injective-map-section)
open import foundation.sets using (is-set; is-set-prop-in-id)
open import foundation.type-arithmetic-dependent-pair-types using
  ( left-unit-law-Σ-is-contr)
open import foundation.unit-type using (unit; is-prop-unit; star)
open import foundation.universe-levels using (Level; UU; lzero)
```

## Hedberg's theorem

```agda
module _
  {l : Level} {A : UU l}
  where

  Eq-has-decidable-equality' :
    (x y : A) → is-decidable (Id x y) → UU lzero
  Eq-has-decidable-equality' x y (inl p) = unit
  Eq-has-decidable-equality' x y (inr f) = empty

  Eq-has-decidable-equality :
    (d : has-decidable-equality A) → A → A → UU lzero
  Eq-has-decidable-equality d x y = Eq-has-decidable-equality' x y (d x y)

  abstract
    is-prop-Eq-has-decidable-equality' :
      (x y : A) (t : is-decidable (Id x y)) →
      is-prop (Eq-has-decidable-equality' x y t)
    is-prop-Eq-has-decidable-equality' x y (inl p) = is-prop-unit
    is-prop-Eq-has-decidable-equality' x y (inr f) = is-prop-empty

  abstract
    is-prop-Eq-has-decidable-equality :
      (d : has-decidable-equality A)
      {x y : A} → is-prop (Eq-has-decidable-equality d x y)
    is-prop-Eq-has-decidable-equality d {x} {y} =
      is-prop-Eq-has-decidable-equality' x y (d x y)

  abstract
    refl-Eq-has-decidable-equality :
      (d : has-decidable-equality A) (x : A) →
      Eq-has-decidable-equality d x x 
    refl-Eq-has-decidable-equality d x with d x x
    ... | inl α = star
    ... | inr f = f refl

  abstract
    Eq-has-decidable-equality-eq :
      (d : has-decidable-equality A) {x y : A} →
      Id x y → Eq-has-decidable-equality d x y
    Eq-has-decidable-equality-eq d {x} {.x} refl =
      refl-Eq-has-decidable-equality d x

  abstract
    eq-Eq-has-decidable-equality' :
      (x y : A) (t : is-decidable (Id x y)) →
      Eq-has-decidable-equality' x y t → Id x y
    eq-Eq-has-decidable-equality' x y (inl p) t = p
    eq-Eq-has-decidable-equality' x y (inr f) t = ex-falso t

  abstract
    eq-Eq-has-decidable-equality :
      (d : has-decidable-equality A) {x y : A} →
      Eq-has-decidable-equality d x y → Id x y
    eq-Eq-has-decidable-equality d {x} {y} =
      eq-Eq-has-decidable-equality' x y (d x y)

  abstract
    is-set-has-decidable-equality : has-decidable-equality A → is-set A
    is-set-has-decidable-equality d =
      is-set-prop-in-id
        ( λ x y → Eq-has-decidable-equality d x y)
        ( λ x y → is-prop-Eq-has-decidable-equality d)
        ( λ x → refl-Eq-has-decidable-equality d x)
        ( λ x y → eq-Eq-has-decidable-equality d)
```

```agda
abstract
  has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    has-decidable-equality A → ((x : A) → has-decidable-equality (B x)) →
    has-decidable-equality (Σ A B)
  has-decidable-equality-Σ dA dB (pair x y) (pair x' y') with dA x x'
  ... | inr np = inr (λ r → np (ap pr1 r))
  ... | inl p =
    is-decidable-iff eq-pair-Σ' pair-eq-Σ
      ( is-decidable-equiv
        ( left-unit-law-Σ-is-contr
          ( is-proof-irrelevant-is-prop
            ( is-set-has-decidable-equality dA x x') p)
          ( p))
        ( dB x' (tr _ p y) y'))

abstract
  has-decidable-equality-fiber-has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    has-decidable-equality A → has-decidable-equality (Σ A B) →
    (x : A) → has-decidable-equality (B x)
  has-decidable-equality-fiber-has-decidable-equality-Σ {B = B} dA dΣ x =
    has-decidable-equality-equiv'
      ( equiv-fib-pr1 B x)
      ( has-decidable-equality-Σ dΣ
        ( λ t →
          has-decidable-equality-is-prop
            ( is-set-has-decidable-equality dA (pr1 t) x)))
```

```agda
abstract
  has-decidable-equality-base-has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    has-decidable-equality (Σ A B) → ((x : A) → has-decidable-equality (B x)) →
    has-decidable-equality A
  has-decidable-equality-base-has-decidable-equality-Σ b dΣ dB =
    has-decidable-equality-equiv'
      ( equiv-total-fib (map-section b))
      ( has-decidable-equality-Σ dΣ
        ( λ t →
          has-decidable-equality-is-prop
            ( is-prop-map-is-injective
              ( is-set-has-decidable-equality dΣ)
              ( is-injective-map-section b)
              ( t))))
```