# Globes in reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.globes where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.coproduct-types
open import foundation.images
open import foundation.codiagonal-maps-of-types

open import elementary-number-theory.natural-numbers

open import globular-types.globular-types
open import globular-types.globular-spheres-reflexive-globular-types
open import globular-types.reflexive-globular-types
open import globular-types.reflexive-globular-equivalences
```

</details>

## Idea

## Definitions

```agda
data
  globe-Reflexive-Globular-Type
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) : ℕ → UU (l1 ⊔ l2)
  where

  0-globe :
      0-cell-Reflexive-Globular-Type G → globe-Reflexive-Globular-Type G 0

  extend-globe : 
    {n : ℕ} → (x y : 0-cell-Reflexive-Globular-Type G) →
    globe-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y) n  →
    globe-Reflexive-Globular-Type G (succ-ℕ n)

```

```agda
module _
    {l : Level}
  where

  reflexive-globular-type-top-cell-globe-Reflexive-Globular-Type :
    {n : ℕ} → {G : Reflexive-Globular-Type l l} →
    globe-Reflexive-Globular-Type G n →
    Reflexive-Globular-Type l l
  reflexive-globular-type-top-cell-globe-Reflexive-Globular-Type
    {G = G} (0-globe x) = G
  reflexive-globular-type-top-cell-globe-Reflexive-Globular-Type
    ( extend-globe x y Γ) =
      reflexive-globular-type-top-cell-globe-Reflexive-Globular-Type Γ

  type-top-cell-globe-Reflexive-Globular-Type : 
    {n : ℕ} → {G : Reflexive-Globular-Type l l} →
    (Γ : globe-Reflexive-Globular-Type G n) → UU l
  type-top-cell-globe-Reflexive-Globular-Type Γ =
    0-cell-Reflexive-Globular-Type
      ( reflexive-globular-type-top-cell-globe-Reflexive-Globular-Type Γ)

  top-cell-globe-Reflexive-Globular-Type :
    {n : ℕ} → {G : Reflexive-Globular-Type l l} →
    (Γ : globe-Reflexive-Globular-Type G n) →
    type-top-cell-globe-Reflexive-Globular-Type Γ
  top-cell-globe-Reflexive-Globular-Type (0-globe x) = x
  top-cell-globe-Reflexive-Globular-Type (extend-globe x y Γ) =
    top-cell-globe-Reflexive-Globular-Type Γ
```

### Forgetting the top cell

```agda
module _
    {l : Level}
  where

  underlying-sphere-globe-Reflexive-Globular-Type :
    {G : Reflexive-Globular-Type l l} {n : ℕ} →
    (Γ : globe-Reflexive-Globular-Type G n) →
    sphere-Reflexive-Globular-Type G n
  underlying-sphere-globe-Reflexive-Globular-Type (0-globe x) =
    empty-sphere-Reflexive-Globular-Type
  underlying-sphere-globe-Reflexive-Globular-Type (extend-globe x y Γ) =
    extension-sphere-Reflexive-Globular-Type x y 
      ( underlying-sphere-globe-Reflexive-Globular-Type Γ)

```

### Making a sphere from a globe by adding another top-dimensional cell

```agda
module _
    {l : Level}
  where

  make-sphere-globe-Reflexive-Globular-Type :
    {G : Reflexive-Globular-Type l l} {n : ℕ} →
    (Γ : globe-Reflexive-Globular-Type G n) →
    (α : type-top-cell-globe-Reflexive-Globular-Type Γ) →
    sphere-Reflexive-Globular-Type G (succ-ℕ n)
  make-sphere-globe-Reflexive-Globular-Type (0-globe x) y =
    extension-sphere-Reflexive-Globular-Type x y
      empty-sphere-Reflexive-Globular-Type
  make-sphere-globe-Reflexive-Globular-Type (extend-globe x y Γ) α =
    extension-sphere-Reflexive-Globular-Type x y
      ( make-sphere-globe-Reflexive-Globular-Type Γ α)

  make-globe-sphere-Reflexive-Globular-Type :
    {G : Reflexive-Globular-Type l l} {n : ℕ}
    (S : sphere-Reflexive-Globular-Type G n) →
    (α : higher-cell-sphere-Reflexive-Globular-Type S) →
    globe-Reflexive-Globular-Type G n
  make-globe-sphere-Reflexive-Globular-Type
    empty-sphere-Reflexive-Globular-Type α = 0-globe α
  make-globe-sphere-Reflexive-Globular-Type
    ( extension-sphere-Reflexive-Globular-Type x y S) α =
      extend-globe x y ( make-globe-sphere-Reflexive-Globular-Type S α)
```

```agda
module _
  {l : Level}
  where

  underlying-make-sphere-globe-equiv :
    {G : Reflexive-Globular-Type l l} {n : ℕ}
    (S : sphere-Reflexive-Globular-Type G n) →
    (α : higher-cell-sphere-Reflexive-Globular-Type S) →
    reflexive-globular-equiv
      ( reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type
        ( underlying-sphere-globe-Reflexive-Globular-Type
          ( make-globe-sphere-Reflexive-Globular-Type S α)))
      ( reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type S)
  underlying-make-sphere-globe-equiv
    empty-sphere-Reflexive-Globular-Type α = id-reflexive-globular-equiv _
  underlying-make-sphere-globe-equiv
    ( extension-sphere-Reflexive-Globular-Type x y S) α =
      underlying-make-sphere-globe-equiv S α
```

```agda
module _
  {l : Level}
  where

  semisuspension-globe-Reflexive-Globular-Type :
    {n : ℕ} → (G : Reflexive-Globular-Type l l) →
    (Γ : globe-Reflexive-Globular-Type G n) →
    (α : type-top-cell-globe-Reflexive-Globular-Type Γ) → 
    (1-cell-Reflexive-Globular-Type
      ( reflexive-globular-type-top-cell-globe-Reflexive-Globular-Type Γ)
      ( top-cell-globe-Reflexive-Globular-Type Γ)
      ( α)) →
    globe-Reflexive-Globular-Type G (succ-ℕ n)
  semisuspension-globe-Reflexive-Globular-Type G (0-globe x) y f =
    extend-globe x y (0-globe f)
  semisuspension-globe-Reflexive-Globular-Type G (extend-globe x y Γ) α φ =
    extend-globe x y ( semisuspension-globe-Reflexive-Globular-Type _ Γ α φ)
    
module _
  {l : Level}
  where

  refl-globe-Reflexive-Globular-Type : 
    {n : ℕ} → {G : Reflexive-Globular-Type l l} →
    (Γ : globe-Reflexive-Globular-Type G n) →
    globe-Reflexive-Globular-Type G (succ-ℕ n)
  refl-globe-Reflexive-Globular-Type Γ =
    semisuspension-globe-Reflexive-Globular-Type _ Γ
      ( top-cell-globe-Reflexive-Globular-Type Γ)
      ( refl-1-cell-Reflexive-Globular-Type
        ( reflexive-globular-type-top-cell-globe-Reflexive-Globular-Type Γ))
``` 