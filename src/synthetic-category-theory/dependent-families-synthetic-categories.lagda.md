# Dependent families of (spheres in the language of) synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.dependent-families-synthetic-categories
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import elementary-number-theory.natural-numbers

open import globular-types.reflexive-globular-types
open import globular-types.globular-spheres-reflexive-globular-types

open import synthetic-category-theory.synthetic-categories
```

</details>

## Idea

A dependent family of spheres in a cosmos K, with basepoint a functor : x → y is
a dependent function P which returns for every funcotr g : x → y and every
natural transformation α : f ⇒ g the following data:
  1) two synthetic categories s₀(P(g,α)) and t₀(P(g,α))
  2) two functors s₁(P(g,α)), t₁(P(g,α)) : s₀(P(g,α)) → t₀(P(g,α))
  3) some higher data, i.e. a globular sphere in the globular type of natural
    transformations s₁(P(g,α)) → t₁(P(g,α)).
An equivalent way to describe such a P(g,α) is, then, as a globular sphere in K
of dimension ≥2.

A point of a dependent family P at g and α is a category in the globular type
of cells with boundary P(g,α).  Given a dependent family P, we define the base
for induction on P to be a point of P at input f, id_f. A section of a dependent 
family P is a dependent function of type (g : x → y) → (α : f ≅ g) → (P(g,α))₀,
i.e. a dependent family of synthetic categories. 


-- ```agda
module _ where

  Dependent-Family-Synthetic-Category-Theory :
    {l : Level} {n : ℕ} {m : ℕ}
    {G : Reflexive-Globular-Type l l}
    (S : sphere-Reflexive-Globular-Type G n) →
    (f : higher-cell-sphere-Reflexive-Globular-Type S) →
    UU (lsuc l)
  Dependent-Family-Synthetic-Category-Theory {m = m} {G = G} S f = 
    (g : higher-cell-sphere-Reflexive-Globular-Type S) →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    sphere-Reflexive-Globular-Type G (succ-ℕ (succ-ℕ m))

  point-Dependent-Family-Synthetic-Category-Theory :
    {l : Level} {n : ℕ} {m : ℕ}
    {G : Reflexive-Globular-Type l l}
    {S : sphere-Reflexive-Globular-Type G n}
    {f : higher-cell-sphere-Reflexive-Globular-Type S}
    (P : Dependent-Family-Synthetic-Category-Theory {m = m} S f) →
    (g : higher-cell-sphere-Reflexive-Globular-Type S) →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    UU l
  point-Dependent-Family-Synthetic-Category-Theory P g α =
    higher-cell-sphere-Reflexive-Globular-Type (P g α)

  base-Dependent-Family-Synthetic-Category-Theory :
    {l : Level} {n : ℕ} {m : ℕ}
    {G : Reflexive-Globular-Type l l}
    {S : sphere-Reflexive-Globular-Type G n}
    {f : higher-cell-sphere-Reflexive-Globular-Type S}
    (P : Dependent-Family-Synthetic-Category-Theory {m = m} S f) →
    UU l
  base-Dependent-Family-Synthetic-Category-Theory {S = S} {f = f} P =
    point-Dependent-Family-Synthetic-Category-Theory {S = S} {f = f}
      P f (refl-sphere-suspension-Reflexive-Globular-Type S f)
      
  section-Dependent-Family-Synthetic-Category-Theory :
    {l : Level} {n : ℕ} {m : ℕ}
    {G : Reflexive-Globular-Type l l}
    {S : sphere-Reflexive-Globular-Type G n}
    {f : higher-cell-sphere-Reflexive-Globular-Type S}
    (P : Dependent-Family-Synthetic-Category-Theory {m = m} S f) →
    UU l
  section-Dependent-Family-Synthetic-Category-Theory {S = S} {f = f} P = 
    (g : higher-cell-sphere-Reflexive-Globular-Type S) →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    point-Dependent-Family-Synthetic-Category-Theory {S = S} {f = f} P g α
```  