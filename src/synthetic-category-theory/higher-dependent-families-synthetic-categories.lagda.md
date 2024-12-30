# Dependent families of (spheres in the language of) synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.higher-dependent-families-synthetic-categories
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import elementary-number-theory.natural-numbers

open import globular-types.reflexive-globular-types
open import globular-types.globes
open import globular-types.globular-spheres-reflexive-globular-types

open import synthetic-category-theory.synthetic-categories'
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

  type-top-cell-globe-Reflexive-Globular-Type' :
    {l : Level} {G : Reflexive-Globular-Type l l} {n : ℕ}
    (Γ : globe-Reflexive-Globular-Type G n) → UU l
  type-top-cell-globe-Reflexive-Globular-Type' Γ =
    higher-cell-sphere-Reflexive-Globular-Type
        ( underlying-sphere-globe-Reflexive-Globular-Type Γ)

  top-cell-globe-Reflexive-Globular-Type' :
    {l : Level} {G : Reflexive-Globular-Type l l} {n : ℕ}
    (Γ : globe-Reflexive-Globular-Type G n) →
    type-top-cell-globe-Reflexive-Globular-Type' Γ
  top-cell-globe-Reflexive-Globular-Type' (0-globe x) = x
  top-cell-globe-Reflexive-Globular-Type' (extend-globe x y Γ) =
      top-cell-globe-Reflexive-Globular-Type' Γ

  Higher-Dependent-Family-Synthetic-Category-Theory :
    {l : Level} {n : ℕ} {m : ℕ}
    {K : Cosmos-Synthetic-Category-Theory l}
    (Γ : globe-Synthetic-Category-Theory K (succ-ℕ n)) →
    UU (lsuc l)
  Higher-Dependent-Family-Synthetic-Category-Theory {n = n} {m = m} {K = K} Γ = 
    (g : type-top-cell-globe-Reflexive-Globular-Type' Γ) →
    (α : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( underlying-sphere-globe-Reflexive-Globular-Type Γ)
        ( top-cell-globe-Reflexive-Globular-Type' Γ)
        ( g))) →
    sphere-Synthetic-Category-Theory K (succ-ℕ (succ-ℕ m))

  point-Dependent-Family-Synthetic-Category-Theory :
    {l : Level} {n : ℕ} {m : ℕ}
    {K : Cosmos-Synthetic-Category-Theory l}
    {Γ : globe-Synthetic-Category-Theory K (succ-ℕ n)}
    (P : Higher-Dependent-Family-Synthetic-Category-Theory {l} {n} {m} {K} Γ) →
    (g : type-top-cell-globe-Reflexive-Globular-Type' Γ) →
    (α : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( underlying-sphere-globe-Reflexive-Globular-Type Γ)
        ( top-cell-globe-Reflexive-Globular-Type' Γ)
        ( g))) → UU l
  point-Dependent-Family-Synthetic-Category-Theory {K = K} P g α =
    iso-Synthetic-Category-Theory K (P g α)

  induction-base-Dependent-Family-Synthetic-Category-Theory :
    {l : Level} {n : ℕ} {m : ℕ}
    {K : Cosmos-Synthetic-Category-Theory l}
    {Γ : globe-Synthetic-Category-Theory K (succ-ℕ n)}
    (P : Higher-Dependent-Family-Synthetic-Category-Theory {l} {n} {m} {K} Γ) →
    UU l
  induction-base-Dependent-Family-Synthetic-Category-Theory {K = K} {Γ = Γ} P =
    point-Dependent-Family-Synthetic-Category-Theory {K = K} {Γ = Γ} P
      ( top-cell-globe-Reflexive-Globular-Type' Γ)
      ( id-iso-Synthetic-Category-Theory K
        ( underlying-sphere-globe-Reflexive-Globular-Type Γ)
        ( top-cell-globe-Reflexive-Globular-Type' Γ))

  section-Dependent-Family-Synthetic-Category-Theory :
    {l : Level} {n : ℕ} {m : ℕ}
    {K : Cosmos-Synthetic-Category-Theory l}
    {Γ : globe-Synthetic-Category-Theory K (succ-ℕ n)}
    (P : Higher-Dependent-Family-Synthetic-Category-Theory {l} {n} {m} {K} Γ) →
    UU l
  section-Dependent-Family-Synthetic-Category-Theory {K = K} {Γ = Γ} P = 
    (g : type-top-cell-globe-Reflexive-Globular-Type' Γ) →
    (α : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( underlying-sphere-globe-Reflexive-Globular-Type Γ)
        ( top-cell-globe-Reflexive-Globular-Type' Γ)
        ( g))) →
    point-Dependent-Family-Synthetic-Category-Theory {K = K} {Γ = Γ} P g α

```  