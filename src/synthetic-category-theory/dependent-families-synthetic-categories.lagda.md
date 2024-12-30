# Dependent families of (spheres in the language of) synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.dependent-families-synthetic-categories where
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

```agda 
record
  Dependent-Family-Synthetic-Category-Theory
  {l1 l2 : Level} (K : Cosmos-Synthetic-Category-Theory l1 l2)
  {C D : category-Synthetic-Category-Theory K}
  (f : functor-Synthetic-Category-Theory K C D) {n : ℕ} : UU (lsuc l1 ⊔ lsuc l2)
  where

  field
    left-cat-Dependent-Family-Synthetic-Category-Theory :
      (g : functor-Synthetic-Category-Theory K C D) →
      (α : nat-iso-Synthetic-Category-Theory K f g) →
      category-Synthetic-Category-Theory K

  field
    right-cat-Dependent-Family-Synthetic-Category-Theory :
      (g : functor-Synthetic-Category-Theory K C D) →
      (α : nat-iso-Synthetic-Category-Theory K f g) →
      category-Synthetic-Category-Theory K
  
  field
    left-fun-Dependent-Family-Synthetic-Category-Theory :
      (g : functor-Synthetic-Category-Theory K C D) →
      (α : nat-iso-Synthetic-Category-Theory K f g) →
      functor-Synthetic-Category-Theory K
        ( left-cat-Dependent-Family-Synthetic-Category-Theory g α)
        ( right-cat-Dependent-Family-Synthetic-Category-Theory g α)
    
  field
    right-fun-Dependent-Family-Synthetic-Category-Theory :
      (g : functor-Synthetic-Category-Theory K C D) →
      (α : nat-iso-Synthetic-Category-Theory K f g) →
      functor-Synthetic-Category-Theory K
        ( left-cat-Dependent-Family-Synthetic-Category-Theory g α)
        ( right-cat-Dependent-Family-Synthetic-Category-Theory g α)

  field
    higher-cells-Dependent-Family-Synthetic-Category-Theory :
      (g : functor-Synthetic-Category-Theory K C D) →
      (α : nat-iso-Synthetic-Category-Theory K f g) →
      sphere-Reflexive-Globular-Type
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type
          ( functor-reflexive-globular-type-Synthetic-Category-Theory K
            ( left-cat-Dependent-Family-Synthetic-Category-Theory g α)
            ( right-cat-Dependent-Family-Synthetic-Category-Theory g α))
          ( left-fun-Dependent-Family-Synthetic-Category-Theory g α)
          ( right-fun-Dependent-Family-Synthetic-Category-Theory g α))
        ( n)

  point-Dependent-Family-Synthetic-Category-Theory :
    (g : functor-Synthetic-Category-Theory K C D) →
    (α : nat-iso-Synthetic-Category-Theory K f g) → UU l2
  point-Dependent-Family-Synthetic-Category-Theory g α =
    iso-Synthetic-Category-Theory K
      ( higher-cells-Dependent-Family-Synthetic-Category-Theory g α)

  induction-base-Dependent-Family-Synthetic-Category-Theory : UU l2
  induction-base-Dependent-Family-Synthetic-Category-Theory =
    point-Dependent-Family-Synthetic-Category-Theory
      ( f)
      ( id-nat-iso-Synthetic-Category-Theory K f)

  section-Dependent-Family-Synthetic-Category-Theory : UU l2
  section-Dependent-Family-Synthetic-Category-Theory = 
    (g : functor-Synthetic-Category-Theory K C D) →
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    point-Dependent-Family-Synthetic-Category-Theory g α

open Dependent-Family-Synthetic-Category-Theory public
```