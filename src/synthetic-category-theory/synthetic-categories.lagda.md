# Synthetic category theory

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.images 

open import elementary-number-theory.natural-numbers

open import globular-types.globular-types
open import globular-types.reflexive-globular-types
open import globular-types.globular-spheres-reflexive-globular-types
open import globular-types.superglobular-types
open import globular-types.binary-dependent-reflexive-globular-types 
```

</details>

## Idea

{{#concept "Synthetic categories"}} are defined by establishing the rules on the
type of all synthetic categories. In particular, synthetic categories are not
defined to be types of objects equipped with hom-sets and so on, but they are
simply elements of the type of synthetic categories, which is given sufficient
structure so that we can work with its elements as if they are categories.

## Definitions

### The type of synthetic categories

#### The language of synthetic categories

In synthetic category theory we may speak of categories, functors, isomorphisms
between them, isomorphisms between those, and so forth; and every n-cell should
come equipped with the identity (n+1)-cell. Moreover, every ynthetic category Γ
should determine the language of synthetic categories in context Γ. The sorts in
the language of synthetic category theory are therefore organized in a
[globular type](globular-types.globular-types.md).

```agda
record
  Cosmos-Synthetic-Category-Theory
    (l : Level) : UU (lsuc l)
  where

  coinductive

  field
    logos-Synthetic-Category-Theory : Reflexive-Globular-Type l l

  sublogos-Synthetic-Category-Theory :
    {n : ℕ} →
    ( sphere-Reflexive-Globular-Type
      logos-Synthetic-Category-Theory (succ-ℕ n)) →
    Reflexive-Globular-Type l l
  sublogos-Synthetic-Category-Theory S =
    reflexive-globular-type-non-1-dim-sphere S

  category-Synthetic-Category-Theory : UU l
  category-Synthetic-Category-Theory =
    0-cell-Reflexive-Globular-Type logos-Synthetic-Category-Theory

  field
    context-extension-cosmos-Synthetic-Category-Theory :
      category-Synthetic-Category-Theory →
      Cosmos-Synthetic-Category-Theory l

  functor-reflexive-globular-type-Synthetic-Category-Theory :
    (C D : category-Synthetic-Category-Theory) → Reflexive-Globular-Type l l
  functor-reflexive-globular-type-Synthetic-Category-Theory C D =
    reflexive-globular-type-non-1-dim-sphere
      { G = logos-Synthetic-Category-Theory}
      ( extension-sphere C D -1-dim-sphere)

  functor-Synthetic-Category-Theory :
    (C D : category-Synthetic-Category-Theory) → UU l
  functor-Synthetic-Category-Theory C D =
    0-cell-Reflexive-Globular-Type
      ( functor-reflexive-globular-type-Synthetic-Category-Theory C D)

  field
    comp-fun-Synthetic-Category-Theory :
      {C D E : category-Synthetic-Category-Theory}
      (f : functor-Synthetic-Category-Theory C D) →
      (g : functor-Synthetic-Category-Theory D E) →
      functor-Synthetic-Category-Theory C E

  id-fun-Synthetic-Category-Theory :
    {C : category-Synthetic-Category-Theory} →
    functor-Synthetic-Category-Theory C C
  id-fun-Synthetic-Category-Theory =
    refl-1-cell-Reflexive-Globular-Type logos-Synthetic-Category-Theory
      
  sphere-Synthetic-Category-Theory :
    (n : ℕ) → UU (lsuc l)
  sphere-Synthetic-Category-Theory =
      sphere-Reflexive-Globular-Type logos-Synthetic-Category-Theory


  -- a sphere determining an isomorphism is of dimension ≥2
  iso-reflexive-globular-type-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory (succ-ℕ (succ-ℕ n))) →
    Reflexive-Globular-Type l l
  iso-reflexive-globular-type-Synthetic-Category-Theory =
    reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type

  iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory (succ-ℕ (succ-ℕ n))) → UU l
  iso-Synthetic-Category-Theory = higher-cell-sphere-Reflexive-Globular-Type 

  id-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory (succ-ℕ n)) →
    (α : higher-cell-sphere-Reflexive-Globular-Type S) →
    iso-Synthetic-Category-Theory
      ( suspension-sphere-Reflexive-Globular-Type S α α)
  id-iso-Synthetic-Category-Theory = refl-sphere-suspension-Reflexive-Globular-Type

  nat-iso-reflexive-globular-type-Synthetic-Category-Theory : 
    {C D : category-Synthetic-Category-Theory}
    (f g : functor-Synthetic-Category-Theory C D) →
    Reflexive-Globular-Type l l
  nat-iso-reflexive-globular-type-Synthetic-Category-Theory {C} {D} f g =
    iso-reflexive-globular-type-Synthetic-Category-Theory {0}
      ( extension-sphere C D ( extension-sphere f g -1-dim-sphere))

  nat-iso-Synthetic-Category-Theory : 
    {C D : category-Synthetic-Category-Theory}
    (f g : functor-Synthetic-Category-Theory C D) → UU l
  nat-iso-Synthetic-Category-Theory f g =
    0-cell-Reflexive-Globular-Type
      ( nat-iso-reflexive-globular-type-Synthetic-Category-Theory f g)

  id-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory}
    (f : functor-Synthetic-Category-Theory C D) →
    nat-iso-Synthetic-Category-Theory f f
  id-nat-iso-Synthetic-Category-Theory {C} {D} f = 
    id-iso-Synthetic-Category-Theory {0}
      ( extension-sphere C D -1-dim-sphere) f

  3-iso-reflexive-globular-type-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory}
    {f g : functor-Synthetic-Category-Theory C D}
    (α β : nat-iso-Synthetic-Category-Theory f g) →
    Reflexive-Globular-Type l l
  3-iso-reflexive-globular-type-Synthetic-Category-Theory {C} {D} {f} {g}  α β =
    iso-reflexive-globular-type-Synthetic-Category-Theory {1}
      ( extension-sphere C D
        ( extension-sphere f g ( extension-sphere α β -1-dim-sphere)))

  3-iso-Synthetic-Category-Theory : 
    {C D : category-Synthetic-Category-Theory}
    {f g : functor-Synthetic-Category-Theory C D}
    (α β : nat-iso-Synthetic-Category-Theory f g) → UU l
  3-iso-Synthetic-Category-Theory α β =
    0-cell-Reflexive-Globular-Type
      ( 3-iso-reflexive-globular-type-Synthetic-Category-Theory α β)

  id-3-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory}
    {f g : functor-Synthetic-Category-Theory C D}
    (α : nat-iso-Synthetic-Category-Theory f g) →
    3-iso-Synthetic-Category-Theory α α
  id-3-iso-Synthetic-Category-Theory {C} {D} {f} {g}  α =
    id-iso-Synthetic-Category-Theory {1}
      ( extension-sphere C D ( extension-sphere f g -1-dim-sphere)) ( α)

  4-iso-reflexive-globular-type-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory}
    {f g : functor-Synthetic-Category-Theory C D}
    {α β : nat-iso-Synthetic-Category-Theory f g}
    (φ ψ : 3-iso-Synthetic-Category-Theory α β) →
    Reflexive-Globular-Type l l
  4-iso-reflexive-globular-type-Synthetic-Category-Theory φ ψ =
    iso-reflexive-globular-type-Synthetic-Category-Theory
      ( extension-sphere _ _
        ( extension-sphere _ _
          ( extension-sphere _ _ ( extension-sphere φ ψ -1-dim-sphere))))

  4-iso-Synthetic-Category-Theory : 
    {C D : category-Synthetic-Category-Theory}
    {f g : functor-Synthetic-Category-Theory C D}
    {α β : nat-iso-Synthetic-Category-Theory f g}
    (φ ψ : 3-iso-Synthetic-Category-Theory α β) → UU l
  4-iso-Synthetic-Category-Theory α β =
    0-cell-Reflexive-Globular-Type
      ( 4-iso-reflexive-globular-type-Synthetic-Category-Theory α β)

  id-4-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory}
    {f g : functor-Synthetic-Category-Theory C D}
    {α β : nat-iso-Synthetic-Category-Theory f g}
    (φ : 3-iso-Synthetic-Category-Theory α β) →
    4-iso-Synthetic-Category-Theory φ φ
  id-4-iso-Synthetic-Category-Theory φ =
    id-iso-Synthetic-Category-Theory 
      ( extension-sphere _ _
        ( extension-sphere _ _ ( extension-sphere _ _ -1-dim-sphere))) ( φ)

open Cosmos-Synthetic-Category-Theory public
```

### The left unit law for the composition of functors of synthetic categories

```agda
record
  left-unit-law-composition-functor-Synthetic-Category-Theory
  {l : Level} (K : Cosmos-Synthetic-Category-Theory l) : UU l
  where

  field
    left-unit-law-comp-fun-Synthetic-Category-Theory :
      {C D : category-Synthetic-Category-Theory K}
      (f : functor-Synthetic-Category-Theory K C D) →
      nat-iso-Synthetic-Category-Theory K
        ( comp-fun-Synthetic-Category-Theory K
          ( f)
          ( id-fun-Synthetic-Category-Theory K))
        ( f)

open left-unit-law-composition-functor-Synthetic-Category-Theory public
```

### The right unit law for the composition of functors of synthetic categories 

```agda
record
  right-unit-law-composition-functor-Synthetic-Category-Theory
  {l : Level} (K : Cosmos-Synthetic-Category-Theory l) : UU l
  where

  field
    right-unit-law-comp-fun-Synthetic-Category-Theory :
      {C D : category-Synthetic-Category-Theory K}
      (f : functor-Synthetic-Category-Theory K C D) →
      nat-iso-Synthetic-Category-Theory K
        ( comp-fun-Synthetic-Category-Theory K
          ( id-fun-Synthetic-Category-Theory K)
          ( f))
        ( f)

open right-unit-law-composition-functor-Synthetic-Category-Theory public
```
