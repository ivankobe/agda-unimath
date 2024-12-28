# Path induction for synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.path-induction-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import elementary-number-theory.natural-numbers

open import globular-types.reflexive-globular-types
open import globular-types.globular-spheres-reflexive-globular-types

open import synthetic-category-theory.synthetic-categories
open import synthetic-category-theory.dependent-families-synthetic-categories
```

</details>

## Idea

The path induction principle for a cosmos K of synthetic categories states that
for every dependent family of spheres in K with base f, if we have a category in
P(f,id_f), there exists a section of P. In other words, to define a dependent
family of cells of K, it suffices to define just the one determined by f, id_f.
This is a powerful principle which we will use to define many important
operations of the language of synthetic categories and derive their coherence
properties.

```agda
module _
  {l1 l2 : Level} (K : Cosmos-Synthetic-Category-Theory l1 l2)
  where

  path-induction-principle-Synthetic-Category-Theory : UU (lsuc l1 ⊔ lsuc l2)
  path-induction-principle-Synthetic-Category-Theory =
    {C D : category-Synthetic-Category-Theory K} {n : ℕ}
    {f : functor-Synthetic-Category-Theory K C D} →
    (P : Dependent-Family-Synthetic-Category-Theory K f {n = n}) →
    induction-base-Dependent-Family-Synthetic-Category-Theory P →
    section-Dependent-Family-Synthetic-Category-Theory P

  path-induction-principle-iso-Synthetic-Category-Theory :
    (I : path-induction-principle-Synthetic-Category-Theory) →
    UU (lsuc l1 ⊔ lsuc l2)
  path-induction-principle-iso-Synthetic-Category-Theory I =
    {C D : category-Synthetic-Category-Theory K} {n : ℕ} → 
    {f : functor-Synthetic-Category-Theory K C D} →
    (P : Dependent-Family-Synthetic-Category-Theory K f {n = n}) →
    (c : induction-base-Dependent-Family-Synthetic-Category-Theory P) →
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( higher-cells-Dependent-Family-Synthetic-Category-Theory P f
          ( id-nat-iso-Synthetic-Category-Theory K f))
        ( I P c f (id-nat-iso-Synthetic-Category-Theory K f))
        ( c))
```

### The path induction axiom for a cosmos K

```agda
record
  path-induction-Synthetic-Category-Theory
  {l1 l2 : Level} (K : Cosmos-Synthetic-Category-Theory l1 l2) :
  UU (lsuc l1 ⊔ lsuc l2)
  where
  coinductive
  field
    ind-Synthetic-Category-Theory :
      path-induction-principle-Synthetic-Category-Theory K
  field
    ind-iso-Synthetic-Category-Theory :
      path-induction-principle-iso-Synthetic-Category-Theory K
        ind-Synthetic-Category-Theory
  field
    ind-ctx-Synthetic-Category-Theory :
      (Γ : category-Synthetic-Category-Theory K) →
      path-induction-Synthetic-Category-Theory
        ( context-extension-cosmos-Synthetic-Category-Theory K Γ)

open path-induction-Synthetic-Category-Theory public
```

## Applications of the path induction axiom

### Inverse natural isomorphism

**Comment.** For a natural isomorphism α : f ⇒ g, we obtain a natural
isomorphism α^-1 : g ⇒ f together with a 3-isomorphism id_f^-1 ≅ id_f for every
functor f.

```agda
module _
  {l1 l2 : Level} (K : Cosmos-Synthetic-Category-Theory l1 l2)
  (I : path-induction-Synthetic-Category-Theory K)
  where

  dependent-family-inv-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    Dependent-Family-Synthetic-Category-Theory K f
  left-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-inv-nat-iso-Synthetic-Category-Theory {C = C} f) g α = C
  right-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-inv-nat-iso-Synthetic-Category-Theory {D = D} f) g α = D
  left-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-inv-nat-iso-Synthetic-Category-Theory f) g α = g
  right-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-inv-nat-iso-Synthetic-Category-Theory f) g α = f
  higher-cells-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-inv-nat-iso-Synthetic-Category-Theory f) g α =
      empty-sphere-Reflexive-Globular-Type

  induction-base-dependent-family-inv-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    induction-base-Dependent-Family-Synthetic-Category-Theory
      ( dependent-family-inv-nat-iso-Synthetic-Category-Theory f)
  induction-base-dependent-family-inv-nat-iso-Synthetic-Category-Theory f =
    id-nat-iso-Synthetic-Category-Theory K f

  inv-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    nat-iso-Synthetic-Category-Theory K g f
  inv-nat-iso-Synthetic-Category-Theory {f = f} {g = g} α =
    ind-Synthetic-Category-Theory I
      ( dependent-family-inv-nat-iso-Synthetic-Category-Theory f)
      ( induction-base-dependent-family-inv-nat-iso-Synthetic-Category-Theory f)
      ( g)
      ( α)
  
  idempotent-inv-iso-id-fun-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    3-iso-Synthetic-Category-Theory
      ( K)
      (inv-nat-iso-Synthetic-Category-Theory (id-nat-iso-Synthetic-Category-Theory K f))
      ( id-nat-iso-Synthetic-Category-Theory K f)
  idempotent-inv-iso-id-fun-Synthetic-Category-Theory f = 
    ind-iso-Synthetic-Category-Theory I
      (dependent-family-inv-nat-iso-Synthetic-Category-Theory f)
      (induction-base-dependent-family-inv-nat-iso-Synthetic-Category-Theory f)
``` 

### Composition of natural isomorphisms

**Comment.** For every pair of natural isomorphisms α : f ⇒ g and β : g ⇒ h, we
obtain a natural isomorphism β ∘ α : f ⇒ h and for every α, a 3-isomorphism 
𝔩_α : id_f ∘ α ≅ α witnessing the left unit law of composition of natural
isomorphisms. 

```agda
module _
  {l1 l2 : Level} (K : Cosmos-Synthetic-Category-Theory l1 l2)
  (I : path-induction-Synthetic-Category-Theory K)
  (L : left-unit-law-composition-functor-Synthetic-Category-Theory K)
  where

  dependent-family-comp-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K C D) →
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    Dependent-Family-Synthetic-Category-Theory K g
  left-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-comp-nat-iso-Synthetic-Category-Theory {C = C} f g α)
    h β = C
  right-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-comp-nat-iso-Synthetic-Category-Theory {D = D} f g α)
    h β = D
  left-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-comp-nat-iso-Synthetic-Category-Theory f g α) h β = f
  right-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-comp-nat-iso-Synthetic-Category-Theory f g α) h β = h
  higher-cells-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-comp-nat-iso-Synthetic-Category-Theory f g α) h β =
    empty-sphere-Reflexive-Globular-Type  

  induction-base-dependent-family-comp-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K C D) →
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    induction-base-Dependent-Family-Synthetic-Category-Theory
      ( dependent-family-comp-nat-iso-Synthetic-Category-Theory f g α)
  induction-base-dependent-family-comp-nat-iso-Synthetic-Category-Theory f g α =
    α

  comp-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g h :  functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    (β : nat-iso-Synthetic-Category-Theory K g h) →
    nat-iso-Synthetic-Category-Theory K f h
  comp-nat-iso-Synthetic-Category-Theory {f = f} {g = g} {h = h} α β =
    ind-Synthetic-Category-Theory I
      ( dependent-family-comp-nat-iso-Synthetic-Category-Theory f g α)
      ( induction-base-dependent-family-comp-nat-iso-Synthetic-Category-Theory
        f g α)
      ( h)
      ( β)

  left-unit-law-comp-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g :  functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    3-iso-Synthetic-Category-Theory K
      (comp-nat-iso-Synthetic-Category-Theory α
        (id-nat-iso-Synthetic-Category-Theory K g)) α
  left-unit-law-comp-nat-iso-Synthetic-Category-Theory {f = f} {g = g} α =
    ind-iso-Synthetic-Category-Theory I
    ( dependent-family-comp-nat-iso-Synthetic-Category-Theory f g α)
    ( induction-base-dependent-family-comp-nat-iso-Synthetic-Category-Theory
      f g α)
``` 

## Whiskering of natural isomorphisms

**Comment.** For every natural isomorphim α : f ≅ f' of functors C → D and a 
functor g : D → E, we obtain a natural isomorphism g * α : g ∘ f ≅ g ≅ f',
called the left whiskering of α by g. The operation comes with a unitality
3-isomorphism g * id_f ≅ id_(g ∘ f). Conversely, For every natural isomorphim
β : g ≅ g' of functors D → E and a functor f : C → D, we obtain a natural
isomorphism β * f : g' ∘ f ≅ g' ≅ f, called the right whiskering of β by f.
The operation comes with a unitality 3-isomorphism id_g * f ≅ id_(g ∘ f).

```agda
module _
  {l1 l2 : Level} (K : Cosmos-Synthetic-Category-Theory l1 l2)
  (I : path-induction-Synthetic-Category-Theory K)
  (L : left-unit-law-composition-functor-Synthetic-Category-Theory K)
  where

  dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    Dependent-Family-Synthetic-Category-Theory K f
  left-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory {C = C} f g)
    f' α = C
  right-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory {E = E} f g)
    f' α = E
  left-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory f g) f' α =
      comp-fun-Synthetic-Category-Theory K f g
  right-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory f g) f' α =
      comp-fun-Synthetic-Category-Theory K f' g
  higher-cells-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory f g) f' α =
      empty-sphere-Reflexive-Globular-Type

  induction-base-dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    induction-base-Dependent-Family-Synthetic-Category-Theory
      ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory f g)
  induction-base-dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory
    f g =
      id-nat-iso-Synthetic-Category-Theory K
        ( comp-fun-Synthetic-Category-Theory K f g)
    
  left-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    {f f' : functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f f') →
    (g : functor-Synthetic-Category-Theory K D E) →
    nat-iso-Synthetic-Category-Theory K
      ( comp-fun-Synthetic-Category-Theory K f g)
      ( comp-fun-Synthetic-Category-Theory K f' g)
  left-whisk-nat-iso-Synthetic-Category-Theory {f = f} {f' = f'} α g =
    ind-Synthetic-Category-Theory I
      ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory f g)
      ( induction-base-dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory
        f g)
      ( f')
      ( α)

  unitality-left-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    {f f' : functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f f') →
    (g : functor-Synthetic-Category-Theory K D E) →
    3-iso-Synthetic-Category-Theory K
      ( left-whisk-nat-iso-Synthetic-Category-Theory
        ( id-nat-iso-Synthetic-Category-Theory K f)
        ( g))
      ( id-nat-iso-Synthetic-Category-Theory K
        ( comp-fun-Synthetic-Category-Theory K f g))
  unitality-left-whisk-nat-iso-Synthetic-Category-Theory {f = f} α g =
    ind-iso-Synthetic-Category-Theory I
      ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory f g)
      ( induction-base-dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory
        f g)

  dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    Dependent-Family-Synthetic-Category-Theory K g
  left-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
      {C = C} f g) g' α = C
  right-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
      {E = E} f g) g' α = E
  left-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory f g) g' α =
      comp-fun-Synthetic-Category-Theory K f g
  right-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory f g) g' α =
      comp-fun-Synthetic-Category-Theory K f g'
  higher-cells-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory f g) g' α =
      empty-sphere-Reflexive-Globular-Type

  induction-base-dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
    :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    induction-base-Dependent-Family-Synthetic-Category-Theory
      ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory f g)
  induction-base-dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
    f g =
      id-nat-iso-Synthetic-Category-Theory K
        ( comp-fun-Synthetic-Category-Theory K f g)

  right-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    {g g' : functor-Synthetic-Category-Theory K D E} →
    (α : nat-iso-Synthetic-Category-Theory K g g') →
    (f : functor-Synthetic-Category-Theory K C D) →
    nat-iso-Synthetic-Category-Theory K
      ( comp-fun-Synthetic-Category-Theory K f g)
      ( comp-fun-Synthetic-Category-Theory K f g')
  right-whisk-nat-iso-Synthetic-Category-Theory {g = g} {g' = g'} α f =
    ind-Synthetic-Category-Theory I
      ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory f g)
      ( induction-base-dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
        f g)
      ( g')
      ( α)

  unitality-right-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    {g : functor-Synthetic-Category-Theory K D E} →
    (f : functor-Synthetic-Category-Theory K C D) →
    3-iso-Synthetic-Category-Theory K
      ( right-whisk-nat-iso-Synthetic-Category-Theory
        ( id-nat-iso-Synthetic-Category-Theory K g)
        ( f))
      ( id-nat-iso-Synthetic-Category-Theory K
        ( comp-fun-Synthetic-Category-Theory K f g))
  unitality-right-whisk-nat-iso-Synthetic-Category-Theory {g = g} f =
    ind-iso-Synthetic-Category-Theory I
      ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory f g)
      ( induction-base-dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
        f g)
```

### The right unit law for composition of natural isomorphisms

**Comment.** For every natural isomorphism α : f ≅ g, we obtain a 3-isomorphism
𝔯_α : α ∘ id_f ≅ α witnessing the right unit law of composition of natural
isomorphisms. Morover, we obtain for every functor f : C → D a 4-isomorphism
𝔯_(id_f) ≅ 𝔩_(id_f) of 3-isomorphisms id_f ∘ id_f ≅ id_f.

```agda
module _
  {l1 l2 : Level} (K : Cosmos-Synthetic-Category-Theory l1 l2)
  (I : path-induction-Synthetic-Category-Theory K)
  (L : left-unit-law-composition-functor-Synthetic-Category-Theory K)
  where

  dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    Dependent-Family-Synthetic-Category-Theory K f
  left-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory
      {C = C} f) g α = C
  right-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory
      {D = D} f) g α = D
  left-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory f)
      g α = f
  right-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory f)
      g α = g
  higher-cells-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory f)
      g α =
    extension-sphere-Reflexive-Globular-Type
      ( comp-nat-iso-Synthetic-Category-Theory K I L
        (id-nat-iso-Synthetic-Category-Theory K f)
        ( α))
      ( α)
      ( empty-sphere-Reflexive-Globular-Type)

  induction-base-dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    induction-base-Dependent-Family-Synthetic-Category-Theory
      ( dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory
        f)
  induction-base-dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory
    f =
    left-unit-law-comp-nat-iso-Synthetic-Category-Theory K I L
      ( id-nat-iso-Synthetic-Category-Theory K f)

  right-unit-law-comp-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    3-iso-Synthetic-Category-Theory K
      ( comp-nat-iso-Synthetic-Category-Theory K I L
        ( id-nat-iso-Synthetic-Category-Theory K f)
        ( α))
      ( α)
  right-unit-law-comp-iso-Synthetic-Category-Theory {f = f} {g = g} α =
    ind-Synthetic-Category-Theory I
      ( dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory
        f)
      ( induction-base-dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory
        f)
      ( g)
      ( α)

  4-iso-id-nat-iso-left-right-unit-law-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K} →
    (f : functor-Synthetic-Category-Theory K C D) →
    4-iso-Synthetic-Category-Theory K
      ( right-unit-law-comp-iso-Synthetic-Category-Theory
        ( id-nat-iso-Synthetic-Category-Theory K f))
      ( left-unit-law-comp-nat-iso-Synthetic-Category-Theory K I L
        ( id-nat-iso-Synthetic-Category-Theory K f))
  4-iso-id-nat-iso-left-right-unit-law-Synthetic-Category-Theory f =
    ind-iso-Synthetic-Category-Theory I
      ( dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory
        f)
      ( induction-base-dependent-family-right-unit-law-comp-nat-iso-Synthetic-Category-Theory
        f)    
```

### Horizontal composition of natural isomorphisms

**Comment.** Applying the path induction twice, we obtain for every pair of
natural isomorphisms α : f ≅ f' of functors C → D and β : g ≅ g' of functors
D → E, a natural isomorphism β ∘_h α : g ∘ f ≅ g' ∘ f'. The operation comes
equipped with a 3-isomorphism id_g ∘_h id_f ≅ id_(g∘f) for every pair of
functors f,g.

```agda
module _
  {l1 l2 : Level} (K : Cosmos-Synthetic-Category-Theory l1 l2)
  (I : path-induction-Synthetic-Category-Theory K)
  (L : left-unit-law-composition-functor-Synthetic-Category-Theory K)
  where

  dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    Dependent-Family-Synthetic-Category-Theory K g
  left-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory
      {C = C} f g) g' α = C
  right-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory
      {E = E} f g) g' α = E
  left-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g)
      g' α = comp-fun-Synthetic-Category-Theory K f g
  right-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g)
      g' α = comp-fun-Synthetic-Category-Theory K f g'
  higher-cells-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g)
      g' α = empty-sphere-Reflexive-Globular-Type

  induction-base-dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    induction-base-Dependent-Family-Synthetic-Category-Theory
      ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g)
  induction-base-dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory
    f g = id-nat-iso-Synthetic-Category-Theory K
      ( comp-fun-Synthetic-Category-Theory K f g)

  partial-hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    {g g' : functor-Synthetic-Category-Theory K D E}
    (f : functor-Synthetic-Category-Theory K C D) →
    (β : nat-iso-Synthetic-Category-Theory K g g') →
    nat-iso-Synthetic-Category-Theory K
      ( comp-fun-Synthetic-Category-Theory K f g)
      ( comp-fun-Synthetic-Category-Theory K f g')
  partial-hor-comp-nat-iso-Synthetic-Category-Theory {g = g} {g' = g'} f β =
    ind-Synthetic-Category-Theory I
      ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g)
      ( induction-base-dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory
        f g)
      ( g')
      ( β)

  coherence-partial-hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    3-iso-Synthetic-Category-Theory K
      ( partial-hor-comp-nat-iso-Synthetic-Category-Theory
        ( f)
        ( id-nat-iso-Synthetic-Category-Theory K g))
      ( id-nat-iso-Synthetic-Category-Theory K
        ( comp-fun-Synthetic-Category-Theory K f g))
  coherence-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g =
    ind-iso-Synthetic-Category-Theory I
      ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g)
      ( induction-base-dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g)

  dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g g' : functor-Synthetic-Category-Theory K D E) →
    Dependent-Family-Synthetic-Category-Theory K f
  left-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory
      {C = C} f g g') f' α = C
  right-cat-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory
      {E = E} f g g') f' α = E
  left-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory f g g')
      f' α = comp-fun-Synthetic-Category-Theory K f g
  right-fun-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory f g g')
      f' α = comp-fun-Synthetic-Category-Theory K f' g'
  higher-cells-Dependent-Family-Synthetic-Category-Theory
    ( dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory f g g')
      f' α = empty-sphere-Reflexive-Globular-Type
      
  induction-base-dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g g' : functor-Synthetic-Category-Theory K D E) →
    (β : nat-iso-Synthetic-Category-Theory K g g') →
    induction-base-Dependent-Family-Synthetic-Category-Theory
      ( dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory f g g')
  induction-base-dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory
    f g g' β = partial-hor-comp-nat-iso-Synthetic-Category-Theory f β

  hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    {f f' : functor-Synthetic-Category-Theory K C D}
    {g g' : functor-Synthetic-Category-Theory K D E}
    (α : nat-iso-Synthetic-Category-Theory K f f') →
    (β : nat-iso-Synthetic-Category-Theory K g g') →
    nat-iso-Synthetic-Category-Theory K
      ( comp-fun-Synthetic-Category-Theory K f g)
      ( comp-fun-Synthetic-Category-Theory K f' g')
  hor-comp-nat-iso-Synthetic-Category-Theory
    {f = f} {f' = f'} {g = g} {g' = g'} α β =
      ind-Synthetic-Category-Theory I
        ( dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory f g g')
        ( induction-base-dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory
          f g g' β)
        ( f')
        ( α)
```