# Higher path induction for synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.path-induction-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.equivalences

open import elementary-number-theory.natural-numbers

open import globular-types.reflexive-globular-types
open import globular-types.globular-spheres-reflexive-globular-types

open import synthetic-category-theory.synthetic-categories
open import synthetic-category-theory.dependent-families-synthetic-categories
open import globular-types.reflexive-globular-equivalences
```

</details>

## Idea

Suppose we are given a dependent family P(g,α) of spheres in a cosmos K based in
(S,f). The path induction principle then states that in order to construct a
cell with boundary P(g,α) for every g and α, it suffices to do so just in the
case when g = f and α = id_f. The principle is modeled after path induction for
identifications. Just as the path induction principle for identifications
ensures that types have a grupoidal structure, so the path induction for
synthetic categories ensures that cells of dimension >1 have grupoidal
structure. 

```agda
module _
  {l : Level} (K : Cosmos-Synthetic-Category-Theory l)
  where

  path-induction-principle-Synthetic-Category-Theory : UU (lsuc l)
  path-induction-principle-Synthetic-Category-Theory = {n m : ℕ}
    (S : sphere-Synthetic-Category-Theory K n) →
    (f : higher-cell-sphere-Reflexive-Globular-Type S) →
    (P : Dependent-Family-Synthetic-Category-Theory
      {m = m} { G = (logos-Synthetic-Category-Theory K)} S f) →
    base-Dependent-Family-Synthetic-Category-Theory
      {S = S} {f = f} P →
    section-Dependent-Family-Synthetic-Category-Theory {S = S} {f = f} P

  path-induction-principle-iso-Synthetic-Category-Theory :
    (I : path-induction-principle-Synthetic-Category-Theory) →
    UU (lsuc l)
  path-induction-principle-iso-Synthetic-Category-Theory I = {n m : ℕ}
    (S : sphere-Synthetic-Category-Theory K n) →
    (f : higher-cell-sphere-Reflexive-Globular-Type S) →
    (P : Dependent-Family-Synthetic-Category-Theory
      {m = m} { G = (logos-Synthetic-Category-Theory K)} S f) →
    (c : base-Dependent-Family-Synthetic-Category-Theory
      {S = S} {f = f} P) →
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( P f (refl-sphere-suspension-Reflexive-Globular-Type S f))
        ( I S f P c f (refl-sphere-suspension-Reflexive-Globular-Type S f))
        ( c))
```

### The path induction axiom for a cosmos K

```agda
record
  path-induction-Synthetic-Category-Theory
  {l : Level} (K : Cosmos-Synthetic-Category-Theory l) :
  UU (lsuc l)
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
      (C : category-Synthetic-Category-Theory K) →
      path-induction-Synthetic-Category-Theory
        ( context-extension-cosmos-Synthetic-Category-Theory K C)

open path-induction-Synthetic-Category-Theory public
```

## Applications of the path induction axiom

### Inverse isomorphism

**Comment.** For an isomorphism α : f ≅ g (i.e. a cell of dimension n≥2), we
obtain an isomorphism α^-1 : g ≅ f together with a (n+1)-cell id_f^-1 ≅ id_f
for every (n-1)-cell f.

```agda
module _
  {l : Level} (K : Cosmos-Synthetic-Category-Theory l)
  (I : path-induction-Synthetic-Category-Theory K)
  where

  dependent-family-inv-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f : higher-cell-sphere-Reflexive-Globular-Type S) →
    Dependent-Family-Synthetic-Category-Theory S f
  dependent-family-inv-iso-Synthetic-Category-Theory S f g α =
    suspension-sphere-Reflexive-Globular-Type S g f

  base-dependent-family-inv-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f : higher-cell-sphere-Reflexive-Globular-Type S) →
    base-Dependent-Family-Synthetic-Category-Theory {S = S} {f = f}
      ( dependent-family-inv-iso-Synthetic-Category-Theory S f)
  base-dependent-family-inv-iso-Synthetic-Category-Theory S f =
    refl-sphere-suspension-Reflexive-Globular-Type S f

  inv-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S f g)) → 
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S g f)
  inv-iso-Synthetic-Category-Theory S {f} {g} α =
    ind-Synthetic-Category-Theory I S f
      ( dependent-family-inv-iso-Synthetic-Category-Theory S f)
      ( base-dependent-family-inv-iso-Synthetic-Category-Theory S f)
      ( g)
      ( α)

  idempotent-inv-iso-id-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f : higher-cell-sphere-Reflexive-Globular-Type S) →
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S f f)
        ( inv-iso-Synthetic-Category-Theory S
          ( id-iso-Synthetic-Category-Theory K S f))
        ( id-iso-Synthetic-Category-Theory K S f))
  idempotent-inv-iso-id-iso-Synthetic-Category-Theory S f =
    ind-iso-Synthetic-Category-Theory I S f
      ( dependent-family-inv-iso-Synthetic-Category-Theory S f)
      ( base-dependent-family-inv-iso-Synthetic-Category-Theory S f)

  inv-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    nat-iso-Synthetic-Category-Theory K g f
  inv-nat-iso-Synthetic-Category-Theory {C} {D} {f} {g} α =
    inv-iso-Synthetic-Category-Theory
      ( extension-sphere C D
        -1-dim-sphere) α

  idempotent-inv-id-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    3-iso-Synthetic-Category-Theory K
      ( inv-nat-iso-Synthetic-Category-Theory
        ( id-nat-iso-Synthetic-Category-Theory K f))
      ( id-nat-iso-Synthetic-Category-Theory K f)
  idempotent-inv-id-nat-iso-Synthetic-Category-Theory {C} {D} f =
    idempotent-inv-iso-id-iso-Synthetic-Category-Theory
      ( extension-sphere C D
        -1-dim-sphere) f

  inv-3-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    {α β : nat-iso-Synthetic-Category-Theory K f g}
    (φ : 3-iso-Synthetic-Category-Theory K α β) →
    3-iso-Synthetic-Category-Theory K β α
  inv-3-iso-Synthetic-Category-Theory φ =
    inv-iso-Synthetic-Category-Theory
      ( extension-sphere _ _  ( extension-sphere _ _  -1-dim-sphere)) ( φ)

  idempotent-inv-id-3-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    4-iso-Synthetic-Category-Theory K
      ( inv-3-iso-Synthetic-Category-Theory
        ( id-3-iso-Synthetic-Category-Theory K α))
      ( id-3-iso-Synthetic-Category-Theory K α)
  idempotent-inv-id-3-iso-Synthetic-Category-Theory {C} {D} {f} {g} α =
    idempotent-inv-iso-id-iso-Synthetic-Category-Theory
      ( extension-sphere C D ( extension-sphere f g -1-dim-sphere)) ( α)

  inv-4-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    {α β : nat-iso-Synthetic-Category-Theory K f g}
    {φ ψ : 3-iso-Synthetic-Category-Theory K α β}
    (Ξ : 4-iso-Synthetic-Category-Theory K φ ψ) →
    4-iso-Synthetic-Category-Theory K ψ φ
  inv-4-iso-Synthetic-Category-Theory Ξ =
    inv-iso-Synthetic-Category-Theory
      ( extension-sphere _ _
        ( extension-sphere _ _ (extension-sphere _ _ -1-dim-sphere))) ( Ξ)
```

### Composition of isomorphisms

**Comment.** For every pair of n-isomorphisms, n≥2, α : f ≅ g and β : g ≅ h, we
obtain an n-isomorphism β ∘ α : f ≅ h and for every n-isomorphism α,
a (n+1)-isomorphism  𝔩_α : id_f ∘ α ≅ α witnessing the left unit law of
composition of isomorphisms. 

```agda
module _
  {l : Level} (K : Cosmos-Synthetic-Category-Theory l)
  (I : path-induction-Synthetic-Category-Theory K)
  where

  dependent-family-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f g : higher-cell-sphere-Reflexive-Globular-Type S) →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    Dependent-Family-Synthetic-Category-Theory S g
  dependent-family-comp-iso-Synthetic-Category-Theory S f g α h β =
      suspension-sphere-Reflexive-Globular-Type S f h

  base-dependent-family-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f g : higher-cell-sphere-Reflexive-Globular-Type S) →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    base-Dependent-Family-Synthetic-Category-Theory {S = S}
      ( dependent-family-comp-iso-Synthetic-Category-Theory S f g α)
  base-dependent-family-comp-iso-Synthetic-Category-Theory S f g α = α

  comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S f h)
  comp-iso-Synthetic-Category-Theory S {f = f} {g = g} {h = h} α β =
    ind-Synthetic-Category-Theory I S g
      ( dependent-family-comp-iso-Synthetic-Category-Theory S f g α)
      ( base-dependent-family-comp-iso-Synthetic-Category-Theory
        S f g α)
      ( h)
      ( β)
    
  left-unit-law-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S f g)
        ( comp-iso-Synthetic-Category-Theory S α
          ( id-iso-Synthetic-Category-Theory K S g))
        ( α))
  left-unit-law-comp-iso-Synthetic-Category-Theory {n} S {f} {g} α =
    ind-iso-Synthetic-Category-Theory I S g
      ( dependent-family-comp-iso-Synthetic-Category-Theory S f g α)
      ( base-dependent-family-comp-iso-Synthetic-Category-Theory
        S f g α)

  comp-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g h : functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    (β : nat-iso-Synthetic-Category-Theory K g h) →
    nat-iso-Synthetic-Category-Theory K f h
  comp-nat-iso-Synthetic-Category-Theory =
    comp-iso-Synthetic-Category-Theory
      ( extension-sphere _ _  -1-dim-sphere)
  
  left-unit-law-comp-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g :  functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    3-iso-Synthetic-Category-Theory K
      (comp-nat-iso-Synthetic-Category-Theory α
        (id-nat-iso-Synthetic-Category-Theory K g)) α
  left-unit-law-comp-nat-iso-Synthetic-Category-Theory {C} {D} {f} {g} α =
    left-unit-law-comp-iso-Synthetic-Category-Theory
      ( extension-sphere _ _
        -1-dim-sphere) α

  comp-3-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    {α β γ : nat-iso-Synthetic-Category-Theory K f g} →
    (φ : 3-iso-Synthetic-Category-Theory K α β) →
    (ψ : 3-iso-Synthetic-Category-Theory K β γ) →
    3-iso-Synthetic-Category-Theory K α γ
  comp-3-iso-Synthetic-Category-Theory =
    comp-iso-Synthetic-Category-Theory
      ( extension-sphere _ _
        ( extension-sphere _ _
          -1-dim-sphere))

  left-unit-law-comp-3-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    {α β : nat-iso-Synthetic-Category-Theory K f g} →
    (φ : 3-iso-Synthetic-Category-Theory K α β) →
    4-iso-Synthetic-Category-Theory K
      ( comp-3-iso-Synthetic-Category-Theory φ
        (id-3-iso-Synthetic-Category-Theory K β)) φ
  left-unit-law-comp-3-iso-Synthetic-Category-Theory =
      left-unit-law-comp-iso-Synthetic-Category-Theory
        ( extension-sphere _ _
          ( extension-sphere _ _
            -1-dim-sphere))

  comp-4-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    {α β : nat-iso-Synthetic-Category-Theory K f g}
    {φ ψ χ : 3-iso-Synthetic-Category-Theory K α β} →
    (Ω : 4-iso-Synthetic-Category-Theory K φ ψ) →
    (Ξ : 4-iso-Synthetic-Category-Theory K ψ χ) →
    4-iso-Synthetic-Category-Theory K φ χ
  comp-4-iso-Synthetic-Category-Theory =
    comp-iso-Synthetic-Category-Theory
      ( extension-sphere _ _
        ( extension-sphere _ _
          ( extension-sphere _ _
            -1-dim-sphere)))
```  

**Comment.** For every natural isomorphim α : f ≅ f' of functors C → D and a 
functor g : D → E, we obtain a natural isomorphism g * α : g ∘ f ≅ g ≅ f',
called the left whiskering of α by g. The operation comes with a unitality
3-isomorphism g * id_f ≅ id_(g ∘ f). Conversely, for every natural isomorphim
β : g ≅ g' of functors D → E and a functor f : C → D, we obtain a natural
isomorphism β * f : g' ∘ f ≅ g' ≅ f, called the right whiskering of β by f.
The operations come with unitality 3-isomorphisms id_g * f ≅ id_(g ∘ f) and
g * id_f ≅ id_(g ∘ f).
Similarly, for every n-isomorphism, n≥3, φ : α ≅ α' of isomorphisms f ≅ g and an
isomorphism β : g ≅ h, we obtain an isomorphism β * φ : β ∘ α ≅ β ∘ α', called
the left whiskering of φ by β. Conversely, for every n-isomorphism ψ : β ≅ β'
of isomorphisms g ≅ h and an isomorphism α : f ≅ g, we obtain an isomorphism
ψ * α : β ∘ α ≅ β' ∘ α, called the right whiskering of ψ by α. The operations
come with unitality (n+1)-isomorphism id_β * α ≅ id_(β ∘ α) and
β * id_α ≅ id_(β ∘ α).

```agda
module _
  {l : Level} (K : Cosmos-Synthetic-Category-Theory l)
  (I : path-induction-Synthetic-Category-Theory K)
  where

  dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    Dependent-Family-Synthetic-Category-Theory
      { G = logos-Synthetic-Category-Theory K}
      ( extension-sphere C D
        -1-dim-sphere) f
  dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory
    {C} {D} {E} f g f' α =
    extension-sphere C E
      ( extension-sphere
        ( comp-fun-Synthetic-Category-Theory K f g)
        ( comp-fun-Synthetic-Category-Theory K f' g)
          -1-dim-sphere)

  dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    Dependent-Family-Synthetic-Category-Theory
      { G = logos-Synthetic-Category-Theory K}
      ( extension-sphere D E
        -1-dim-sphere) g
  dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
    {C} {D} {E} f g g' β =
    extension-sphere C E
      ( extension-sphere
        ( comp-fun-Synthetic-Category-Theory K f g)
        ( comp-fun-Synthetic-Category-Theory K f g')
          -1-dim-sphere)

  base-dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    base-Dependent-Family-Synthetic-Category-Theory
      { S = extension-sphere C D
        -1-dim-sphere}
      ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory f g)
  base-dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory
    f g =
      id-nat-iso-Synthetic-Category-Theory K
        ( comp-fun-Synthetic-Category-Theory K f g)

  base-dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
    : {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    base-Dependent-Family-Synthetic-Category-Theory
      { S = extension-sphere D E
        -1-dim-sphere}
      ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory f g)
  base-dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
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
      ( extension-sphere _ _
        -1-dim-sphere)
      ( f)
      ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory f g)
      ( base-dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory
        f g)
      ( f')
      ( α)

  right-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    {g g' : functor-Synthetic-Category-Theory K D E} →
    (β : nat-iso-Synthetic-Category-Theory K g g') →
    nat-iso-Synthetic-Category-Theory K
      ( comp-fun-Synthetic-Category-Theory K f g)
      ( comp-fun-Synthetic-Category-Theory K f g')
  right-whisk-nat-iso-Synthetic-Category-Theory f {g = g} {g' = g'} β =
    ind-Synthetic-Category-Theory I
      ( extension-sphere _ _
        -1-dim-sphere)
      ( g)
      ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory f g)
      ( base-dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
        f g)
      ( g')
      ( β)

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
      ( extension-sphere _ _
        -1-dim-sphere)
      ( f)
      ( dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory f g)
      ( base-dependent-family-left-whisk-nat-iso-Synthetic-Category-Theory
        f g)

  unitality-right-whisk-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    {g g' : functor-Synthetic-Category-Theory K D E} →
    (β : nat-iso-Synthetic-Category-Theory K g g') →
    3-iso-Synthetic-Category-Theory K
      ( right-whisk-nat-iso-Synthetic-Category-Theory
        ( f)
        ( id-nat-iso-Synthetic-Category-Theory K g))
      ( id-nat-iso-Synthetic-Category-Theory K
        ( comp-fun-Synthetic-Category-Theory K f g))
  unitality-right-whisk-nat-iso-Synthetic-Category-Theory f {g = g} β =
    ind-iso-Synthetic-Category-Theory I
      ( extension-sphere _ _
        -1-dim-sphere)
      ( g)
      ( dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory f g)
      ( base-dependent-family-right-whisk-nat-iso-Synthetic-Category-Theory
        f g)

  dependent-family-left-whisk-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f g h : higher-cell-sphere-Reflexive-Globular-Type S) →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    Dependent-Family-Synthetic-Category-Theory
      ( suspension-sphere-Reflexive-Globular-Type S f g) α
  dependent-family-left-whisk-iso-Synthetic-Category-Theory S f g h α β α' φ =
    suspension-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f h)
      ( comp-iso-Synthetic-Category-Theory K I S α β)
      ( comp-iso-Synthetic-Category-Theory K I S α' β)

  dependent-family-right-whisk-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f g h : higher-cell-sphere-Reflexive-Globular-Type S) →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    Dependent-Family-Synthetic-Category-Theory
      ( suspension-sphere-Reflexive-Globular-Type S g h) β
  dependent-family-right-whisk-iso-Synthetic-Category-Theory S f g h α β β' φ =
    suspension-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f h)
      ( comp-iso-Synthetic-Category-Theory K I S α β)
      ( comp-iso-Synthetic-Category-Theory K I S α β')

  base-dependent-family-left-whisk-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f g h : higher-cell-sphere-Reflexive-Globular-Type S) →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    base-Dependent-Family-Synthetic-Category-Theory
      { S = suspension-sphere-Reflexive-Globular-Type S f g}
      ( dependent-family-left-whisk-iso-Synthetic-Category-Theory S f g h α β)
  base-dependent-family-left-whisk-iso-Synthetic-Category-Theory
    S f g h α β =
      (id-iso-Synthetic-Category-Theory K
        ( suspension-sphere-Reflexive-Globular-Type S f h)
        ( comp-iso-Synthetic-Category-Theory K I S α β))

  base-dependent-family-right-whisk-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f g h : higher-cell-sphere-Reflexive-Globular-Type S) →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    base-Dependent-Family-Synthetic-Category-Theory
      { S = suspension-sphere-Reflexive-Globular-Type S g h}
      ( dependent-family-right-whisk-iso-Synthetic-Category-Theory S f g h α β)
  base-dependent-family-right-whisk-iso-Synthetic-Category-Theory
    S f g h α β =
      (id-iso-Synthetic-Category-Theory K
        ( suspension-sphere-Reflexive-Globular-Type S f h)
        ( comp-iso-Synthetic-Category-Theory K I S α β))

  left-whisk-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    {α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)} →
    (β : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    {α' : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)} →
    (φ : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S f g) α α')) →
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S f h)
        ( comp-iso-Synthetic-Category-Theory K I S α β)
        ( comp-iso-Synthetic-Category-Theory K I S α' β))
  left-whisk-iso-Synthetic-Category-Theory S {f} {g} {h} {α} β {α'} φ =
    ind-Synthetic-Category-Theory I
      ( suspension-sphere-Reflexive-Globular-Type S f g)
      ( α)
      ( dependent-family-left-whisk-iso-Synthetic-Category-Theory S f g h α β)
      ( base-dependent-family-left-whisk-iso-Synthetic-Category-Theory
        S f g h α β)
      ( α')
      ( φ)

  right-whisk-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    {β β' : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)} →
    (φ : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S g h) β β')) →
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S f h)
        ( comp-iso-Synthetic-Category-Theory K I S α β)
        ( comp-iso-Synthetic-Category-Theory K I S α β'))
  right-whisk-iso-Synthetic-Category-Theory S {f} {g} {h} α {β} {β'} φ =
    ind-Synthetic-Category-Theory I
      ( suspension-sphere-Reflexive-Globular-Type S g h)
      ( β)
      ( dependent-family-right-whisk-iso-Synthetic-Category-Theory S f g h α β)
      ( base-dependent-family-right-whisk-iso-Synthetic-Category-Theory
        S f g h α β)
      ( β')
      ( φ)

  left-whisk-3-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g h : functor-Synthetic-Category-Theory K C D}
    {α α' : nat-iso-Synthetic-Category-Theory K f g} →
    (β : nat-iso-Synthetic-Category-Theory K g h) →
    (φ : 3-iso-Synthetic-Category-Theory K α α') →
    3-iso-Synthetic-Category-Theory K
      ( comp-nat-iso-Synthetic-Category-Theory K I α β)
      ( comp-nat-iso-Synthetic-Category-Theory K I α' β)
  left-whisk-3-iso-Synthetic-Category-Theory β φ =
    left-whisk-iso-Synthetic-Category-Theory
      ( extension-sphere _ _
        -1-dim-sphere) β φ

  right-whisk-3-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g h : functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    {β β' : nat-iso-Synthetic-Category-Theory K g h} →
    (φ : 3-iso-Synthetic-Category-Theory K β β') →
    3-iso-Synthetic-Category-Theory K
      ( comp-nat-iso-Synthetic-Category-Theory K I α β)
      ( comp-nat-iso-Synthetic-Category-Theory K I α β')
  right-whisk-3-iso-Synthetic-Category-Theory α φ =
    right-whisk-iso-Synthetic-Category-Theory
      ( extension-sphere _ _
        -1-dim-sphere) α φ
```

### Associativity of composition of isomorphisms

**Comment.** For composable n-cells, n≥2, α : f ≅ g, β : g ≅ h and γ : h ≅ k,
we obtain an associator (n+1)-isomorphism 𝔞 : (γ ∘ β) ∘ α ≅ γ ∘ (β ∘ α).

```agda
module _
  {l : Level} (K : Cosmos-Synthetic-Category-Theory l)
  (I : path-induction-Synthetic-Category-Theory K)
  where

  dependent-family-assoc-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    Dependent-Family-Synthetic-Category-Theory S h
  dependent-family-assoc-comp-iso-Synthetic-Category-Theory S {f} α β k γ =
    suspension-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f k)
      ( comp-iso-Synthetic-Category-Theory K I S α
        (comp-iso-Synthetic-Category-Theory K I S β γ))
      ( comp-iso-Synthetic-Category-Theory K I S
        (comp-iso-Synthetic-Category-Theory K I S α β) γ)
  
  base-dependent-family-assoc-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    base-Dependent-Family-Synthetic-Category-Theory {S = S}
      ( dependent-family-assoc-comp-iso-Synthetic-Category-Theory S α β)
  base-dependent-family-assoc-comp-iso-Synthetic-Category-Theory
    S {f = f} {h = h} α β =
    comp-iso-Synthetic-Category-Theory K I
      ( suspension-sphere-Reflexive-Globular-Type S f h)
      ( right-whisk-iso-Synthetic-Category-Theory K I S α
        ( left-unit-law-comp-iso-Synthetic-Category-Theory K I S β))
      ( inv-iso-Synthetic-Category-Theory K I
        ( suspension-sphere-Reflexive-Globular-Type S f h)
        ( left-unit-law-comp-iso-Synthetic-Category-Theory K I S
          ( comp-iso-Synthetic-Category-Theory K I S α β)))

  assoc-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h k : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    (γ : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S h k)) →
    higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S f k)
        ( comp-iso-Synthetic-Category-Theory K I S
          ( α)
          ( comp-iso-Synthetic-Category-Theory K I S β γ))
        ( comp-iso-Synthetic-Category-Theory K I S
          ( comp-iso-Synthetic-Category-Theory K I S α β)
          ( γ)))
  assoc-comp-iso-Synthetic-Category-Theory S {h = h} {k = k} α β γ =
    ind-Synthetic-Category-Theory I S h
      ( dependent-family-assoc-comp-iso-Synthetic-Category-Theory S α β)
      ( base-dependent-family-assoc-comp-iso-Synthetic-Category-Theory S α β)
      ( k) ( γ)
  
  assoc-comp-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g h k : functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    (β : nat-iso-Synthetic-Category-Theory K g h) →
    (γ : nat-iso-Synthetic-Category-Theory K h k) →
    3-iso-Synthetic-Category-Theory K
      ( comp-nat-iso-Synthetic-Category-Theory K I α
        ( comp-nat-iso-Synthetic-Category-Theory K I β γ))
      ( comp-nat-iso-Synthetic-Category-Theory K I
        ( comp-nat-iso-Synthetic-Category-Theory K I α β) γ)
  assoc-comp-nat-iso-Synthetic-Category-Theory =
    assoc-comp-iso-Synthetic-Category-Theory
      ( extension-sphere _ _ -1-dim-sphere)

  assoc-comp-3-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    {α β γ δ : nat-iso-Synthetic-Category-Theory K f g} →
    (φ : 3-iso-Synthetic-Category-Theory K α β) →
    (ψ : 3-iso-Synthetic-Category-Theory K β γ) →
    (χ : 3-iso-Synthetic-Category-Theory K γ δ) →
    4-iso-Synthetic-Category-Theory K
      ( comp-3-iso-Synthetic-Category-Theory K I φ
        ( comp-3-iso-Synthetic-Category-Theory K I ψ χ))
      ( comp-3-iso-Synthetic-Category-Theory K I
        ( comp-3-iso-Synthetic-Category-Theory K I φ ψ) χ)
  assoc-comp-3-iso-Synthetic-Category-Theory =
    assoc-comp-iso-Synthetic-Category-Theory
      ( extension-sphere _ _ ( extension-sphere _ _ -1-dim-sphere))
```

### The right unit law for composition of isomorphisms

**Comment.** For every n-isomorphism, n≥2, α : f ≅ g, we obtain a
(n+1)-isomorphism 𝔯_α : α ∘ id_f ≅ α witnessing the right unit law of
composition of isomorphisms. Morover, we obtain for every (n-1)-cell f : C → D
a (n+2)-isomorphism 𝔯_(id_f) ≅ 𝔩_(id_f) of (n+1)-isomorphisms id_f ∘ id_f ≅ id_f.

```agda
module _
  {l : Level} (K : Cosmos-Synthetic-Category-Theory l)
  (I : path-induction-Synthetic-Category-Theory K)
  where

  dependent-family-right-unit-law-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f : higher-cell-sphere-Reflexive-Globular-Type S) →
    Dependent-Family-Synthetic-Category-Theory S f
  dependent-family-right-unit-law-comp-iso-Synthetic-Category-Theory S f g α =
    suspension-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)
      ( comp-iso-Synthetic-Category-Theory K I S
        ( id-iso-Synthetic-Category-Theory K S f) α)
      ( α)

  base-dependent-family-right-unit-law-comp-iso-Synthetic-Category-Theory 
    :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f : higher-cell-sphere-Reflexive-Globular-Type S) →
    base-Dependent-Family-Synthetic-Category-Theory {S = S}
      ( dependent-family-right-unit-law-comp-iso-Synthetic-Category-Theory S f)
  base-dependent-family-right-unit-law-comp-iso-Synthetic-Category-Theory
    S f = left-unit-law-comp-iso-Synthetic-Category-Theory K I S
      ( id-iso-Synthetic-Category-Theory K S f)

  right-unit-law-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S f g)
        ( comp-iso-Synthetic-Category-Theory K I S
          ( id-iso-Synthetic-Category-Theory K S f)
          ( α))
        ( α))
  right-unit-law-comp-iso-Synthetic-Category-Theory S {f} {g} α =
    ind-Synthetic-Category-Theory I S f
      ( dependent-family-right-unit-law-comp-iso-Synthetic-Category-Theory S f)
      ( base-dependent-family-right-unit-law-comp-iso-Synthetic-Category-Theory
        S f) g α

  right-unit-law-comp-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K}
    {f g : functor-Synthetic-Category-Theory K C D}
    (α : nat-iso-Synthetic-Category-Theory K f g) →
    3-iso-Synthetic-Category-Theory K
      ( comp-nat-iso-Synthetic-Category-Theory K I
        ( id-nat-iso-Synthetic-Category-Theory K f)
        ( α))
      ( α)
  right-unit-law-comp-nat-iso-Synthetic-Category-Theory =
    right-unit-law-comp-iso-Synthetic-Category-Theory
      ( extension-sphere _ _
        -1-dim-sphere) 

  iso-right-left-unit-law-comp-id-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    (f : higher-cell-sphere-Reflexive-Globular-Type S) →
    iso-Synthetic-Category-Theory K 
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type
          ( suspension-sphere-Reflexive-Globular-Type S f f)
          ( comp-iso-Synthetic-Category-Theory K I S
            ( id-iso-Synthetic-Category-Theory K S f)
            ( id-iso-Synthetic-Category-Theory K S f))
          ( id-iso-Synthetic-Category-Theory K S f))
        ( right-unit-law-comp-iso-Synthetic-Category-Theory S
          ( id-iso-Synthetic-Category-Theory K S f))
        ( left-unit-law-comp-iso-Synthetic-Category-Theory K I S
          ( id-iso-Synthetic-Category-Theory K S f)))
  iso-right-left-unit-law-comp-id-iso-Synthetic-Category-Theory S f =
    ind-iso-Synthetic-Category-Theory I S f
      ( dependent-family-right-unit-law-comp-iso-Synthetic-Category-Theory S f)
      ( base-dependent-family-right-unit-law-comp-iso-Synthetic-Category-Theory
        S f)


  iso-right-left-unit-law-comp-id-nat-iso-Synthetic-Category-Theory :
    {C D : category-Synthetic-Category-Theory K} →
    (f : functor-Synthetic-Category-Theory K C D) →
    4-iso-Synthetic-Category-Theory K
      ( right-unit-law-comp-nat-iso-Synthetic-Category-Theory
        ( id-nat-iso-Synthetic-Category-Theory K f))
      ( left-unit-law-comp-nat-iso-Synthetic-Category-Theory K I
        ( id-nat-iso-Synthetic-Category-Theory K f))
  iso-right-left-unit-law-comp-id-nat-iso-Synthetic-Category-Theory {C} {D} =
    iso-right-left-unit-law-comp-id-iso-Synthetic-Category-Theory
      ( extension-sphere C D
        -1-dim-sphere)
```

### Horizontal composition of isomorphisms

**Comment.** Applying the path induction twice, we obtain for every pair of
n-isomorphisms α : f ≅ f' of (n-1)-cells C → D and a n-isomorphism β : g ≅ g'
of (n-1)-cells D → E, a n-isomorphism β ∘_h α : g ∘ f ≅ g' ∘ f'. The operation
comes equipped with a 3-isomorphism id_g ∘_h id_f ≅ id_(g∘f) for every pair of
functors f,g.

```agda
module _
  {l : Level} (K : Cosmos-Synthetic-Category-Theory l)
  (I : path-induction-Synthetic-Category-Theory K)
  where

  dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    Dependent-Family-Synthetic-Category-Theory
      { G = logos-Synthetic-Category-Theory K}
      ( extension-sphere D E
        -1-dim-sphere) g
  dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g g' α =
    extension-sphere _ _
      ( extension-sphere
        ( comp-fun-Synthetic-Category-Theory K f g)
        ( comp-fun-Synthetic-Category-Theory K f g')
          -1-dim-sphere)

  base-dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g : functor-Synthetic-Category-Theory K D E) →
    base-Dependent-Family-Synthetic-Category-Theory
      { S = (extension-sphere D E 
        -1-dim-sphere)}
      ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g)
  base-dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory
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
      ( extension-sphere _ _
        -1-dim-sphere)
      ( g)
      ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g)
      ( base-dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory
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
      ( extension-sphere _ _
        -1-dim-sphere)
      ( g)
      ( dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory f g)
      ( base-dependent-family-partial-hor-comp-nat-iso-Synthetic-Category-Theory
        f g)

  dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g g' : functor-Synthetic-Category-Theory K D E) →
    Dependent-Family-Synthetic-Category-Theory
      { G = logos-Synthetic-Category-Theory K}
      ( extension-sphere C D
        -1-dim-sphere) f
  dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory f g g' f' α =
    extension-sphere _ _
      ( extension-sphere
        ( comp-fun-Synthetic-Category-Theory K f g)
        ( comp-fun-Synthetic-Category-Theory K f' g')
          -1-dim-sphere)

  base-dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory :
    {C D E : category-Synthetic-Category-Theory K}
    (f : functor-Synthetic-Category-Theory K C D) →
    (g g' : functor-Synthetic-Category-Theory K D E) →
    (β : nat-iso-Synthetic-Category-Theory K g g') →
    base-Dependent-Family-Synthetic-Category-Theory
      { S = (extension-sphere _ _ 
        -1-dim-sphere)}
      ( dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory f g g')
  base-dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory
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
        (extension-sphere _ _ 
          -1-dim-sphere)
        ( f)
        ( dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory f g g')
        ( base-dependent-family-hor-comp-nat-iso-Synthetic-Category-Theory
          f g g' β)
        ( f')
        ( α)

  dependent-family-partial-hor-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    Dependent-Family-Synthetic-Category-Theory
      ( suspension-sphere-Reflexive-Globular-Type S g h) β
  dependent-family-partial-hor-comp-iso-Synthetic-Category-Theory
    S {f = f} {h = h} α β β' φ =
    suspension-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f h)
      ( comp-iso-Synthetic-Category-Theory K I S α β)
      ( comp-iso-Synthetic-Category-Theory K I S α β')

  base-dependent-family-partial-hor-comp-iso-Synthetic-Category-Theory
    : {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    base-Dependent-Family-Synthetic-Category-Theory
      { S = suspension-sphere-Reflexive-Globular-Type S g h}
      ( dependent-family-partial-hor-comp-iso-Synthetic-Category-Theory S α β)
  base-dependent-family-partial-hor-comp-iso-Synthetic-Category-Theory
    S {f} {g} {h} α β = id-iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S f h)
      ( comp-iso-Synthetic-Category-Theory K I S α β)
    
  partial-hor-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    {β β' : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S g h)} →
    (α : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (φ : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S g h) β β')) →
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S f h)
        ( comp-iso-Synthetic-Category-Theory K I S α β)
        ( comp-iso-Synthetic-Category-Theory K I S α β'))
  partial-hor-comp-iso-Synthetic-Category-Theory S {f} {g} {h} {β} {β'}  α φ =
    ind-Synthetic-Category-Theory I
      ( suspension-sphere-Reflexive-Globular-Type S g h) _
      ( dependent-family-partial-hor-comp-iso-Synthetic-Category-Theory S α β)
      ( base-dependent-family-partial-hor-comp-iso-Synthetic-Category-Theory
        S α β)
      ( β')
      ( φ)

  dependent-family-hor-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β β' : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    Dependent-Family-Synthetic-Category-Theory
      ( suspension-sphere-Reflexive-Globular-Type S f g) α
  dependent-family-hor-comp-iso-Synthetic-Category-Theory
    S {f} {g} {h} α β β' α' φ =
    suspension-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f h)
      ( comp-iso-Synthetic-Category-Theory K I S α β)
      ( comp-iso-Synthetic-Category-Theory K I S α' β')

  base-dependent-family-hor-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    (α : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S f g)) →
    (β β' : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S g h)) →
    (φ : higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S g h) β β')) →
    base-Dependent-Family-Synthetic-Category-Theory
      { S = suspension-sphere-Reflexive-Globular-Type S f g}
      ( dependent-family-hor-comp-iso-Synthetic-Category-Theory S α β β')
  base-dependent-family-hor-comp-iso-Synthetic-Category-Theory
    S α β β' φ = partial-hor-comp-iso-Synthetic-Category-Theory S α φ

  hor-comp-iso-Synthetic-Category-Theory :
    {n : ℕ} (S : sphere-Synthetic-Category-Theory K (succ-ℕ n)) →
    {f g h : higher-cell-sphere-Reflexive-Globular-Type S} →
    {α α' : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S f g)} →
    {β β' : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type S g h)} →
    (φ : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S f g) α α')) →
    (ψ : iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S g h) β β')) →
    iso-Synthetic-Category-Theory K
      ( suspension-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S f h)
        ( comp-iso-Synthetic-Category-Theory K I S α β)
        ( comp-iso-Synthetic-Category-Theory K I S α' β'))
  hor-comp-iso-Synthetic-Category-Theory S {f} {g} {h} {α} {α'} {β} {β'} φ ψ =
    ind-Synthetic-Category-Theory I
      ( suspension-sphere-Reflexive-Globular-Type S f g)
      ( α)
      ( dependent-family-hor-comp-iso-Synthetic-Category-Theory S α β β')
      ( base-dependent-family-hor-comp-iso-Synthetic-Category-Theory
        S α β β' ψ)
      ( α')
      ( φ)
    
```