# Globular spheres

```agda
{-# OPTIONS --guardedness #-}

module globular-types.globular-spheres-reflexive-globular-types where
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
open import globular-types.reflexive-globular-types
open import globular-types.reflexive-globular-equivalences
```

</details>

## Idea

A [globular sphere](globular-types.globular-spheres-reflexive-globular-types.md)
in a [reflexive globular type](globular-types.reflexive-globular-types.md) G is
represented by a finite list of ordered pairs of cells of G of consecutive
dimesions, starting with dimesion 0, such that the source and target of the two
n-cells in the list are the two (n-1)-cells, respectively. Such a sphere is thus
determined by data of the form [(x,y); (f,g); (α,β); ⋯], where s(f)=s(g)=x,
t(f)=t(g)=y, s(α)=s(β)=f, t(α)=t(β)=g, etc. The main idea is that globular
spheres parametrize reflexive globular subtypes of the ambient reflexive
globular type G, i.e. given such a sphere S, we can construct the reflexive
globular type of cells of G whose boundary is S. This is also the main utility
of the concept as it allows us to parametrize over cells of different
dimensions. 

A depiction of a globular sphere given by the above list would be

```text
            f
       -------------
     /   //     \\   \
    /   //       \\   ∨
   x  α||         ||β  y.
    \   \\       //   ∧
     \   V       V   /
       -------------
            g
```

Thus, a globular sphere is the globular analogue of the CW structure on a
topological sphere with two cells in each dimension.

## Definitions

### The type of globular spheres in a reflexive globular type G

**Comment.** Given a reflexive globular type G and a natural number n, we define
the type of globular spheres of G of dimension (n-1). Every such sphere is
either the "empty sphere" (a sphere of dimension -1) or it is constructed from
two 0-cells x and y of G and a globular sphere in the globular type of 1-cells
with source x and target y. E.g., the 2-dimensional globular sphere above is
constructed from 0-cells x and y, and the 1-dimensional sphere 

```text
            α
       -------------
     /               \
    /                 ∨
   f                   g
    \                 ∧
     \               /
       -------------
            β
```

in the globular type of 1-cells with source x and target y. Also note the
off-by-one miss-match in the indexing of dimensions. 

```agda
data sphere-Reflexive-Globular-Type
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) :
  ℕ → UU (lsuc l1 ⊔ lsuc l2)
  where

  empty-sphere-Reflexive-Globular-Type :
    sphere-Reflexive-Globular-Type G zero-ℕ

  extension-sphere-Reflexive-Globular-Type :
    {n : ℕ} (x y : 0-cell-Reflexive-Globular-Type G) →
    sphere-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y) n →
    sphere-Reflexive-Globular-Type G (succ-ℕ n)

open sphere-Reflexive-Globular-Type public
```

### The components of a globular sphere

**Comment.** Given a sphere of dimension ≥0, we may decompose it into its two
0-cells and the higher-dimensional data, which again form a globular sphere.


```agda
module _
  {l1 l2 : Level} {G : Reflexive-Globular-Type l1 l2} {n : ℕ}
  where

  source-0-cell-sphere-Reflexive-Globular-Type :
    (S : sphere-Reflexive-Globular-Type G (succ-ℕ n)) →
    0-cell-Reflexive-Globular-Type G
  source-0-cell-sphere-Reflexive-Globular-Type
    ( extension-sphere-Reflexive-Globular-Type x y S) = x

  target-0-cell-sphere-Reflexive-Globular-Type :
    (S : sphere-Reflexive-Globular-Type G (succ-ℕ n)) →
    0-cell-Reflexive-Globular-Type G
  target-0-cell-sphere-Reflexive-Globular-Type
    ( extension-sphere-Reflexive-Globular-Type x y S) = y
    
  sphere-higher-cells-sphere-Reflexive-Gloublar-Type :
    (S : sphere-Reflexive-Globular-Type G (succ-ℕ n)) →
    sphere-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type
        ( G)
        ( source-0-cell-sphere-Reflexive-Globular-Type S)
        ( target-0-cell-sphere-Reflexive-Globular-Type S))
      ( n)
  sphere-higher-cells-sphere-Reflexive-Gloublar-Type
    (extension-sphere-Reflexive-Globular-Type x y S) = S

```

### The reflexive globular type of cells of a reflexive globular type G whose
### boundary is the globular sphere S

**Comment.** Given a reflexive gloublar type G and a globular shphere S in G of
dimension n≥0, whose n-cells are φ and ψ, we form a globular type whose 0-cells
are the (n+1)-cells φ⇒ψ. The gloular type corresponding to the "empty" sphere
of dimesion -1 is G itself. This makes sense because every 0-cell has empty
boudary.

```agda
module _ where

  reflexive-globular-type-sphere-Reflexive-Globular-Type :
    {l1 l2 : Level} {n : ℕ}
    {G : Reflexive-Globular-Type l1 l2} →
    (S : sphere-Reflexive-Globular-Type G n) →
    Reflexive-Globular-Type l1 l2 + Reflexive-Globular-Type l2 l2
  reflexive-globular-type-sphere-Reflexive-Globular-Type {G = G}
    empty-sphere-Reflexive-Globular-Type = inl G
  reflexive-globular-type-sphere-Reflexive-Globular-Type {l1} {l2} {G}
    ( extension-sphere-Reflexive-Globular-Type x y S') = inr
      ( codiagonal _
        ( reflexive-globular-type-sphere-Reflexive-Globular-Type {l2} {l2} S'))

  reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type :
    {l : Level} {n : ℕ}
    {G : Reflexive-Globular-Type l l} →
    (S : sphere-Reflexive-Globular-Type G n) →
    Reflexive-Globular-Type l l
  reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type S =
    codiagonal _ (reflexive-globular-type-sphere-Reflexive-Globular-Type S)

  reflexive-globular-type-nonempty-sphere-Reflexive-Globular-Type :
    {l1 l2 : Level} {n : ℕ}
    {G : Reflexive-Globular-Type l1 l2} →
    (S : sphere-Reflexive-Globular-Type G (succ-ℕ n)) →
    Reflexive-Globular-Type l2 l2
  reflexive-globular-type-nonempty-sphere-Reflexive-Globular-Type
    ( extension-sphere-Reflexive-Globular-Type x y S') =
      codiagonal _ ( reflexive-globular-type-sphere-Reflexive-Globular-Type S')
```

### The type of (n+1)-cells with boundary S

**Comment.** The type of 0-cells of the globular type constructed from S above.

```agda
module _ where

  higher-cell-sphere-Reflexive-Globular-Type :
    {l : Level} {n : ℕ} {G : Reflexive-Globular-Type l l }
    (S : sphere-Reflexive-Globular-Type G n) → UU l
  higher-cell-sphere-Reflexive-Globular-Type {l} {n} {G} S =
    0-cell-Reflexive-Globular-Type
      ( reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type
        {l} {n} {G} S)
```

### The type of globular subtypes of a reflexive globular type G

**Comment.** We call a globular type H a globular subtype of G if it arizes as
the type of cells of G with boundary S for some gloublar sphere S in G.

```agda
module _ where

  n-subtype-Reflexive-Globular-Type : {l1 l2 : Level}
    (G : Reflexive-Globular-Type l1 l2) → (n : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
  n-subtype-Reflexive-Globular-Type {l1} {l2} G n = im
    ( reflexive-globular-type-sphere-Reflexive-Globular-Type {l1} {l2} {n} {G})  

  subtype-Reflexive-Globular-Type : {l1 l2 : Level}
    (G : Reflexive-Globular-Type l1 l2) → UU (lsuc (lsuc l1) ⊔ lsuc (lsuc l2))
  subtype-Reflexive-Globular-Type G = im ( n-subtype-Reflexive-Globular-Type G)

  n-proper-subtype-Reflexive-Globular-Type : {l1 l2 : Level}
    (G : Reflexive-Globular-Type l1 l2) → (n : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
  n-proper-subtype-Reflexive-Globular-Type {l1} {l2} G n = im
    ( reflexive-globular-type-nonempty-sphere-Reflexive-Globular-Type
      {l1} {l2} {n} {G})  

  proper-subtype-Reflexive-Globular-Type : {l1 l2 : Level}
    (G : Reflexive-Globular-Type l1 l2) → UU (lsuc (lsuc l1) ⊔ lsuc (lsuc l2))
  proper-subtype-Reflexive-Globular-Type G = im
    ( n-proper-subtype-Reflexive-Globular-Type G)
```

### Suspensions of globular spheres

**Comment.** Given a globular sphere S in G of dimension n, and two (n+1)-cells
x and y whose boundary is S, we can form the suspension of S using x and y as
the poles.

```agda
module _ where

  suspension-sphere-Reflexive-Globular-Type :
    {l : Level} {G : Reflexive-Globular-Type l l} {n : ℕ}
    (S : sphere-Reflexive-Globular-Type G n) →
    (f g : 0-cell-Reflexive-Globular-Type
      ( reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type S)) →
    sphere-Reflexive-Globular-Type G (succ-ℕ n)
  suspension-sphere-Reflexive-Globular-Type
    {n = zero-ℕ} empty-sphere-Reflexive-Globular-Type f g =
      extension-sphere-Reflexive-Globular-Type f g
      empty-sphere-Reflexive-Globular-Type
  suspension-sphere-Reflexive-Globular-Type
    {n = succ-ℕ n} (extension-sphere-Reflexive-Globular-Type x y S) f g =
      extension-sphere-Reflexive-Globular-Type x y
        (suspension-sphere-Reflexive-Globular-Type S f g)

  desuspension-sphere-Reflexive-Globular-Type :
    {l : Level} {G : Reflexive-Globular-Type l l} {n : ℕ}
    (S : sphere-Reflexive-Globular-Type G (succ-ℕ n)) →
    sphere-Reflexive-Globular-Type G n
  desuspension-sphere-Reflexive-Globular-Type
    ( extension-sphere-Reflexive-Globular-Type x y
      empty-sphere-Reflexive-Globular-Type) =
        empty-sphere-Reflexive-Globular-Type
  desuspension-sphere-Reflexive-Globular-Type
    ( extension-sphere-Reflexive-Globular-Type x y
      ( extension-sphere-Reflexive-Globular-Type f g S)) =
        extension-sphere-Reflexive-Globular-Type x y
          ( desuspension-sphere-Reflexive-Globular-Type
            ( extension-sphere-Reflexive-Globular-Type f g S))
```

**Comment.** Given a globular sphere S of dimension n and two (n+1)-cells x and
y with boundary S, a 1-cell x→y in the globular type of cells with boundary S
determines a 0-cell in the type of cells with boundary Σ(S,x,y).
```agda
module _ where

  0-cell-suspension-1-cell-sphere-Reflexive-Globular-Type :
    {l : Level} {n : ℕ} →
    {G : Reflexive-Globular-Type l l} →
    (S : sphere-Reflexive-Globular-Type G n) →
    (x y : higher-cell-sphere-Reflexive-Globular-Type S) →
    (1-cell-Reflexive-Globular-Type
      ( reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type S)
      x y) → 
    higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S x y)
  0-cell-suspension-1-cell-sphere-Reflexive-Globular-Type
    {n = zero-ℕ} empty-sphere-Reflexive-Globular-Type x y f = f
  0-cell-suspension-1-cell-sphere-Reflexive-Globular-Type
    {n = succ-ℕ n} (extension-sphere-Reflexive-Globular-Type a b S) x y f =
      0-cell-suspension-1-cell-sphere-Reflexive-Globular-Type S x y f

  1-cell-sphere-0-cell-suspension-Reflexive-Globular-Type :
    {l : Level} {n : ℕ} →
    {G : Reflexive-Globular-Type l l} →
    (S : sphere-Reflexive-Globular-Type G n) →
    (x y : higher-cell-sphere-Reflexive-Globular-Type S) →
    higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S x y) →
    (1-cell-Reflexive-Globular-Type
      ( reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type S) x y)
  1-cell-sphere-0-cell-suspension-Reflexive-Globular-Type
    {n = zero-ℕ} empty-sphere-Reflexive-Globular-Type x y f = f
  1-cell-sphere-0-cell-suspension-Reflexive-Globular-Type
    {n = succ-ℕ n} (extension-sphere-Reflexive-Globular-Type a b S) x y f =
      1-cell-sphere-0-cell-suspension-Reflexive-Globular-Type S x y f
```

### Nonempty globular spheres are determined solely by their top-dimension data

**Comment.** I.e. if we have a sphere S = (x,y) ∷ S' in G, and we denote |S| the
globular type of cells with boundary S, we have a globular equivalence |S|≅|S'|.

```agda
module _ where

  invariance-reflexive-globular-type-sphere-Reflexive-Globular-Type :
    {l : Level} {G : Reflexive-Globular-Type l l} {n : ℕ} 
    (S : sphere-Reflexive-Globular-Type G (succ-ℕ n)) →
    reflexive-globular-equiv 
      ( reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type S)
      ( reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type
        ( sphere-higher-cells-sphere-Reflexive-Gloublar-Type S))
  invariance-reflexive-globular-type-sphere-Reflexive-Globular-Type
    ( extension-sphere-Reflexive-Globular-Type x y S) =
      id-reflexive-globular-equiv _
```

### Reflexivity terms of suspensions

**Comment.** For every globular sphere S and every cell x with boundary S,
we obtain a 0-cell refl(x) in |Σ(S,x,x)|.

```agda
module _ where

  refl-1-cell-sphere-Reflexive-Globular-Type :
    {l : Level} {G : Reflexive-Globular-Type l l} {n : ℕ}
    (S : sphere-Reflexive-Globular-Type G n) →
    (f : higher-cell-sphere-Reflexive-Globular-Type S) →
    1-cell-Reflexive-Globular-Type
      ( reflexive-globular-type-one-level-sphere-Reflexive-Globular-Type S) f f
  refl-1-cell-sphere-Reflexive-Globular-Type
    {G = G} empty-sphere-Reflexive-Globular-Type x =
      refl-1-cell-Reflexive-Globular-Type G {x}
  refl-1-cell-sphere-Reflexive-Globular-Type
    ( extension-sphere-Reflexive-Globular-Type x y S) f =
      refl-1-cell-sphere-Reflexive-Globular-Type S f

  refl-sphere-Reflexive-Globular-Type : 
    {l : Level} {G : Reflexive-Globular-Type l l} {n : ℕ}
    (S : sphere-Reflexive-Globular-Type G n) →
    (x : higher-cell-sphere-Reflexive-Globular-Type S) →
    higher-cell-sphere-Reflexive-Globular-Type
      ( sphere-higher-cells-sphere-Reflexive-Gloublar-Type
        ( suspension-sphere-Reflexive-Globular-Type S x x))
  refl-sphere-Reflexive-Globular-Type S x = 
    0-cell-reflexive-globular-equiv
      ( invariance-reflexive-globular-type-sphere-Reflexive-Globular-Type
        ( suspension-sphere-Reflexive-Globular-Type S x x))
      ( 0-cell-suspension-1-cell-sphere-Reflexive-Globular-Type S x x
        ( refl-1-cell-sphere-Reflexive-Globular-Type S x))


  refl-sphere-Reflexive-Globular-Type' : 
    {l : Level} {G : Reflexive-Globular-Type l l} {n : ℕ}
    (S : sphere-Reflexive-Globular-Type G n) →
    (x : higher-cell-sphere-Reflexive-Globular-Type S) →
    higher-cell-sphere-Reflexive-Globular-Type
      ( suspension-sphere-Reflexive-Globular-Type S x x)
  refl-sphere-Reflexive-Globular-Type' S x = 
    0-cell-suspension-1-cell-sphere-Reflexive-Globular-Type S x x
      ( refl-1-cell-sphere-Reflexive-Globular-Type S x)
 
```