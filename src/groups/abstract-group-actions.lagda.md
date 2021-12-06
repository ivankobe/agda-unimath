---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.abstract-group-actions where

open import groups.abstract-groups public

module _
  {l1 : Level} (G : Group l1)
  where

  Abstract-Group-Action : (l : Level) → UU (l1 ⊔ lsuc l)
  Abstract-Group-Action l =
    Σ (UU-Set l) (λ X → hom-Group G (symmetric-Group X))

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  set-Abstract-Group-Action : UU-Set l2
  set-Abstract-Group-Action = pr1 X

  type-Abstract-Group-Action : UU l2
  type-Abstract-Group-Action = type-Set set-Abstract-Group-Action

  is-set-type-Abstract-Group-Action : is-set type-Abstract-Group-Action
  is-set-type-Abstract-Group-Action = is-set-type-Set set-Abstract-Group-Action
  
  equiv-mul-Abstract-Group-Action :
    type-Group G → type-Abstract-Group-Action ≃ type-Abstract-Group-Action
  equiv-mul-Abstract-Group-Action =
    map-hom-Group G (symmetric-Group set-Abstract-Group-Action) (pr2 X)

  mul-Abstract-Group-Action :
    type-Group G → type-Abstract-Group-Action → type-Abstract-Group-Action
  mul-Abstract-Group-Action g =
    map-equiv (equiv-mul-Abstract-Group-Action g)

  preserves-unit-mul-Abstract-Group-Action :
    (mul-Abstract-Group-Action (unit-Group G)) ~ id
  preserves-unit-mul-Abstract-Group-Action =
    htpy-eq
      ( ap pr1
        ( preserves-unit-hom-Group G
          ( symmetric-Group set-Abstract-Group-Action)
          ( pr2 X)))

  preserves-mul-Abstract-Group-Action :
    (g : type-Group G) (h : type-Group G) (x : type-Abstract-Group-Action) →
    Id ( mul-Abstract-Group-Action (mul-Group G g h) x)
       ( mul-Abstract-Group-Action g (mul-Abstract-Group-Action h x))
  preserves-mul-Abstract-Group-Action g h =
    htpy-eq
      ( ap pr1
        ( preserves-mul-hom-Group G
          ( symmetric-Group set-Abstract-Group-Action) (pr2 X) g h))

module _
  {l1 : Level} (G : Group l1)
  where
  
  principal-Abstract-Group-Action : Abstract-Group-Action G l1
  pr1 principal-Abstract-Group-Action = set-Group G
  pr1 (pr2 principal-Abstract-Group-Action) g = equiv-mul-Group G g
  pr2 (pr2 principal-Abstract-Group-Action) g h =
    eq-htpy-equiv (is-associative-mul-Group G g h)
  
  conjugation-Abstract-Group-Action : Abstract-Group-Action G l1
  pr1 conjugation-Abstract-Group-Action = set-Group G
  pr1 (pr2 conjugation-Abstract-Group-Action) g = equiv-conjugation-Group G g
  pr2 (pr2 conjugation-Abstract-Group-Action) g h =
    eq-htpy-equiv
      ( λ x →
        ( ap-mul-Group G
          ( is-associative-mul-Group G g h x)
          ( distributive-inv-mul-Group G g h)) ∙
        ( ( inv
            ( is-associative-mul-Group G
              ( mul-Group G g (mul-Group G h x))
              ( inv-Group G h)
              ( inv-Group G g))) ∙
          ( ap
            ( mul-Group' G (inv-Group G g))
            ( is-associative-mul-Group G g
              ( mul-Group G h x)
              ( inv-Group G h)))))

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  hom-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  hom-Abstract-Group-Action =
    Σ ( type-Set (pr1 X) → type-Set (pr1 Y))
      ( λ f →
        ( g : type-Group G) →
        ( f ∘ mul-Abstract-Group-Action G X g) ~
        ( mul-Abstract-Group-Action G Y g ∘ f))

  equiv-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  equiv-Abstract-Group-Action =
    Σ ( type-Set (pr1 X) ≃ type-Set (pr1 Y))
      ( λ e →
        ( g : type-Group G) →
        htpy-equiv
          ( e ∘e equiv-mul-Abstract-Group-Action G X g)
          ( equiv-mul-Abstract-Group-Action G Y g ∘e e))

  hom-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action → hom-Abstract-Group-Action
  hom-equiv-Abstract-Group-Action (pair e H) = pair (map-equiv e) H

  mere-equiv-Abstract-Group-Action-Prop : UU-Prop (l1 ⊔ l2 ⊔ l3)
  mere-equiv-Abstract-Group-Action-Prop =
    trunc-Prop equiv-Abstract-Group-Action

  mere-equiv-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  mere-equiv-Abstract-Group-Action =
    type-Prop mere-equiv-Abstract-Group-Action-Prop

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3) (f : hom-Abstract-Group-Action G X Y)
  where

  htpy-hom-Abstract-Group-Action :
    (g : hom-Abstract-Group-Action G X Y) → UU (l2 ⊔ l3)
  htpy-hom-Abstract-Group-Action g = pr1 f ~ pr1 g

  refl-htpy-hom-Abstract-Group-Action : htpy-hom-Abstract-Group-Action f
  refl-htpy-hom-Abstract-Group-Action = refl-htpy

  htpy-eq-hom-Abstract-Group-Action :
    (g : hom-Abstract-Group-Action G X Y) →
    Id f g → htpy-hom-Abstract-Group-Action g
  htpy-eq-hom-Abstract-Group-Action .f refl =
    refl-htpy-hom-Abstract-Group-Action

  is-contr-total-htpy-hom-Abstract-Group-Action :
    is-contr
      ( Σ ( hom-Abstract-Group-Action G X Y)
          ( htpy-hom-Abstract-Group-Action))
  is-contr-total-htpy-hom-Abstract-Group-Action =
    is-contr-total-Eq-substructure
      ( is-contr-total-htpy (pr1 f))
      ( λ g →
        is-prop-Π
          ( λ x →
            is-prop-Π
              ( λ y →
                is-set-type-Set
                  ( set-Abstract-Group-Action G Y)
                  ( g (mul-Abstract-Group-Action G X x y))
                  ( mul-Abstract-Group-Action G Y x (g y)))))
      ( pr1 f)
      ( refl-htpy)
      ( pr2 f)

  is-equiv-htpy-eq-hom-Abstract-Group-Action :
    (g : hom-Abstract-Group-Action G X Y) →
    is-equiv (htpy-eq-hom-Abstract-Group-Action g)
  is-equiv-htpy-eq-hom-Abstract-Group-Action =
    fundamental-theorem-id f
      refl-htpy-hom-Abstract-Group-Action
      is-contr-total-htpy-hom-Abstract-Group-Action
      htpy-eq-hom-Abstract-Group-Action

  extensionality-hom-Abstract-Group-Action :
    (g : hom-Abstract-Group-Action G X Y) →
    Id f g ≃ htpy-hom-Abstract-Group-Action g
  pr1 (extensionality-hom-Abstract-Group-Action g) =
    htpy-eq-hom-Abstract-Group-Action g
  pr2 (extensionality-hom-Abstract-Group-Action g) =
    is-equiv-htpy-eq-hom-Abstract-Group-Action g

  eq-htpy-hom-Abstract-Group-Action :
    (g : hom-Abstract-Group-Action G X Y) →
    htpy-hom-Abstract-Group-Action g → Id f g
  eq-htpy-hom-Abstract-Group-Action g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-Abstract-Group-Action g)

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3) (e : equiv-Abstract-Group-Action G X Y)
  where
  
  htpy-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) → UU (l2 ⊔ l3)
  htpy-equiv-Abstract-Group-Action f =
    htpy-hom-Abstract-Group-Action G X Y
      ( hom-equiv-Abstract-Group-Action G X Y e)
      ( hom-equiv-Abstract-Group-Action G X Y f)

  refl-htpy-equiv-Abstract-Group-Action : htpy-equiv-Abstract-Group-Action e
  refl-htpy-equiv-Abstract-Group-Action =
    refl-htpy-hom-Abstract-Group-Action G X Y
      ( hom-equiv-Abstract-Group-Action G X Y e)

  htpy-eq-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id e f → htpy-equiv-Abstract-Group-Action f
  htpy-eq-equiv-Abstract-Group-Action .e refl =
    refl-htpy-equiv-Abstract-Group-Action 

  is-contr-total-htpy-equiv-Abstract-Group-Action :
    is-contr
      ( Σ ( equiv-Abstract-Group-Action G X Y)
          ( htpy-equiv-Abstract-Group-Action))
  is-contr-total-htpy-equiv-Abstract-Group-Action =
    is-contr-equiv
      ( Σ ( Σ ( hom-Abstract-Group-Action G X Y) (λ f → is-equiv (pr1 f)))
          ( λ f →
            htpy-hom-Abstract-Group-Action G X Y
              ( hom-equiv-Abstract-Group-Action G X Y e)
              ( pr1 f)))
      ( equiv-Σ
        ( λ f →
          htpy-hom-Abstract-Group-Action G X Y
            ( hom-equiv-Abstract-Group-Action G X Y e)
            ( pr1 f))
        ( equiv-right-swap-Σ)
        ( λ { (pair (pair f E) H) → equiv-id}))
      ( is-contr-total-Eq-substructure
        ( is-contr-total-htpy-hom-Abstract-Group-Action G X Y
          ( hom-equiv-Abstract-Group-Action G X Y e))
        ( λ f → is-subtype-is-equiv (pr1 f))
        ( hom-equiv-Abstract-Group-Action G X Y e)
        ( refl-htpy)
        ( is-equiv-map-equiv (pr1 e)))

  is-equiv-htpy-eq-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    is-equiv (htpy-eq-equiv-Abstract-Group-Action f)
  is-equiv-htpy-eq-equiv-Abstract-Group-Action =
    fundamental-theorem-id e
      refl-htpy-equiv-Abstract-Group-Action
      is-contr-total-htpy-equiv-Abstract-Group-Action
      htpy-eq-equiv-Abstract-Group-Action

  extensionality-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    Id e f ≃ htpy-equiv-Abstract-Group-Action f
  pr1 (extensionality-equiv-Abstract-Group-Action f) =
    htpy-eq-equiv-Abstract-Group-Action f
  pr2 (extensionality-equiv-Abstract-Group-Action f) =
    is-equiv-htpy-eq-equiv-Abstract-Group-Action f

  eq-htpy-equiv-Abstract-Group-Action :
    (f : equiv-Abstract-Group-Action G X Y) →
    htpy-equiv-Abstract-Group-Action f → Id e f
  eq-htpy-equiv-Abstract-Group-Action f =
    map-inv-is-equiv (is-equiv-htpy-eq-equiv-Abstract-Group-Action f)

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  inv-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action G X Y → equiv-Abstract-Group-Action G Y X
  pr1 (inv-equiv-Abstract-Group-Action (pair e H)) = inv-equiv e
  pr2 (inv-equiv-Abstract-Group-Action (pair e H)) g =
    coherence-square-inv-horizontal
      ( e)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( e)
      ( H g)

module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : Abstract-Group-Action G l2) (Y : Abstract-Group-Action G l3)
  (Z : Abstract-Group-Action G l4)
  where

  comp-equiv-Abstract-Group-Action :
    equiv-Abstract-Group-Action G Y Z → equiv-Abstract-Group-Action G X Y →
    equiv-Abstract-Group-Action G X Z
  pr1 (comp-equiv-Abstract-Group-Action (pair f K) (pair e H)) = f ∘e e
  pr2 (comp-equiv-Abstract-Group-Action (pair f K) (pair e H)) g =
    coherence-square-comp-horizontal
      ( map-equiv e)
      ( map-equiv f)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( mul-Abstract-Group-Action G Z g)
      ( map-equiv e)
      ( map-equiv f)
      ( H g)
      ( K g)

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  equiv-id-Abstract-Group-Action :
    equiv-Abstract-Group-Action G X X
  pr1 equiv-id-Abstract-Group-Action = equiv-id
  pr2 equiv-id-Abstract-Group-Action g = refl-htpy

  equiv-eq-Abstract-Group-Action :
    (Y : Abstract-Group-Action G l2) →
    Id X Y → equiv-Abstract-Group-Action G X Y
  equiv-eq-Abstract-Group-Action .X refl = equiv-id-Abstract-Group-Action

  abstract
    is-contr-total-equiv-Abstract-Group-Action :
      is-contr
        ( Σ ( Abstract-Group-Action G l2)
            ( equiv-Abstract-Group-Action G X))
    is-contr-total-equiv-Abstract-Group-Action =
      is-contr-total-Eq-structure
        ( λ Y ν e →
          (g : type-Group G) →
          htpy-equiv
            ( e ∘e map-hom-Group G (symmetric-Group (pr1 X)) (pr2 X) g)
            ( map-hom-Group G (symmetric-Group Y) ν g ∘e e))
        ( is-contr-total-equiv-Set (pr1 X))
        ( pair (pr1 X) equiv-id)
        ( is-contr-equiv
          ( Σ ( hom-Group G (symmetric-Group (pr1 X)))
              ( htpy-hom-Group G (symmetric-Group (pr1 X)) (pr2 X)))
          ( equiv-tot
            ( λ f →
              equiv-map-Π
                ( λ g →
                  inv-equiv
                    ( equiv-htpy-eq-equiv
                      ( map-hom-Group G (symmetric-Group (pr1 X)) (pr2 X) g)
                      ( map-hom-Group G (symmetric-Group (pr1 X)) f g)))))
          ( is-contr-total-htpy-hom-Group G
            ( symmetric-Group (pr1 X))
            ( pr2 X)))

  abstract
    is-equiv-equiv-eq-Abstract-Group-Action :
      (Y : Abstract-Group-Action G l2) →
      is-equiv (equiv-eq-Abstract-Group-Action Y)
    is-equiv-equiv-eq-Abstract-Group-Action =
      fundamental-theorem-id X
        equiv-id-Abstract-Group-Action
        is-contr-total-equiv-Abstract-Group-Action
        equiv-eq-Abstract-Group-Action

  eq-equiv-Abstract-Group-Action :
    (Y : Abstract-Group-Action G l2) →
    equiv-Abstract-Group-Action G X Y → Id X Y
  eq-equiv-Abstract-Group-Action Y =
    map-inv-is-equiv (is-equiv-equiv-eq-Abstract-Group-Action Y)

  extensionality-Abstract-Group-Action :
    (Y : Abstract-Group-Action G l2) →
    Id X Y ≃ equiv-Abstract-Group-Action G X Y
  pr1 (extensionality-Abstract-Group-Action Y) =
    equiv-eq-Abstract-Group-Action Y
  pr2 (extensionality-Abstract-Group-Action Y) =
    is-equiv-equiv-eq-Abstract-Group-Action Y

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  -- The following are the morphisms in a groupoid with objects type-Set X
  hom-orbit-Abstract-Group-Action :
    (x y : type-Abstract-Group-Action G X) → UU (l1 ⊔ l2)
  hom-orbit-Abstract-Group-Action x y =
    Σ (type-Group G) (λ g → Id (mul-Abstract-Group-Action G X g x) y)

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  -- The following defines the stabilizer subgroup of G
  type-stabilizer-Abstract-Group-Action :
    type-Abstract-Group-Action G X → UU (l1 ⊔ l2)
  type-stabilizer-Abstract-Group-Action x =
    Σ (type-Group G) (λ g → Id (mul-Abstract-Group-Action G X g x) x)

```