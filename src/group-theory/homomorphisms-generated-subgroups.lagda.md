# Homomorphisms of generated subgroups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.homomorphisms-generated-subgroups where

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (_↪_; is-emb; map-emb; comp-emb)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using (is-equiv-has-inverse; emb-equiv)
open import foundation.function-extensionality using (eq-htpy; htpy-eq)
open import foundation.identity-types using (Id; refl; ap; _∙_; inv)
open import foundation.propositions using (eq-is-prop)
open import foundation.propositional-truncations using
  ( unit-trunc-Prop; apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop)
open import foundation.sets using (Id-Prop)
open import foundation.subtypes using (type-subtype)
open import foundation.truncated-types using (is-trunc-Π)
open import foundation.truncation-levels using (zero-𝕋)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.epimorphisms-groups using (is-epi-iso-Group)
open import group-theory.groups using
  ( Group; type-Group; right-unit-law-Group; is-set-type-Group; set-Group;
    unit-Group; mul-Group; inv-Group)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group; map-hom-Group; is-set-type-hom-Group; eq-htpy-hom-Group;
    preserves-unit-hom-Group; preserves-mul-hom-Group; preserves-inverses-hom-Group;
    comp-hom-Group)
open import group-theory.isomorphisms-groups using
  ( inv-iso-Group; hom-iso-Group; hom-inv-iso-Group)
open import group-theory.subgroups using
  ( subset-Group; group-Subgroup; isomorph-inclusion-complete-subgroup-Subgroup)
open import group-theory.subgroups-generated-by-subsets-groups using
  ( subgroup-subset-Group; ev-formal-combination-subset-Group; formal-combination-subset-Group;
    preserves-concat-ev-formal-combination-subset-Group; is-generating-subset-Group)

open import univalent-combinatorics.lists using
  ( list; nil; cons; in-list; fold-list)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

A group homomorphism from a subgroup generated by a subset `S` is defined by its values on `S`.

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (S : subset-Group l2 G) (G' : Group l3) 
  where

  distributivity-hom-group-ev-formal-combination :
    ( f : type-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G') →
    ( l : formal-combination-subset-Group G S) →
    Id
      ( map-hom-Group
        ( group-Subgroup G (subgroup-subset-Group G S))
        ( G')
        ( f)
        ( pair (ev-formal-combination-subset-Group G S l) (unit-trunc-Prop (pair l refl))))
      ( fold-list
        ( unit-Group G')
        ( λ (pair s x) →
          mul-Group
            ( G')
            ( map-hom-Group
              ( group-Subgroup G (subgroup-subset-Group G S))
              ( G')
              ( f)
              ( pair
                ( ev-formal-combination-subset-Group G S (in-list (pair s x)))
                ( unit-trunc-Prop (pair (in-list (pair s x)) refl)))))
        ( l))
  distributivity-hom-group-ev-formal-combination f nil =
    preserves-unit-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' f
  distributivity-hom-group-ev-formal-combination f (cons (pair s x) l) =
    ( ap
      ( map-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' f)
      ( eq-pair-Σ
        ( preserves-concat-ev-formal-combination-subset-Group G S
          ( in-list (pair s x))
          ( l))
        ( eq-is-prop is-prop-type-trunc-Prop))) ∙
      ( ( preserves-mul-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' f
        ( pair
          ( ev-formal-combination-subset-Group G S (in-list (pair s x)))
          ( unit-trunc-Prop (pair (in-list (pair s x)) refl)))
        ( pair (ev-formal-combination-subset-Group G S l) (unit-trunc-Prop (pair l refl)))) ∙
        ( ap
          ( mul-Group G'
            ( map-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' f
              ( pair
                ( ev-formal-combination-subset-Group G S (in-list (pair s x)))
                ( unit-trunc-Prop (pair (in-list (pair s x)) refl)))))
          ( distributivity-hom-group-ev-formal-combination f l)))

  map-restriction-generating-subset-Subgroup : 
    type-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' →
    type-subtype S → type-Group G'
  map-restriction-generating-subset-Subgroup f x =
    map-hom-Group
      ( group-Subgroup G (subgroup-subset-Group G S))
      ( G')
      ( f)
      ( pair
        ( ev-formal-combination-subset-Group G S (in-list (pair (inr star) x)))
        ( unit-trunc-Prop
          ( pair (in-list (pair (inr star) x)) refl)))

  is-emb-map-restriction-generating-subset-Subgroup : 
    is-emb (map-restriction-generating-subset-Subgroup)
  is-emb-map-restriction-generating-subset-Subgroup f g =
    is-equiv-has-inverse
      ( λ P →
        eq-htpy-hom-Group
          ( group-Subgroup G (subgroup-subset-Group G S))
          ( G')
          ( λ x →
            apply-universal-property-trunc-Prop
              ( pr2 x)
              ( Id-Prop
                ( set-Group G')
                ( map-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' f x)
                ( map-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' g x))
              ( λ (pair y Q) →
                ( ap
                  ( map-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' f)
                  ( eq-pair-Σ (inv Q) (eq-is-prop is-prop-type-trunc-Prop))) ∙
                  ( ( distributivity-hom-group-ev-formal-combination f y) ∙
                    ( ( ap
                      ( λ F → fold-list (unit-Group G') (λ Y → mul-Group G' (F Y)) y)
                      { x =
                        λ z →
                          ( map-hom-Group
                            ( group-Subgroup G (subgroup-subset-Group G S))
                            ( G')
                            ( f)
                            ( pair
                              ( ev-formal-combination-subset-Group G S (in-list z))
                              ( unit-trunc-Prop (pair (in-list z) refl))))}
                      { y =
                        λ z →
                          ( map-hom-Group
                            ( group-Subgroup G (subgroup-subset-Group G S))
                            ( G')
                            ( g)
                            ( pair
                              ( ev-formal-combination-subset-Group G S (in-list z))
                              ( unit-trunc-Prop (pair (in-list z) refl))))}
                      ( eq-htpy (lemma (htpy-eq P)))) ∙
                      ( ( inv
                        ( distributivity-hom-group-ev-formal-combination g y)) ∙
                        ( ap
                          ( map-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' g)
                          ( eq-pair-Σ Q (eq-is-prop is-prop-type-trunc-Prop)))))))))
      ( λ p →
        eq-is-prop
          ( is-trunc-Π
            ( zero-𝕋)
            ( λ z → is-set-type-Group G')
            ( λ S → map-restriction-generating-subset-Subgroup f S)
            ( λ S → map-restriction-generating-subset-Subgroup g S)))
      ( λ p →
        eq-is-prop
          ( is-set-type-hom-Group
            ( group-Subgroup G (subgroup-subset-Group G S))
            ( G')
            ( f)
            ( g)))
    where
    lemma :
      ( (x : type-subtype S) →
        Id
          ( map-hom-Group
            ( group-Subgroup G (subgroup-subset-Group G S))
            ( G')
            ( f)
            ( pair
              ( ev-formal-combination-subset-Group G S (in-list (pair (inr star) x)))
              ( unit-trunc-Prop (pair (in-list (pair (inr star) x)) refl))))
          ( map-hom-Group
            ( group-Subgroup G (subgroup-subset-Group G S))
            ( G')
            ( g)
            ( pair
              ( ev-formal-combination-subset-Group G S (in-list (pair (inr star) x)))
              ( unit-trunc-Prop (pair (in-list (pair (inr star) x)) refl))))) →
      ( z : Fin 2 × type-subtype S) →
      Id
        ( map-hom-Group
          ( group-Subgroup G (subgroup-subset-Group G S))
          ( G')
          ( f)
          ( pair
            ( ev-formal-combination-subset-Group G S (in-list z))
            ( unit-trunc-Prop (pair (in-list z) refl))))
        ( map-hom-Group
          ( group-Subgroup G (subgroup-subset-Group G S))
          ( G')
          ( g)
          ( pair
            ( ev-formal-combination-subset-Group G S (in-list z))
            ( unit-trunc-Prop (pair (in-list z) refl))))
    lemma P (pair (inl (inr star)) (pair x s)) =
      ( ap
        ( map-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' f)
        ( eq-pair-Σ (right-unit-law-Group G (inv-Group G x)) (eq-is-prop is-prop-type-trunc-Prop))) ∙
        ( preserves-inverses-hom-Group
          ( group-Subgroup G (subgroup-subset-Group G S))
          ( G')
          ( f)
          ( pair x (unit-trunc-Prop (pair (in-list (pair (inr star) (pair x s))) (right-unit-law-Group G x)))) ∙
          ( (ap
            ( inv-Group G')
            ( ( ap
              ( map-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' f)
              ( eq-pair-Σ (inv (right-unit-law-Group G x)) (eq-is-prop is-prop-type-trunc-Prop))) ∙
              ( ( P (pair x s)) ∙
                ( ap
                  ( map-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' g)
                  ( eq-pair-Σ (right-unit-law-Group G x) (eq-is-prop is-prop-type-trunc-Prop)))))) ∙
            ( ( inv
              ( preserves-inverses-hom-Group
                ( group-Subgroup G (subgroup-subset-Group G S))
                ( G')
                ( g)
                ( pair x (unit-trunc-Prop (pair (in-list (pair (inr star) (pair x s))) (right-unit-law-Group G x)))))) ∙
                ( ap
                  ( map-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' g)
                  ( eq-pair-Σ (inv (right-unit-law-Group G (inv-Group G x))) (eq-is-prop is-prop-type-trunc-Prop))))))
    lemma P (pair (inr star) x) = P x

  restriction-generating-subset-Subgroup : 
    type-hom-Group (group-Subgroup G (subgroup-subset-Group G S)) G' ↪
      ( type-subtype S → type-Group G')
  pr1 restriction-generating-subset-Subgroup = map-restriction-generating-subset-Subgroup
  pr2 restriction-generating-subset-Subgroup = is-emb-map-restriction-generating-subset-Subgroup

module _
  {l1 l2 l3 : Level} (G : Group l1) (S : subset-Group l2 G) (H : is-generating-subset-Group G S)
  (G' : Group l3) 
  where

  restriction-generating-subset-Group : 
    type-hom-Group G G' ↪ (type-subtype S → type-Group G')
  restriction-generating-subset-Group =
    comp-emb
      ( restriction-generating-subset-Subgroup G S G')
      ( pair
        ( λ f →
          comp-hom-Group
            ( group-Subgroup G (subgroup-subset-Group G S))
            ( G)
            ( G')
            ( f)
            ( pair pr1 (λ x y → refl)))
        ( is-epi-iso-Group l3
          ( group-Subgroup G (subgroup-subset-Group G S))
          ( G)
          ( inv-iso-Group
            ( G)
            ( group-Subgroup G (subgroup-subset-Group G S))
            ( isomorph-inclusion-complete-subgroup-Subgroup G (subgroup-subset-Group G S) H))
          ( G')))

  eq-map-restriction-generating-subset-Group :
    ( f : type-hom-Group G G') (x : type-subtype S) →
    Id
      ( map-emb restriction-generating-subset-Group f x)
      ( map-hom-Group G G' f (pr1 x))
  eq-map-restriction-generating-subset-Group f x =
    ap
      ( map-hom-Group G G' f)
      ( right-unit-law-Group G (pr1 x))
```