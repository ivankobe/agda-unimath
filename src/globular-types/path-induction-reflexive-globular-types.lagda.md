# Path induction for reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.path-induction-reflexive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import elementary-number-theory.natural-numbers

open import globular-types.reflexive-globular-types
open import globular-types.subtypes-reflexive-globular-types
```

```agda
module _
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2)
  where

  dependent-family-Reflexive-Globular-Type :
    {C D : 0-cell-Reflexive-Globular-Type G} {n : ℕ}
    (f : 0-cell-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G C D)) →
    UU (lsuc l1 ⊔ lsuc l2)
  dependent-family-Reflexive-Globular-Type {C} {D} {n} f =
    (g : 0-cell-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G C D)) →
    (α : nat-iso-Synthetic-Category-Theory f g) →
    Proper-Context-Reflexive-Globular-Type
      l1 l2 logos-Synthetic-Category-Theory n
```