{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

module Categories.Category.Monoidal.CompactClosed.Properties
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) where

open import Data.Sum using (inj₁)

open import Categories.Category.Monoidal.CompactClosed M using (CompactClosed)
open import Categories.Category.Monoidal.Properties M using (monoidal-Op)
open import Categories.Category.Monoidal.Rigid.Properties M using (rigidʳ-Op)
open import Categories.Category.Monoidal.Symmetric.Properties using (symmetric-Op)
import Categories.Category.Monoidal.CompactClosed monoidal-Op as OpCompactClosed

open CompactClosed

compactClosed-Op : CompactClosed → OpCompactClosed.CompactClosed
compactClosed-Op K = record
  { symmetric = symmetric-Op (symmetric K)
  ; rigid = inj₁ (rigidʳ-Op (rightRigid K))
  }
