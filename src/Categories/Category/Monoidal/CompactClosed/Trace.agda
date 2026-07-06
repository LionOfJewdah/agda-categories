{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Category.Monoidal.CompactClosed.Trace
  {o ℓ e} {C : Category o ℓ e}
  (M : Monoidal C) where

open import Categories.Category.Monoidal.CompactClosed M using (CompactClosed)
open import Categories.Category.Monoidal.Traced M using (Traced)
import Categories.Category.Monoidal.CompactClosed.Trace.Definition as Definition
import Categories.Category.Monoidal.CompactClosed.Trace.Construction as Construction
import Categories.Category.Monoidal.CompactClosed.Trace.Vanishing as Vanishing

open CompactClosed

traced : CompactClosed → Traced
traced K = record
  { symmetric    = symmetric K
  ; trace        = Definition.trace M (symmetric K) (leftRigid K)
  ; trace-resp-≈ = Definition.trace-resp-≈ M (symmetric K) (leftRigid K)
  ; slide        = Definition.trace-slide M (symmetric K) (leftRigid K)
  ; tightenₗ     = Definition.trace-tightenₗ M (symmetric K) (leftRigid K)
  ; tightenᵣ     = Definition.trace-tightenᵣ M (symmetric K) (leftRigid K)
  ; vanishing₁   = Construction.vanishing₁ M (symmetric K) (leftRigid K)
  ; vanishing₂   = Vanishing.vanishing₂ M (symmetric K) (leftRigid K)
  ; superposing  = Construction.superposing M (symmetric K) (leftRigid K)
  ; yanking      = Construction.yanking M (symmetric K) (leftRigid K)
  }
