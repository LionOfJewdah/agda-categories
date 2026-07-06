{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Tactic.Monoidal.Symmetric.Examples
  {o ℓ e : Level}
  {C : Category o ℓ e}
  {M : Monoidal C}
  (S : Symmetric M)
  (X Y Z : Category.Obj C)
  where

open import Data.Fin.Base using (Fin)
open import Data.Fin.Patterns using (0F; 1F; 2F)

open Category C using (_≈_)
open import Categories.Tactic.Monoidal.Symmetric using (module Finite)
open Finite S

private
  atom : Fin 3 → Category.Obj C
  atom 0F = X
  atom 1F = Y
  atom 2F = Z

  open SolverFor atom renaming (solveᶠ to solve)

  double-braid : (‹ 0F › ⊗ᵒ ‹ 1F ›) ⇒ᶠ (‹ 0F › ⊗ᵒ ‹ 1F ›)
  double-braid = σᶠ ∘ᶠ σᶠ

  block-braid : ((‹ 0F › ⊗ᵒ ‹ 1F ›) ⊗ᵒ ‹ 2F ›) ⇒ᶠ (‹ 2F › ⊗ᵒ (‹ 0F › ⊗ᵒ ‹ 1F ›))
  block-braid = σᶠ

  block-stepwise : ((‹ 0F › ⊗ᵒ ‹ 1F ›) ⊗ᵒ ‹ 2F ›) ⇒ᶠ (‹ 2F › ⊗ᵒ (‹ 0F › ⊗ᵒ ‹ 1F ›))
  block-stepwise = α⇒ᶠ ∘ᶠ (σᶠ ⊗ᶠ idₘ) ∘ᶠ α⇐ᶠ ∘ᶠ (idₘ ⊗ᶠ σᶠ) ∘ᶠ α⇒ᶠ

  unit-braid : (‹ 0F › ⊗ᵒ I) ⇒ᶠ (I ⊗ᵒ ‹ 0F ›)
  unit-braid = σᶠ

  unit-swap : (‹ 0F › ⊗ᵒ I) ⇒ᶠ (I ⊗ᵒ ‹ 0F ›)
  unit-swap = λ⇐ᶠ ∘ᶠ ρ⇒ᶠ

  braid-braid : ⟦ double-braid ⟧ᵇ ≈ ⟦ idₘ {‹ 0F › ⊗ᵒ ‹ 1F ›} ⟧ᵇ
  braid-braid = solve double-braid idₘ

  braid-block : ⟦ block-braid ⟧ᵇ ≈ ⟦ block-stepwise ⟧ᵇ
  braid-block = solve block-braid block-stepwise

  braid-unit : ⟦ unit-braid ⟧ᵇ ≈ ⟦ unit-swap ⟧ᵇ
  braid-unit = solve unit-braid unit-swap
