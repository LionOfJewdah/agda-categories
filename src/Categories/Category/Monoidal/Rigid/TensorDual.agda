{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)

module Categories.Category.Monoidal.Rigid.TensorDual
    {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) (R : LeftRigid M) where

open Category C
open Monoidal M
open LeftRigid R using (_⁻¹; η; ε; snake₁)
import Categories.Category.Monoidal.Utilities M as MonUtil
open import Categories.Category.Monoidal.Reasoning M
open TensorIdentity using (id⊗id; ⊗id-∘)
open import Categories.Morphism.Reasoning C
import Categories.Category.Monoidal.Properties M as MonoidalProps
open MonoidalProps using (coherence-inv₁)

open MonUtil.Shorthands
open MonoidalProps.Structural using (cap-reassoc; λ-left; ρ-sweep; pentagon′; α-sweep; α-unit)

private
  variable A K P Q X Y Z : Obj

  snake₁⊗id-merge : ∀ {X Z} →
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ ((η {X} ⊗₁ id) ⊗₁ id {Z}) ∘ (λ⇐ ⊗₁ id {Z})
    ≈ ((ρ⇒ ∘ (id ⊗₁ ε {X}) ∘ α⇒ ∘ (η {X} ⊗₁ id) ∘ λ⇐) ⊗₁ id {Z})
  snake₁⊗id-merge {X} {Z} = begin
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ ((η {X} ⊗₁ id) ⊗₁ id {Z}) ∘ (λ⇐ ⊗₁ id {Z})
      ≈⟨ assoc ⟩
    (ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}) ∘ (α⇒ ⊗₁ id {Z})
      ∘ ((η {X} ⊗₁ id) ⊗₁ id {Z}) ∘ (λ⇐ ⊗₁ id {Z})
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗id-∘ ⟩
    (ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z})
      ∘ (α⇒ ⊗₁ id {Z}) ∘ (((η {X} ⊗₁ id) ∘ λ⇐) ⊗₁ id {Z})
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗id-∘ ⟩
    (ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z})
      ∘ ((α⇒ ∘ (η {X} ⊗₁ id) ∘ λ⇐) ⊗₁ id {Z})
      ≈˘⟨ refl⟩∘⟨ ⊗id-∘ ⟩
    (ρ⇒ ⊗₁ id {Z}) ∘ (((id ⊗₁ ε {X}) ∘ α⇒ ∘ (η {X} ⊗₁ id) ∘ λ⇐) ⊗₁ id {Z})
      ≈˘⟨ ⊗id-∘ ⟩
    (ρ⇒ ∘ (id ⊗₁ ε {X}) ∘ α⇒ ∘ (η {X} ⊗₁ id) ∘ λ⇐) ⊗₁ id {Z} ∎

  η-merge : ∀ {Y K} {k : K ⇒ Y} → ((id {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ k) ∘ (η {Y} ⊗₁ id {K}) ≈ η {Y} ⊗₁ k
  η-merge {Y} {K} {k} = begin
    ((id {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ k) ∘ (η {Y} ⊗₁ id {K})
      ≈˘⟨ ⊗-distrib-over-∘ ⟩
    ((id {Y} ⊗₁ id {Y ⁻¹}) ∘ η {Y}) ⊗₁ (k ∘ id {K})
      ≈⟨ elimˡ id⊗id ⟩⊗⟨ identityʳ ⟩
    η {Y} ⊗₁ k ∎

  η-unit : ∀ {Y K} {k : K ⇒ Y} →
    (((η {Y} ⊗₁ id {Y}) ∘ (id {unit} ⊗₁ k)) ∘ λ⇐) ≈ (η {Y} ⊗₁ id {Y}) ∘ λ⇐ ∘ k
  η-unit {Y} {K} {k} = begin
    ((η {Y} ⊗₁ id {Y}) ∘ (id {unit} ⊗₁ k)) ∘ λ⇐
      ≈⟨ assoc ⟩
    (η {Y} ⊗₁ id {Y}) ∘ (id {unit} ⊗₁ k) ∘ λ⇐
      ≈˘⟨ refl⟩∘⟨ unitorˡ-commute-to {f = k} ⟩
    (η {Y} ⊗₁ id {Y}) ∘ λ⇐ ∘ k ∎

  expanded-cup : ∀ {Y P Q} → P ⊗₀ Q ⇒ Y ⊗₀ ((Y ⁻¹ ⊗₀ P) ⊗₀ Q)
  expanded-cup {Y} {P} {Q} =
    α⇒ {Y} {Y ⁻¹ ⊗₀ P} {Q} ∘
      ((α⇒ {Y} {Y ⁻¹} {P} ⊗₁ id {Q}) ∘ ((η {Y} ⊗₁ id {P}) ⊗₁ id {Q}) ∘ (λ⇐ ⊗₁ id {Q}))

  cupᵀ : ∀ {Y P Q} → P ⊗₀ Q ⇒ Y ⊗₀ (Y ⁻¹ ⊗₀ (P ⊗₀ Q))
  cupᵀ {Y} {P} {Q} = α⇒ {Y} {Y ⁻¹} {P ⊗₀ Q} ∘ (η {Y} ⊗₁ id {P ⊗₀ Q}) ∘ λ⇐

  capᵀ : ∀ {Y P Q} {k : P ⊗₀ Q ⇒ Y} → Y ⁻¹ ⊗₀ (P ⊗₀ Q) ⇒ unit
  capᵀ {Y} {k = k} = ε {Y} ∘ (id {Y ⁻¹} ⊗₁ k)

  snake₁⊗id-coherence : ∀ {X Z} →
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Z}
      ∘ (η {X} ⊗₁ id {X ⊗₀ Z}) ∘ λ⇐
    ≈ ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ ((η {X} ⊗₁ id {X}) ⊗₁ id {Z}) ∘ (λ⇐ ⊗₁ id {Z})
  snake₁⊗id-coherence {X} {Z} = begin
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Z}
      ∘ (η {X} ⊗₁ id {X ⊗₀ Z}) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩⊗⟨ ⟺ id⊗id) ⟩∘⟨refl) ⟩
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Z}
      ∘ (η {X} ⊗₁ (id {X} ⊗₁ id {Z})) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ assoc-commute-to ⟩
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ (((η {X} ⊗₁ id) ⊗₁ id {Z}) ∘ α⇐ {unit} {X} {Z}) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ ((η {X} ⊗₁ id) ⊗₁ id {Z}) ∘ α⇐ {unit} {X} {Z} ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₁ ⟩
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ ((η {X} ⊗₁ id {X}) ⊗₁ id {Z}) ∘ (λ⇐ ⊗₁ id {Z}) ∎

  snake₁⊗id : ∀ {X Z} →
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Z} ∘ (η {X} ⊗₁ id {X ⊗₀ Z}) ∘ λ⇐
    ≈ id {X ⊗₀ Z}
  snake₁⊗id {X} {Z} = begin
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Z}
      ∘ (η {X} ⊗₁ id {X ⊗₀ Z}) ∘ λ⇐
      ≈⟨ snake₁⊗id-coherence ⟩
    ((ρ⇒ ⊗₁ id {Z}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Z}))
      ∘ (α⇒ ⊗₁ id {Z}) ∘ ((η {X} ⊗₁ id {X}) ⊗₁ id {Z}) ∘ (λ⇐ ⊗₁ id {Z})
      ≈⟨ snake₁⊗id-merge ⟩
    (ρ⇒ ∘ (id ⊗₁ ε {X}) ∘ α⇒ ∘ (η {X} ⊗₁ id) ∘ λ⇐) ⊗₁ id {Z}
      ≈⟨ snake₁ {X} ⟩⊗⟨refl ⟩
    id ⊗₁ id {Z} ≈⟨ id⊗id ⟩
    id ∎

  cap-cup-context-step : ∀ {Y K} {k : K ⇒ Y} →
    (id {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ k)) ∘ α⇒ ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐
    ≈ α⇒ ∘ (((id {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ k) ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐)
  cap-cup-context-step {Y} {K} {k} = begin
    (id {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ k)) ∘ α⇒ ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐
      ≈⟨ sym-assoc ⟩
    ((id {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ k)) ∘ α⇒) ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐
      ≈⟨ ⟺ assoc-commute-from ⟩∘⟨refl ⟩
    (α⇒ ∘ ((id {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ k)) ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐
      ≈⟨ assoc ⟩
    α⇒ ∘ (((id {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ k) ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐) ∎

  cap-cup-context : ∀ {Y K} {k : K ⇒ Y} →
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ (id {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ k)) ∘ α⇒ ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐
    ≈ (ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ α⇒ ∘ (η {Y} ⊗₁ id {Y}) ∘ λ⇐) ∘ k
  cap-cup-context {Y} {K} {k} = begin
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ (id {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ k)) ∘ α⇒ ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cap-cup-context-step {Y} {K} {k} ⟩
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ α⇒
      ∘ (((id {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ k) ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ α⇒
      ∘ ((((id {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ k) ∘ (η {Y} ⊗₁ id {K})) ∘ λ⇐)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ η-merge ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ α⇒ ∘ ((η {Y} ⊗₁ k) ∘ λ⇐)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ serialize₁₂ ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ α⇒
      ∘ ((η {Y} ⊗₁ id {Y}) ∘ (id {unit} ⊗₁ k)) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ η-unit ⟩
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ α⇒ ∘ (η {Y} ⊗₁ id {Y}) ∘ λ⇐ ∘ k
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ α⇒ ∘ ((η {Y} ⊗₁ id {Y}) ∘ λ⇐) ∘ k
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ (α⇒ ∘ (η {Y} ⊗₁ id {Y}) ∘ λ⇐) ∘ k
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    ρ⇒ ∘ ((id {Y} ⊗₁ ε {Y}) ∘ α⇒ ∘ (η {Y} ⊗₁ id {Y}) ∘ λ⇐) ∘ k
      ≈⟨ sym-assoc ⟩
    (ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ α⇒ ∘ (η {Y} ⊗₁ id {Y}) ∘ λ⇐) ∘ k ∎

  cap-cup : ∀ {Y K} {k : K ⇒ Y} →
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ (id {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ k)) ∘ α⇒ ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐ ≈ k
  cap-cup {Y} {K} {k} = begin
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ (id {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ k)) ∘ α⇒ ∘ (η {Y} ⊗₁ id {K}) ∘ λ⇐
      ≈⟨ cap-cup-context {Y} {K} {k} ⟩
    (ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ α⇒ ∘ (η {Y} ⊗₁ id {Y}) ∘ λ⇐) ∘ k
      ≈⟨ snake₁ {Y} ⟩∘⟨refl ⟩
    id ∘ k ≈⟨ identityˡ ⟩
    k ∎

  cupᵀ-snake : ∀ {Y P Q} {k : P ⊗₀ Q ⇒ Y} →
    (ρ⇒ ∘ (id {Y} ⊗₁ capᵀ {Y} {P} {Q} {k})) ∘ cupᵀ {Y} {P} {Q} ≈ k
  cupᵀ-snake {Y} {P} {Q} {k} = begin
    (ρ⇒ ∘ (id {Y} ⊗₁ capᵀ {Y} {P} {Q} {k})) ∘ cupᵀ {Y} {P} {Q}
      ≈⟨ assoc ⟩
    ρ⇒ ∘ (id {Y} ⊗₁ capᵀ {Y} {P} {Q} {k}) ∘ cupᵀ {Y} {P} {Q}
      ≈⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
    ρ⇒ ∘ ((id {Y} ⊗₁ ε {Y}) ∘ (id {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ k))) ∘ cupᵀ {Y} {P} {Q}
      ≈⟨ refl⟩∘⟨ assoc ⟩
    ρ⇒ ∘ (id {Y} ⊗₁ ε {Y}) ∘ (id {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ k)) ∘ cupᵀ {Y} {P} {Q}
      ≈⟨ cap-cup {Y} {P ⊗₀ Q} {k} ⟩
    k ∎

module CupThreading where
  η-through-α : ∀ {P X Y} →
    α⇒ {P} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
      ∘ ((id {P} ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
      ∘ (ρ⇐ {P} ⊗₁ id {X ⁻¹})
    ≈ (id {P} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹}))
        ∘ α⇒ {P} {unit} {X ⁻¹}
        ∘ (ρ⇐ {P} ⊗₁ id {X ⁻¹})
  η-through-α {P} {X} {Y} = begin
    α⇒ {P} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
      ∘ ((id {P} ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
      ∘ (ρ⇐ {P} ⊗₁ id {X ⁻¹})
      ≈˘⟨ assoc ⟩
    (α⇒ {P} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
      ∘ ((id {P} ⊗₁ η {Y}) ⊗₁ id {X ⁻¹}))
      ∘ (ρ⇐ {P} ⊗₁ id {X ⁻¹})
      ≈⟨ assoc-commute-from {f = id {P}} {g = η {Y}} {h = id {X ⁻¹}} ⟩∘⟨refl ⟩
    ((id {P} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹}))
      ∘ α⇒ {P} {unit} {X ⁻¹})
      ∘ (ρ⇐ {P} ⊗₁ id {X ⁻¹})
      ≈⟨ assoc ⟩
    (id {P} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹}))
      ∘ α⇒ {P} {unit} {X ⁻¹}
      ∘ (ρ⇐ {P} ⊗₁ id {X ⁻¹}) ∎

  η-thread : ∀ {A X Y} →
    α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
      ∘ ((id ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
    ≈ (id {A ⊗₀ X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹}))
        ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
        ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
        ∘ (id ⊗₁ η {X}) ∘ ρ⇐
  η-thread {A} {X} {Y} = begin
    α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
      ∘ ((id ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈˘⟨ assoc ⟩
    (α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
      ∘ ((id ⊗₁ η {Y}) ⊗₁ id {X ⁻¹}))
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈⟨ assoc-commute-from {f = id {A ⊗₀ X}} {g = η {Y}} {h = id {X ⁻¹}} ⟩∘⟨refl ⟩
    ((id {A ⊗₀ X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹}))
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹})
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈⟨ assoc ⟩
    (id {A ⊗₀ X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹}))
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ∎

  η-thread₂ : ∀ {A X Y} →
    α⇒ {A} {X} {(Y ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹}
      ∘ (id {A ⊗₀ X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹}))
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
    ≈ (id {A} ⊗₁ (id {X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹})))
        ∘ α⇒ {A} {X} {unit ⊗₀ X ⁻¹}
        ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
        ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
        ∘ (id ⊗₁ η {X}) ∘ ρ⇐
  η-thread₂ {A} {X} {Y} = begin
    α⇒ {A} {X} {(Y ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹}
      ∘ (id {A ⊗₀ X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹}))
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈˘⟨ assoc ⟩
    (α⇒ {A} {X} {(Y ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹}
      ∘ (id {A ⊗₀ X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹})))
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈⟨ α-sweep {Y = A} {B = X}
           {P = unit ⊗₀ X ⁻¹}
           {Q = (Y ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹}
           {k = η {Y} ⊗₁ id {X ⁻¹}} ⟩∘⟨refl ⟩
    ((id {A} ⊗₁ (id {X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹})))
      ∘ α⇒ {A} {X} {unit ⊗₀ X ⁻¹})
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈⟨ assoc ⟩
    (id {A} ⊗₁ (id {X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹})))
      ∘ α⇒ {A} {X} {unit ⊗₀ X ⁻¹}
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐ ∎

  η-unit-thread : ∀ {A X} →
    α⇒ {A} {X} {unit ⊗₀ X ⁻¹}
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
    ≈ (id {A} ⊗₁ (id {X} ⊗₁ λ⇐)) ∘ (id ⊗₁ η {X}) ∘ ρ⇐
  η-unit-thread {A} {X} = begin
    α⇒ {A} {X} {unit ⊗₀ X ⁻¹}
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    α⇒ {A} {X} {unit ⊗₀ X ⁻¹}
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ ((ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹})
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈˘⟨ refl⟩∘⟨ assoc ⟩
    α⇒ {A} {X} {unit ⊗₀ X ⁻¹}
      ∘ (α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ ((ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}))
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈˘⟨ assoc ⟩
    (α⇒ {A} {X} {unit ⊗₀ X ⁻¹}
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹})
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈⟨ α-unit {A} {X} {X ⁻¹} ⟩∘⟨refl ⟩
    (id {A} ⊗₁ (id {X} ⊗₁ λ⇐)) ∘ (id ⊗₁ η {X}) ∘ ρ⇐ ∎

private
  cup-reassoc : ∀ {Y P Q} →
    (id {Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q})
      ∘ α⇒ {Y} {Y ⁻¹ ⊗₀ P} {Q}
      ∘ (α⇒ {Y} {Y ⁻¹} {P} ⊗₁ id {Q})
      ∘ ((η {Y} ⊗₁ id {P}) ⊗₁ id {Q})
      ∘ (λ⇐ ⊗₁ id {Q})
    ≈ α⇒ {Y} {Y ⁻¹} {P ⊗₀ Q}
        ∘ (η {Y} ⊗₁ id {P ⊗₀ Q})
        ∘ λ⇐
  cup-reassoc {Y} {P} {Q} =
    (refl⟩∘⟨ sym-assoc ○ sym-assoc)
    ○ pentagon ⟩∘⟨refl
    ○ assoc
    ○ (refl⟩∘⟨ (sym-assoc ○ (assoc-commute-from ⟩∘⟨refl) ○ assoc))
    ○ refl⟩∘⟨ (refl⟩⊗⟨ id⊗id) ⟩∘⟨refl
    ○ refl⟩∘⟨ refl⟩∘⟨ λ-left

  cupᵀ-outer-naturality : ∀ {X Y P Q} →
    (id {X ⊗₀ Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q})
      ∘ α⇐ {X} {Y} {(Y ⁻¹ ⊗₀ P) ⊗₀ Q}
    ≈ α⇐ {X} {Y} {Y ⁻¹ ⊗₀ (P ⊗₀ Q)}
        ∘ (id {X} ⊗₁ (id {Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q}))
  cupᵀ-outer-naturality {X} {Y} {P} {Q} =
    begin
    (id {X ⊗₀ Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q})
      ∘ α⇐ {X} {Y} {(Y ⁻¹ ⊗₀ P) ⊗₀ Q}
      ≈˘⟨ ((id⊗id {X} {Y}) ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    ((id {X} ⊗₁ id {Y}) ⊗₁ α⇒ {Y ⁻¹} {P} {Q})
      ∘ α⇐ {X} {Y} {(Y ⁻¹ ⊗₀ P) ⊗₀ Q}
      ≈˘⟨ assoc-commute-to
            {f = id {X}} {g = id {Y}}
            {h = α⇒ {Y ⁻¹} {P} {Q}} ⟩
    α⇐ {X} {Y} {Y ⁻¹ ⊗₀ (P ⊗₀ Q)}
      ∘ (id {X} ⊗₁ (id {Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q})) ∎

  cupᵀ-outer : ∀ {X Y P Q} →
    (id {X ⊗₀ Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q})
      ∘ α⇐ {X} {Y} {(Y ⁻¹ ⊗₀ P) ⊗₀ Q}
      ∘ (id {X} ⊗₁ expanded-cup {Y} {P} {Q})
    ≈ α⇐ {X} {Y} {Y ⁻¹ ⊗₀ (P ⊗₀ Q)}
        ∘ (id {X} ⊗₁ cupᵀ {Y} {P} {Q})
  cupᵀ-outer {X} {Y} {P} {Q} = begin
    (id {X ⊗₀ Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q})
      ∘ α⇐ {X} {Y} {(Y ⁻¹ ⊗₀ P) ⊗₀ Q}
      ∘ (id {X} ⊗₁ expanded-cup {Y} {P} {Q})
      ≈˘⟨ assoc ⟩
    ((id {X ⊗₀ Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q})
      ∘ α⇐ {X} {Y} {(Y ⁻¹ ⊗₀ P) ⊗₀ Q})
      ∘ (id {X} ⊗₁ expanded-cup {Y} {P} {Q})
      ≈⟨ cupᵀ-outer-naturality {X} {Y} {P} {Q} ⟩∘⟨refl ⟩
    (α⇐ {X} {Y} {Y ⁻¹ ⊗₀ (P ⊗₀ Q)}
      ∘ (id {X} ⊗₁ (id {Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q})))
      ∘ (id {X} ⊗₁ expanded-cup {Y} {P} {Q})
      ≈⟨ assoc ⟩
    α⇐ {X} {Y} {Y ⁻¹ ⊗₀ (P ⊗₀ Q)}
      ∘ (id {X} ⊗₁ (id {Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q}))
      ∘ (id {X} ⊗₁ expanded-cup {Y} {P} {Q})
      ≈⟨ refl⟩∘⟨ merge₂ˡ ⟩
    α⇐ {X} {Y} {Y ⁻¹ ⊗₀ (P ⊗₀ Q)}
      ∘ (id {X} ⊗₁
        ((id {Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q}) ∘ expanded-cup {Y} {P} {Q}))
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ cup-reassoc {Y} {P} {Q}) ⟩
    α⇐ {X} {Y} {Y ⁻¹ ⊗₀ (P ⊗₀ Q)}
      ∘ (id {X} ⊗₁ cupᵀ {Y} {P} {Q}) ∎

  id⊗cap-cup : ∀ {X Y P Q} {k : P ⊗₀ Q ⇒ Y} →
    ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ ε {Y}) ∘ (id {X ⊗₀ Y} ⊗₁ (id {Y ⁻¹} ⊗₁ k))
      ∘ (id {X ⊗₀ Y} ⊗₁ α⇒ {Y ⁻¹} {P} {Q}) ∘ α⇐ {X} {Y} {(Y ⁻¹ ⊗₀ P) ⊗₀ Q}
      ∘ (id {X} ⊗₁ expanded-cup {Y} {P} {Q}) ≈ id {X} ⊗₁ k
  id⊗cap-cup {X} {Y} {P} {Q} {k} =
    begin
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ k)) ∘ (id ⊗₁ α⇒)
      ∘ α⇐ ∘ (id {X} ⊗₁ expanded-cup {Y} {P} {Q})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cupᵀ-outer {X} {Y} {P} {Q} ⟩
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ k))
      ∘ α⇐ ∘ (id {X} ⊗₁ cupᵀ {Y} {P} {Q})
      ≈˘⟨ refl⟩∘⟨ assoc ⟩
    ρ⇒ ∘ ((id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ k)))
      ∘ α⇐ ∘ (id {X} ⊗₁ cupᵀ {Y} {P} {Q})
      ≈⟨ refl⟩∘⟨ merge₂ˡ ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id ⊗₁ capᵀ {Y} {P} {Q} {k})
      ∘ α⇐ ∘ (id {X} ⊗₁ cupᵀ {Y} {P} {Q})
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    ρ⇒ ∘ ((id ⊗₁ capᵀ {Y} {P} {Q} {k}) ∘ α⇐)
      ∘ (id {X} ⊗₁ cupᵀ {Y} {P} {Q})
      ≈⟨ sym-assoc ⟩
    (ρ⇒ ∘ ((id ⊗₁ capᵀ {Y} {P} {Q} {k}) ∘ α⇐))
      ∘ (id {X} ⊗₁ cupᵀ {Y} {P} {Q})
      ≈⟨ ρ-sweep {X = X} {Y = Y} {h = capᵀ {Y} {P} {Q} {k}} ⟩∘⟨refl ⟩
    (id {X} ⊗₁ (ρ⇒ ∘ (id {Y} ⊗₁ capᵀ {Y} {P} {Q} {k}))) ∘ (id {X} ⊗₁ cupᵀ {Y} {P} {Q})
      ≈⟨ merge₂ˡ ⟩
    id {X} ⊗₁ ((ρ⇒ ∘ (id {Y} ⊗₁ capᵀ {Y} {P} {Q} {k})) ∘ cupᵀ {Y} {P} {Q})
      ≈⟨ refl⟩⊗⟨ cupᵀ-snake {Y} {P} {Q} {k} ⟩
    id {X} ⊗₁ k
      ∎

  ζ : ∀ {X Y} → X ⁻¹ ⇒ Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)
  ζ {X} {Y} = α⇒ ∘ (η {Y} ⊗₁ id) ∘ λ⇐

ξ : ∀ {X Y} → X ⁻¹ ⊗₀ (X ⊗₀ Y) ⇒ Y
ξ {X} {Y} = λ⇒ ∘ (ε {X} ⊗₁ id) ∘ α⇐

⊗-cup : ∀ {X Y} → unit ⇒ (X ⊗₀ Y) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)
⊗-cup {X} {Y} =
  α⇐ {X} {Y} {Y ⁻¹ ⊗₀ X ⁻¹} ∘ (id {X} ⊗₁ α⇒ {Y} {Y ⁻¹} {X ⁻¹})
    ∘ (id {X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹})) ∘ (id {X} ⊗₁ λ⇐ {X ⁻¹}) ∘ η {X}

⊗-cap : ∀ {X Y} → (Y ⁻¹ ⊗₀ X ⁻¹) ⊗₀ (X ⊗₀ Y) ⇒ unit
⊗-cap {X} {Y} =
  ε {Y} ∘ (id {Y ⁻¹} ⊗₁ λ⇒ {Y}) ∘ (id {Y ⁻¹} ⊗₁ (ε {X} ⊗₁ id {Y}))
    ∘ (id {Y ⁻¹} ⊗₁ α⇐ {X ⁻¹} {X} {Y}) ∘ α⇒ {Y ⁻¹} {X ⁻¹} {X ⊗₀ Y}

private
  cup-factor : ∀ {X Y} →
    ⊗-cup {X} {Y} ≈ α⇐ ∘ (id ⊗₁ ζ {X} {Y}) ∘ η {X}
  cup-factor {X} {Y} =
    begin
    ⊗-cup {X} {Y}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    α⇐ {X} {Y} {Y ⁻¹ ⊗₀ X ⁻¹}
      ∘ (id {X} ⊗₁ α⇒ {Y} {Y ⁻¹} {X ⁻¹})
      ∘ (id {X} ⊗₁ ((η {Y} ⊗₁ id {X ⁻¹}) ∘ λ⇐ {X ⁻¹}))
      ∘ η {X}
      ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    α⇐ ∘ (id ⊗₁ ζ {X} {Y}) ∘ η {X}
      ∎

cap-factor : ∀ {X Y} →
  ⊗-cap {X} {Y} ≈ ε {Y} ∘ (id ⊗₁ ξ {X} {Y}) ∘ α⇒
cap-factor {X} {Y} =
  begin
  ⊗-cap {X} {Y}
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
  ε {Y}
    ∘ (id {Y ⁻¹} ⊗₁ λ⇒ {Y})
    ∘ (id {Y ⁻¹} ⊗₁ ((ε {X} ⊗₁ id {Y}) ∘ α⇐ {X ⁻¹} {X} {Y}))
    ∘ α⇒ {Y ⁻¹} {X ⁻¹} {X ⊗₀ Y}
    ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
  ε {Y} ∘ (id ⊗₁ ξ {X} {Y}) ∘ α⇒
    ∎

private
  inner-fill : ∀ {X Y} → X ⊗₀ (X ⁻¹ ⊗₀ (X ⊗₀ Y)) ⇒
    X ⊗₀ (Y ⊗₀ ((Y ⁻¹ ⊗₀ X ⁻¹) ⊗₀ (X ⊗₀ Y)))
  inner-fill {X} {Y} = id {X} ⊗₁ expanded-cup {Y} {X ⁻¹} {X ⊗₀ Y}

  inner-cap : ∀ {X Y} → X ⊗₀ (X ⁻¹ ⊗₀ (X ⊗₀ Y)) ⇒ X ⊗₀ Y
  inner-cap {X} {Y} =
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y}))
      ∘ (id ⊗₁ α⇒) ∘ α⇐ ∘ inner-fill {X} {Y}

  ζ-inner : ∀ {X Y} → X ⊗₀ (X ⁻¹ ⊗₀ (X ⊗₀ Y)) ⇒ X ⊗₀ Y
  ζ-inner {X} {Y} =
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y}))
      ∘ (id ⊗₁ α⇒) ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (ζ {X} {Y} ⊗₁ id))

  outer-cup : ∀ {X Y} → X ⊗₀ Y ⇒ X ⊗₀ (X ⁻¹ ⊗₀ (X ⊗₀ Y))
  outer-cup {X} {Y} = α⇒ ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐

  cup-loop : ∀ {X Y} → X ⊗₀ Y ⇒ X ⊗₀ Y
  cup-loop {X} {Y} = inner-cap {X} {Y} ∘ outer-cup {X} {Y}

  ζ-loop : ∀ {X Y} → X ⊗₀ Y ⇒ X ⊗₀ Y
  ζ-loop {X} {Y} = ζ-inner {X} {Y} ∘ α⇒ ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐

  ζ-arrival : ∀ {X Y} → X ⊗₀ Y ⇒ X ⊗₀ Y
  ζ-arrival {X} {Y} =
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y}))
      ∘ (id ⊗₁ α⇒) ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (ζ {X} {Y} ⊗₁ id))
      ∘ α⇒ ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐

  ζ-arrival-factor : ∀ {X Y} → ζ-arrival {X} {Y} ≈ ζ-loop {X} {Y}
  ζ-arrival-factor =
    refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
    ○ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
    ○ refl⟩∘⟨ sym-assoc
    ○ sym-assoc

  inner-cap-snake : ∀ {X Y} → inner-cap {X} {Y} ≈ id {X} ⊗₁ ξ {X} {Y}
  inner-cap-snake {X} {Y} =
    id⊗cap-cup {X} {Y} {X ⁻¹} {X ⊗₀ Y} {ξ {X} {Y}}

  inner-snake₁ : ∀ {X Y} →
    cup-loop {X} {Y}
    ≈ (id {X} ⊗₁ ξ {X} {Y}) ∘ α⇒ ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
  inner-snake₁ {X} {Y} = begin
    cup-loop {X} {Y}
      ≈⟨ inner-cap-snake {X} {Y} ⟩∘⟨refl ⟩
    (id {X} ⊗₁ ξ {X} {Y}) ∘ α⇒ ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
      ∎

  outer-snake₁ : ∀ {X Y} →
    (id {X} ⊗₁ ξ {X} {Y}) ∘ α⇒ ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
    ≈ ((ρ⇒ ⊗₁ id {Y}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Y}))
        ∘ (α⇒ ⊗₁ id {Y}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Y}
        ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
  outer-snake₁ {X} {Y} = begin
    (id {X} ⊗₁ ξ {X} {Y}) ∘ α⇒ ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
      ≈˘⟨ assoc ⟩
    ((id {X} ⊗₁ ξ {X} {Y}) ∘ α⇒)
      ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
      ≈⟨ cap-reassoc {A = X} {P = X ⁻¹} {Q = X} {B = Y} {cap = ε {X}} ⟩∘⟨refl ⟩
    (((ρ⇒ ⊗₁ id {Y}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Y}))
      ∘ (α⇒ ⊗₁ id {Y}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Y})
      ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
      ≈⟨ ⟺ (refl⟩∘⟨ sym-assoc ○ sym-assoc) ⟩
    ((ρ⇒ ⊗₁ id {Y}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Y}))
      ∘ (α⇒ ⊗₁ id {Y}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Y}
      ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐ ∎

  split-snake₁ : ∀ {X Y} →
    cup-loop {X} {Y}
    ≈ ((ρ⇒ ⊗₁ id {Y}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Y}))
      ∘ (α⇒ ⊗₁ id {Y}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Y} ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
  split-snake₁ {X} {Y} = begin
    cup-loop {X} {Y}
      ≈⟨ inner-snake₁ {X} {Y} ⟩
    (id {X} ⊗₁ ξ {X} {Y}) ∘ α⇒ ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
      ≈⟨ outer-snake₁ {X} {Y} ⟩
    ((ρ⇒ ⊗₁ id {Y}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Y}))
      ∘ (α⇒ ⊗₁ id {Y}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Y} ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
      ∎

  ζ-inner-context : ∀ {X Y} → ζ-inner {X} {Y} ≈ inner-cap {X} {Y}
  ζ-inner-context {X} {Y} = begin
    ζ-inner {X} {Y}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ merge₂ˡ ⟩
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y}))
      ∘ (id ⊗₁ α⇒) ∘ α⇐
      ∘ (id {X} ⊗₁ (α⇒ ∘ (ζ {X} {Y} ⊗₁ id {X ⊗₀ Y})))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
          (refl⟩⊗⟨ (refl⟩∘⟨ (split₁ˡ ○ (refl⟩∘⟨ split₁ˡ)))) ⟩
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y}))
      ∘ (id ⊗₁ α⇒) ∘ α⇐
      ∘ (id {X} ⊗₁ (α⇒ ∘ ((α⇒ ⊗₁ id) ∘ ((η {Y} ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id))))
      ≈⟨ Equiv.refl ⟩
    inner-cap {X} {Y}
      ∎

  ζ-context : ∀ {X Y} → ζ-loop {X} {Y} ≈ cup-loop {X} {Y}
  ζ-context {X} {Y} = begin
    ζ-loop {X} {Y}
      ≈⟨ ζ-inner-context {X} {Y} ⟩∘⟨refl ⟩
    inner-cap {X} {Y} ∘ α⇒ ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
      ≈⟨ Equiv.refl ⟩
    cup-loop {X} {Y}
      ∎

  ⊗-snake-core : ∀ {X Y} → ζ-loop {X} {Y} ≈ id {X ⊗₀ Y}
  ⊗-snake-core {X} {Y} = begin
    ζ-loop {X} {Y}
      ≈⟨ ζ-context {X} {Y} ⟩
    cup-loop {X} {Y}
      ≈⟨ split-snake₁ {X} {Y} ⟩
    ((ρ⇒ ⊗₁ id {Y}) ∘ ((id ⊗₁ ε {X}) ⊗₁ id {Y}))
      ∘ (α⇒ ⊗₁ id {Y}) ∘ α⇐ {X ⊗₀ X ⁻¹} {X} {Y} ∘ (η {X} ⊗₁ id {X ⊗₀ Y}) ∘ λ⇐
      ≈⟨ snake₁⊗id {X} {Y} ⟩
    id {X ⊗₀ Y}
      ∎

  ⊗-snakeˡ-spine : ∀ {X Y} →
    ρ⇒ ∘ ((id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y})) ∘ (id ⊗₁ α⇒))
      ∘ α⇒ ∘ ((α⇐ ⊗₁ id) ∘ ((id ⊗₁ ζ {X} {Y}) ⊗₁ id) ∘ (η {X} ⊗₁ id)) ∘ λ⇐
    ≈ ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y})) ∘ (id ⊗₁ α⇒)
      ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ ζ {X} {Y}) ⊗₁ id) ∘ (η {X} ⊗₁ id) ∘ λ⇐
  ⊗-snakeˡ-spine {X} {Y} = begin
    ρ⇒ ∘ ((id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y})) ∘ (id ⊗₁ α⇒))
      ∘ α⇒ ∘ ((α⇐ ⊗₁ id) ∘ ((id ⊗₁ ζ {X} {Y}) ⊗₁ id) ∘ (η {X} ⊗₁ id)) ∘ λ⇐
      ≈˘⟨ refl⟩∘⟨ sym-assoc ⟩
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ ((id ⊗₁ (id ⊗₁ ξ {X} {Y})) ∘ (id ⊗₁ α⇒))
      ∘ α⇒ ∘ ((α⇐ ⊗₁ id) ∘ ((id ⊗₁ ζ {X} {Y}) ⊗₁ id) ∘ (η {X} ⊗₁ id)) ∘ λ⇐
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y})) ∘ (id ⊗₁ α⇒)
      ∘ α⇒ ∘ ((α⇐ ⊗₁ id) ∘ ((id ⊗₁ ζ {X} {Y}) ⊗₁ id) ∘ (η {X} ⊗₁ id)) ∘ λ⇐
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y})) ∘ (id ⊗₁ α⇒) ∘ α⇒
      ∘ (α⇐ ⊗₁ id) ∘ (((id ⊗₁ ζ {X} {Y}) ⊗₁ id) ∘ (η {X} ⊗₁ id)) ∘ λ⇐
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ (id ⊗₁ ξ {X} {Y})) ∘ (id ⊗₁ α⇒) ∘ α⇒
      ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ ζ {X} {Y}) ⊗₁ id) ∘ (η {X} ⊗₁ id) ∘ λ⇐
      ∎

⊗-snakeˡ : ∀ {X Y} →
  ρ⇒ ∘ (id ⊗₁ ⊗-cap {X} {Y})
    ∘ α⇒ ∘ (⊗-cup {X} {Y} ⊗₁ id) ∘ λ⇐
  ≈ id {X ⊗₀ Y}
⊗-snakeˡ {X} {Y} =
  refl⟩∘⟨ (refl⟩⊗⟨ cap-factor) ⟩∘⟨ refl⟩∘⟨ (cup-factor ⟩⊗⟨refl) ⟩∘⟨refl
  ○ (refl⟩∘⟨ (split₂ˡ ○ (refl⟩∘⟨ split₂ˡ)) ⟩∘⟨ refl⟩∘⟨ (split₁ˡ ○ (refl⟩∘⟨ split₁ˡ)) ⟩∘⟨refl)
  ○ ⊗-snakeˡ-spine
  ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (pentagon′ {X} {Y} {Y ⁻¹ ⊗₀ X ⁻¹} {X ⊗₀ Y})
  ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ (refl⟩∘⟨ sym-assoc ○ sym-assoc)
  ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ assoc-commute-from
  ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc
  ○ ζ-arrival-factor
  ○ ⊗-snake-core
