{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)

module Categories.Category.Monoidal.Rigid.Dual
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) (R : LeftRigid M) where

open Category C
open Monoidal M
open LeftRigid R using (_⁻¹; η; ε; snake₁; dual₁)

open import Categories.Category.Monoidal.Reasoning M
open TensorIdentity using (id⊗id; ⊗id-∘)
open import Categories.Morphism.Reasoning C
import Categories.Category.Monoidal.Properties M as MonoidalProps
open MonoidalProps
  using (coherence₁; coherence-inv₁; coherence-inv₂; coherence-inv₃)
import Categories.Category.Monoidal.Utilities M as MonUtil

open MonUtil.Shorthands
open MonoidalProps.Structural using (assoc-to-coherence; pentagon′; triangle-inv)

private
  variable
    W X Y Z : Obj

  mateˡ : ∀ {X Z W} → Z ⊗₀ X ⇒ unit → unit ⇒ X ⊗₀ W → Z ⇒ W
  mateˡ {Z = Z} {W = W} cap cup =
    λ⇒ ∘ (cap ⊗₁ id {W}) ∘ α⇐ ∘ (id {Z} ⊗₁ cup) ∘ ρ⇐

cup-ᵀ⇒ : ∀ {X Z} → unit ⇒ X ⊗₀ Z → X ⁻¹ ⇒ Z
cup-ᵀ⇒ {X} g = mateˡ (ε {X}) g

private
  module MateˡLaw
      {X Z W}
      (cup : unit ⇒ X ⊗₀ Z)
      (cap : Z ⊗₀ X ⇒ unit)
      (cup′ : unit ⇒ X ⊗₀ W)
      (snake : ρ⇒ ∘ (id {X} ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id {X}) ∘ λ⇐ ≈ id {X})
      where

    cup-slide : (cup ⊗₁ cup′) ∘ ρ⇐ ≈ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′
    cup-slide = begin
      (cup ⊗₁ cup′) ∘ ρ⇐
        ≈⟨ serialize₁₂ ⟩∘⟨refl ⟩
      ((cup ⊗₁ id) ∘ (id ⊗₁ cup′)) ∘ ρ⇐
        ≈⟨ assoc ⟩
      (cup ⊗₁ id) ∘ ((id ⊗₁ cup′) ∘ ρ⇐)
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟩
      (cup ⊗₁ id) ∘ ((id ⊗₁ cup′) ∘ λ⇐)
        ≈˘⟨ refl⟩∘⟨ unitorˡ-commute-to ⟩
      (cup ⊗₁ id) ∘ λ⇐ ∘ cup′
        ∎

    collect-cup :
        ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
          ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′
      ≈ (((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
          ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (cup ⊗₁ id) ∘ λ⇐) ∘ cup′
    collect-cup = begin
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ ((cup ⊗₁ id) ∘ λ⇐) ∘ cup′
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ (α⇐ ∘ (cup ⊗₁ id) ∘ λ⇐) ∘ cup′
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ ((α⇒ ⊗₁ id) ∘ α⇐ ∘ (cup ⊗₁ id) ∘ λ⇐) ∘ cup′
        ≈⟨ sym-assoc ⟩
      (((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (cup ⊗₁ id) ∘ λ⇐) ∘ cup′
        ∎

    merge-whiskerʳ : ∀ {P Q T} {a : Q ⇒ T} {b : P ⇒ Q} →
      (a ⊗₁ id {W}) ∘ (b ⊗₁ id {W}) ≈ (a ∘ b) ⊗₁ id {W}
    merge-whiskerʳ {a = a} {b} = begin
      (a ⊗₁ id) ∘ (b ⊗₁ id)
        ≈˘⟨ ⊗-distrib-over-∘ ⟩
      (a ∘ b) ⊗₁ (id ∘ id)
        ≈⟨ Equiv.refl ⟩⊗⟨ identity² ⟩
      (a ∘ b) ⊗₁ id
        ∎

    merge-snake :
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ ((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)
      ≈ ((ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐) ⊗₁ id)
    merge-snake = begin
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ ((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)
        ≈⟨ assoc ⟩
      (ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id)
        ∘ ((α⇒ ⊗₁ id) ∘ ((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ merge-whiskerʳ ⟩
      (ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id)
        ∘ ((α⇒ ⊗₁ id) ∘ ((cup ⊗₁ id) ∘ λ⇐) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge-whiskerʳ ⟩
      (ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id)
        ∘ ((α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ merge-whiskerʳ ⟩
      (ρ⇒ ⊗₁ id) ∘ (((id ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐) ⊗₁ id)
        ≈⟨ merge-whiskerʳ ⟩
      ((ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐) ⊗₁ id)
        ∎

    snake⊗id-coherence :
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ α⇐ {X ⊗₀ Z} {X} {W}
        ∘ (cup ⊗₁ id) ∘ λ⇐
      ≈ ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
          ∘ (α⇒ ⊗₁ id) ∘ ((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)
    snake⊗id-coherence = begin
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ α⇐ {X ⊗₀ Z} {X} {W}
        ∘ (cup ⊗₁ id) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩⊗⟨ ⟺ id⊗id) ⟩∘⟨refl) ⟩
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ α⇐ {X ⊗₀ Z} {X} {W}
        ∘ (cup ⊗₁ (id {X} ⊗₁ id {W})) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ assoc-commute-to ⟩
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ (((cup ⊗₁ id) ⊗₁ id) ∘ α⇐ {unit} {X} {W}) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ ((cup ⊗₁ id) ⊗₁ id) ∘ α⇐ {unit} {X} {W} ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₁ ⟩
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ ((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)
        ∎

    snake⊗id :
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ α⇐ {X ⊗₀ Z} {X} {W}
        ∘ (cup ⊗₁ id) ∘ λ⇐
      ≈ id {X ⊗₀ W}
    snake⊗id = begin
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ α⇐ {X ⊗₀ Z} {X} {W}
        ∘ (cup ⊗₁ id) ∘ λ⇐
        ≈⟨ snake⊗id-coherence ⟩
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ ((cup ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id)
        ≈⟨ merge-snake ⟩
      (ρ⇒ ∘ (id ⊗₁ cap) ∘ α⇒ ∘ (cup ⊗₁ id) ∘ λ⇐) ⊗₁ id
        ≈⟨ snake ⟩⊗⟨refl ⟩
      id ⊗₁ id
        ≈⟨ id⊗id ⟩
      id
        ∎

    id⊗ρ⇐ : (id {X} ⊗₁ ρ⇐ {Z}) ≈ α⇒ ∘ ρ⇐ {X ⊗₀ Z}
    id⊗ρ⇐ = begin
      id {X} ⊗₁ ρ⇐ {Z}
        ≈˘⟨ cancelˡ associator.isoʳ ⟩
      α⇒ ∘ (α⇐ ∘ (id {X} ⊗₁ ρ⇐ {Z}))
        ≈⟨ refl⟩∘⟨ coherence-inv₂ ⟩
      α⇒ ∘ ρ⇐ {X ⊗₀ Z}
        ∎

    assoc-cup :
      (id {X} ⊗₁ α⇐ {Z} {X} {W}) ∘ α⇒ {X} {Z} {X ⊗₀ W}
      ≈ α⇒ {X} {Z ⊗₀ X} {W} ∘ (α⇒ {X} {Z} {X} ⊗₁ id)
          ∘ α⇐ {X ⊗₀ Z} {X} {W}
    assoc-cup = assoc-to-coherence

    mateˡ-cup-expand :
        (id {X} ⊗₁ mateˡ cap cup′) ∘ cup
      ≈ ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
          ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′
    mateˡ-cup-expand =
      ((split₂ˡ
        ○ (refl⟩∘⟨ split₂ˡ)
        ○ (refl⟩∘⟨ refl⟩∘⟨ split₂ˡ)
        ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ)) ⟩∘⟨refl)
      ○ ⟺ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
        ○ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
        ○ refl⟩∘⟨ sym-assoc
        ○ sym-assoc)
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (id⊗ρ⇐ ⟩∘⟨refl)
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ-commute-to
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (⟺ assoc-commute-from)
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (⟺ ⊗-distrib-over-∘)
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ((elimˡ id⊗id ⟩⊗⟨ identityʳ) ⟩∘⟨refl)
      ○ refl⟩∘⟨ refl⟩∘⟨ pullˡ assoc-cup
      ○ refl⟩∘⟨ refl⟩∘⟨ (assoc ○ refl⟩∘⟨ assoc)
      ○ refl⟩∘⟨ pullˡ (⟺ assoc-commute-from)
      ○ pullˡ (pullˡ triangle)
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cup-slide

    mateˡ-cup : (id {X} ⊗₁ mateˡ cap cup′) ∘ cup ≈ cup′
    mateˡ-cup = begin
      (id {X} ⊗₁ mateˡ cap cup′) ∘ cup
        ≈⟨ mateˡ-cup-expand ⟩
      ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (cup ⊗₁ id) ∘ λ⇐ ∘ cup′
        ≈⟨ collect-cup ⟩
      (((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ cap) ⊗₁ id))
        ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (cup ⊗₁ id) ∘ λ⇐) ∘ cup′
        ≈⟨ snake⊗id ⟩∘⟨refl ⟩
      id ∘ cup′
        ≈⟨ identityˡ ⟩
      cup′
        ∎

cup-ᵀ : ∀ {X Z} (g : unit ⇒ X ⊗₀ Z) →
  (id {X} ⊗₁ cup-ᵀ⇒ g) ∘ η {X} ≈ g
cup-ᵀ {X} g = MateˡLaw.mateˡ-cup (η {X}) (ε {X}) g (snake₁ {X})

dual₁-cup : ∀ {X Y} {f : X ⇒ Y} →
  (id {Y} ⊗₁ dual₁ f) ∘ η {Y}
  ≈ (f ⊗₁ id {X ⁻¹}) ∘ η {X}
dual₁-cup {X} {Y} {f} = cup-ᵀ {X = Y} {Z = X ⁻¹} ((f ⊗₁ id {X ⁻¹}) ∘ η {X})

cap-ᵀ : ∀ {X W} → W ⊗₀ X ⇒ unit → W ⇒ X ⁻¹
cap-ᵀ {X} k = mateˡ k (η {X})

private
  module CapᵀCounit {X W} (k : W ⊗₀ X ⇒ unit) where
    ε-λ : ε {X} ∘ (λ⇒ ⊗₁ id) ≈ λ⇒ ∘ (id ⊗₁ ε {X}) ∘ α⇒
    ε-λ = begin
      ε {X} ∘ (λ⇒ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ ⟺ coherence₁ ⟩
      ε {X} ∘ (λ⇒ ∘ α⇒)
        ≈⟨ pullˡ (⟺ unitorˡ-commute-from) ⟩
      (λ⇒ ∘ (id ⊗₁ ε {X})) ∘ α⇒
        ≈⟨ assoc ⟩
      λ⇒ ∘ (id ⊗₁ ε {X}) ∘ α⇒
        ∎

    merge-ε : (id ⊗₁ ε {X}) ∘ (k ⊗₁ (id ⊗₁ id)) ≈ (k ⊗₁ ε {X})
    merge-ε = begin
      (id ⊗₁ ε {X}) ∘ (k ⊗₁ (id ⊗₁ id))
        ≈˘⟨ ⊗-distrib-over-∘ ⟩
      (id ∘ k) ⊗₁ (ε {X} ∘ (id ⊗₁ id))
        ≈⟨ identityˡ ⟩⊗⟨ elimʳ id⊗id ⟩
      k ⊗₁ ε {X}
        ∎

    η-assoc :
      α⇒ {W} {X ⊗₀ X ⁻¹} {X}
        ∘ ((id {W} ⊗₁ η {X}) ⊗₁ id {X})
        ∘ (ρ⇐ {W} ⊗₁ id {X})
      ≈ (id {W} ⊗₁ (η {X} ⊗₁ id {X}))
          ∘ α⇒ {W} {unit} {X}
          ∘ (ρ⇐ {W} ⊗₁ id {X})
    η-assoc =
      begin
      α⇒ {W} {X ⊗₀ X ⁻¹} {X}
        ∘ ((id {W} ⊗₁ η {X}) ⊗₁ id {X})
        ∘ (ρ⇐ {W} ⊗₁ id {X})
        ≈⟨ pullˡ (assoc-commute-from {f = id} {g = η {X}} {h = id}) ⟩
      ((id {W} ⊗₁ (η {X} ⊗₁ id {X})) ∘ α⇒ {W} {unit} {X})
        ∘ (ρ⇐ {W} ⊗₁ id {X})
        ≈⟨ assoc ⟩
      (id {W} ⊗₁ (η {X} ⊗₁ id {X}))
        ∘ α⇒ {W} {unit} {X}
        ∘ (ρ⇐ {W} ⊗₁ id {X})
        ∎

    η-unit : α⇒ {W} {unit} {X} ∘ (ρ⇐ ⊗₁ id) ≈ (id ⊗₁ λ⇐)
    η-unit = triangle-inv

    split-ε : (k ⊗₁ ε {X}) ≈ (k ⊗₁ id) ∘ (id ⊗₁ ε {X})
    split-ε = serialize₁₂

    ε-natural :
      (id ⊗₁ ε {X}) ∘ α⇐ {W} {X} {X ⁻¹ ⊗₀ X}
      ≈ α⇐ {W} {X} {unit} ∘ (id ⊗₁ (id ⊗₁ ε {X}))
    ε-natural = begin
      (id ⊗₁ ε {X}) ∘ α⇐ {W} {X} {X ⁻¹ ⊗₀ X}
        ≈˘⟨ (id⊗id ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      ((id {W} ⊗₁ id {X}) ⊗₁ ε {X}) ∘ α⇐ {W} {X} {X ⁻¹ ⊗₀ X}
        ≈˘⟨ assoc-commute-to {f = id} {g = id} {h = ε {X}} ⟩
      α⇐ {W} {X} {unit} ∘ (id ⊗₁ (id ⊗₁ ε {X}))
        ∎

    snake⇒ρ⇐ :
      (id ⊗₁ ε {X}) ∘ (α⇒ ∘ (η {X} ⊗₁ id) ∘ λ⇐) ≈ ρ⇐ {X}
    snake⇒ρ⇐ = begin
      (id ⊗₁ ε {X}) ∘ (α⇒ ∘ (η {X} ⊗₁ id) ∘ λ⇐)
        ≈˘⟨ cancelˡ unitorʳ.isoˡ ⟩
      ρ⇐ {X} ∘ (ρ⇒ ∘ (id ⊗₁ ε {X}) ∘ α⇒ ∘ (η {X} ⊗₁ id) ∘ λ⇐)
        ≈⟨ refl⟩∘⟨ snake₁ {X} ⟩
      ρ⇐ {X} ∘ id
        ≈⟨ identityʳ ⟩
      ρ⇐ {X}
        ∎

    assoc-ε :
      α⇒ {W ⊗₀ X} {X ⁻¹} {X} ∘ (α⇐ {W} {X} {X ⁻¹} ⊗₁ id)
      ≈ α⇐ {W} {X} {X ⁻¹ ⊗₀ X} ∘ (id ⊗₁ α⇒ {X} {X ⁻¹} {X})
          ∘ α⇒ {W} {X ⊗₀ X ⁻¹} {X}
    assoc-ε = pentagon′

    counit-expand : ε {X} ∘ (cap-ᵀ k ⊗₁ id {X}) ≈ id ∘ k
    counit-expand =
      refl⟩∘⟨ (split₁ˡ
        ○ (refl⟩∘⟨ split₁ˡ)
        ○ (refl⟩∘⟨ refl⟩∘⟨ split₁ˡ)
        ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ))
      ○ pullˡ ε-λ
      ○ ⟺ (refl⟩∘⟨ sym-assoc ○ sym-assoc)
      ○ refl⟩∘⟨ refl⟩∘⟨ pullˡ assoc-commute-from
      ○ refl⟩∘⟨ pullˡ (pullˡ merge-ε)
      ○ refl⟩∘⟨ assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ pullˡ assoc-ε
      ○ refl⟩∘⟨ refl⟩∘⟨ (assoc ○ refl⟩∘⟨ assoc)
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ η-assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ η-unit
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ merge₂ˡ ○ merge₂ˡ)
      ○ refl⟩∘⟨ (split-ε ⟩∘⟨refl)
      ○ refl⟩∘⟨ assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ pullˡ ε-natural
      ○ refl⟩∘⟨ refl⟩∘⟨ assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ snake⇒ρ⇐))
      ○ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₂
      ○ refl⟩∘⟨ ⟺ unitorʳ-commute-to
      ○ pullˡ (refl⟩∘⟨ ⟺ coherence-inv₃ ○ unitorˡ.isoʳ)

    counit : ε {X} ∘ (cap-ᵀ k ⊗₁ id {X}) ≈ k
    counit = begin
      ε {X} ∘ (cap-ᵀ k ⊗₁ id {X})
        ≈⟨ counit-expand ⟩
      id ∘ k
        ≈⟨ identityˡ ⟩
      k
        ∎

cap-ᵀ-counit : ∀ {X W} (k : W ⊗₀ X ⇒ unit) →
  ε {X} ∘ (cap-ᵀ k ⊗₁ id {X}) ≈ k
cap-ᵀ-counit k = CapᵀCounit.counit k

cap-ᵀ-cup : ∀ {X Z} {g : unit ⇒ X ⊗₀ Z} {k : Z ⊗₀ X ⇒ unit} →
  ρ⇒ ∘ (id {X} ⊗₁ k) ∘ α⇒ ∘ (g ⊗₁ id {X}) ∘ λ⇐ ≈ id {X} →
  (id {X} ⊗₁ cap-ᵀ k) ∘ g ≈ η {X}
cap-ᵀ-cup {X} {g = g} {k = k} snake =
  MateˡLaw.mateˡ-cup g k (η {X}) snake

private
  dual₁-as-cap-ᵀ : ∀ {X Y} {f : X ⇒ Y} →
    dual₁ f ≈ cap-ᵀ (ε {Y} ∘ (id {Y ⁻¹} ⊗₁ f))
  dual₁-as-cap-ᵀ {X} {Y} {f} = begin
    λ⇒ ∘ (ε {Y} ⊗₁ id {X ⁻¹}) ∘ α⇐
      ∘ (id {Y ⁻¹} ⊗₁ ((f ⊗₁ id {X ⁻¹}) ∘ η {X})) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
    λ⇒ ∘ (ε {Y} ⊗₁ id {X ⁻¹}) ∘ α⇐
      ∘ ((id ⊗₁ (f ⊗₁ id {X ⁻¹})) ∘ (id {Y ⁻¹} ⊗₁ η {X})) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pull-first (assoc-commute-to {f = id {Y ⁻¹}} {g = f} {h = id {X ⁻¹}}) ⟩
    λ⇒ ∘ (ε {Y} ⊗₁ id {X ⁻¹})
      ∘ ((((id {Y ⁻¹} ⊗₁ f) ⊗₁ id {X ⁻¹}) ∘ α⇐)
          ∘ ((id {Y ⁻¹} ⊗₁ η {X}) ∘ ρ⇐))
      ≈⟨ refl⟩∘⟨ pull-first (⟺ (⊗id-∘ {W = X ⁻¹} {f = ε {Y}} {g = id {Y ⁻¹} ⊗₁ f})) ⟩
    λ⇒ ∘ ((ε {Y} ∘ (id {Y ⁻¹} ⊗₁ f)) ⊗₁ id {X ⁻¹}) ∘ α⇐
      ∘ (id {Y ⁻¹} ⊗₁ η {X}) ∘ ρ⇐
      ∎

dual₁-cap : ∀ {X Y} {f : X ⇒ Y} →
  ε {X} ∘ (dual₁ f ⊗₁ id {X}) ≈ ε {Y} ∘ (id {Y ⁻¹} ⊗₁ f)
dual₁-cap {X} {Y} {f} = begin
  ε {X} ∘ (dual₁ f ⊗₁ id {X})
    ≈⟨ refl⟩∘⟨ (dual₁-as-cap-ᵀ {f = f} ⟩⊗⟨refl) ⟩
  ε {X} ∘ (cap-ᵀ (ε {Y} ∘ (id {Y ⁻¹} ⊗₁ f)) ⊗₁ id {X})
    ≈⟨ cap-ᵀ-counit {X} {Y ⁻¹} (ε {Y} ∘ (id {Y ⁻¹} ⊗₁ f)) ⟩
  ε {Y} ∘ (id {Y ⁻¹} ⊗₁ f)
    ∎
