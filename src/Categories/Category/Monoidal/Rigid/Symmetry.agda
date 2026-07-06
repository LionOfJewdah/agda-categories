{-# OPTIONS --without-K --safe #-}


open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Rigid using (LeftRigid; RightRigid)

module Categories.Category.Monoidal.Rigid.Symmetry
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) (S : Symmetric M) where

open Category C
open Monoidal M
open Symmetric S using (braided; commutative)
import Categories.Category.Monoidal.Utilities M as MonUtil
open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
  using ()
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Rigid.Symmetry.Properties M S
  using (braid-snakeˡ; braid-snakeʳ; transposeˡ⇒ʳ)
open import Categories.Morphism.Reasoning C

open MonUtil.Shorthands
open BraidShorthands

private
  module Left⇒Right (R : LeftRigid M) where
    open LeftRigid R using (_⁻¹; η; ε; snake₁; snake₂)

    snake₁ʳ : ∀ {X} →
      λ⇒ ∘ ((ε {X} ∘ σ⇒ {X} {X ⁻¹}) ⊗₁ id)
        ∘ α⇐ ∘ (id ⊗₁ (σ⇒ {X} {X ⁻¹} ∘ η {X})) ∘ ρ⇐
      ≈ id {X}
    snake₁ʳ {X} =
      braid-snakeˡ {X = X} {Y = X ⁻¹} {ηₗ = η {X}} {εₗ = ε {X}} (snake₁ {X})

    snake₂ʳ : ∀ {X} →
      ρ⇒ ∘ (id ⊗₁ (ε {X} ∘ σ⇒ {X} {X ⁻¹}))
        ∘ α⇒ ∘ ((σ⇒ {X} {X ⁻¹} ∘ η {X}) ⊗₁ id) ∘ λ⇐
      ≈ id {X ⁻¹}
    snake₂ʳ {X} =
      braid-snakeʳ {X = X ⁻¹} {Y = X} {ηᵣ = η {X}} {εᵣ = ε {X}} (snake₂ {X})

left⇒right : LeftRigid M → RightRigid M
left⇒right R =
  let open Left⇒Right R in record
    { _⁻¹ = LeftRigid._⁻¹ R
    ; η = σ⇒ ∘ LeftRigid.η R
    ; ε = LeftRigid.ε R ∘ σ⇒
    ; snake₁ = snake₁ʳ
    ; snake₂ = snake₂ʳ
    }

private
  module Right⇒Left (R : RightRigid M) where
    open RightRigid R using (_⁻¹; η; ε; snake₁; snake₂)

    snake₁ˡ : ∀ {X} →
      ρ⇒ ∘ (id ⊗₁ (ε {X} ∘ σ⇒ {X ⁻¹} {X}))
        ∘ α⇒ ∘ ((σ⇒ {X ⁻¹} {X} ∘ η {X}) ⊗₁ id) ∘ λ⇐
      ≈ id {X}
    snake₁ˡ {X} =
      braid-snakeʳ {X = X} {Y = X ⁻¹} {ηᵣ = η {X}} {εᵣ = ε {X}} (snake₁ {X})

    snake₂ˡ : ∀ {X} →
      λ⇒ ∘ ((ε {X} ∘ σ⇒ {X ⁻¹} {X}) ⊗₁ id)
        ∘ α⇐ ∘ (id ⊗₁ (σ⇒ {X ⁻¹} {X} ∘ η {X})) ∘ ρ⇐
      ≈ id {X ⁻¹}
    snake₂ˡ {X} =
      braid-snakeˡ {X = X ⁻¹} {Y = X} {ηₗ = η {X}} {εₗ = ε {X}} (snake₂ {X})

right⇒left : RightRigid M → LeftRigid M
right⇒left R =
  let open Right⇒Left R in record
    { _⁻¹ = RightRigid._⁻¹ R
    ; η = σ⇒ ∘ RightRigid.η R
    ; ε = RightRigid.ε R ∘ σ⇒
    ; snake₁ = snake₁ˡ
    ; snake₂ = snake₂ˡ
    }

η-roundtripˡ : (R : LeftRigid M) → ∀ {X} →
  LeftRigid.η (right⇒left (left⇒right R)) {X} ≈ LeftRigid.η R {X}
η-roundtripˡ R {X} =
  let open LeftRigid R using (_⁻¹; η) in begin
  σ⇒ {X ⁻¹} {X} ∘ (σ⇒ {X} {X ⁻¹} ∘ η {X})  ≈˘⟨ assoc ⟩
  (σ⇒ {X ⁻¹} {X} ∘ σ⇒ {X} {X ⁻¹}) ∘ η {X}  ≈⟨ commutative ⟩∘⟨refl ⟩
  id ∘ η {X}                                 ≈⟨ identityˡ ⟩
  η {X}                                      ∎

ε-roundtripˡ : (R : LeftRigid M) → ∀ {X} →
  LeftRigid.ε (right⇒left (left⇒right R)) {X} ≈ LeftRigid.ε R {X}
ε-roundtripˡ R {X} =
  let open LeftRigid R using (_⁻¹; ε) in begin
  (ε {X} ∘ σ⇒ {X} {X ⁻¹}) ∘ σ⇒ {X ⁻¹} {X}  ≈⟨ assoc ⟩
  ε {X} ∘ (σ⇒ {X} {X ⁻¹} ∘ σ⇒ {X ⁻¹} {X})  ≈⟨ refl⟩∘⟨ commutative ⟩
  ε {X} ∘ id                                ≈⟨ identityʳ ⟩
  ε {X}                                     ∎

η-roundtripʳ : (R : RightRigid M) → ∀ {X} →
  RightRigid.η (left⇒right (right⇒left R)) {X} ≈ RightRigid.η R {X}
η-roundtripʳ R {X} =
  let open RightRigid R using (_⁻¹; η) in begin
  σ⇒ {X} {X ⁻¹} ∘ (σ⇒ {X ⁻¹} {X} ∘ η {X})  ≈˘⟨ assoc ⟩
  (σ⇒ {X} {X ⁻¹} ∘ σ⇒ {X ⁻¹} {X}) ∘ η {X}  ≈⟨ commutative ⟩∘⟨refl ⟩
  id ∘ η {X}                                ≈⟨ identityˡ ⟩
  η {X}                                     ∎

ε-roundtripʳ : (R : RightRigid M) → ∀ {X} →
  RightRigid.ε (left⇒right (right⇒left R)) {X} ≈ RightRigid.ε R {X}
ε-roundtripʳ R {X} =
  let open RightRigid R using (_⁻¹; ε) in begin
  (ε {X} ∘ σ⇒ {X ⁻¹} {X}) ∘ σ⇒ {X} {X ⁻¹}  ≈⟨ assoc ⟩
  ε {X} ∘ (σ⇒ {X ⁻¹} {X} ∘ σ⇒ {X} {X ⁻¹})  ≈⟨ refl⟩∘⟨ commutative ⟩
  ε {X} ∘ id                                ≈⟨ identityʳ ⟩
  ε {X}                                     ∎

private
  module Dual₁ˡ≈dual₁ʳProof (R : LeftRigid M) {X Y} (f : X ⇒ Y) where
    open LeftRigid R using (_⁻¹; η; ε; dual₁)

    ηʳ : unit ⇒ X ⁻¹ ⊗₀ X
    ηʳ = σ⇒ {X} {X ⁻¹} ∘ η {X}

    f-slide :
      σ⇒ {Y} {X ⁻¹} ∘ ((f ⊗₁ id {X ⁻¹}) ∘ η {X})
      ≈ (id {X ⁻¹} ⊗₁ f) ∘ ηʳ
    f-slide = begin
      σ⇒ {Y} {X ⁻¹} ∘ ((f ⊗₁ id {X ⁻¹}) ∘ η {X})   ≈˘⟨ assoc ⟩
      (σ⇒ {Y} {X ⁻¹} ∘ (f ⊗₁ id {X ⁻¹})) ∘ η {X}   ≈⟨ σ-commute {f = f} {g = id {X ⁻¹}} ⟩∘⟨refl ⟩
      ((id {X ⁻¹} ⊗₁ f) ∘ σ⇒ {X} {X ⁻¹}) ∘ η {X}   ≈⟨ assoc ⟩
      (id {X ⁻¹} ⊗₁ f) ∘ ηʳ                        ∎

    f-slide-α :
      α⇒ ∘ ((σ⇒ {Y} {X ⁻¹} ∘ ((f ⊗₁ id {X ⁻¹}) ∘ η {X})) ⊗₁ id {Y ⁻¹}) ∘ λ⇐
      ≈ (id {X ⁻¹} ⊗₁ (f ⊗₁ id {Y ⁻¹}))
          ∘ α⇒ ∘ (ηʳ ⊗₁ id {Y ⁻¹}) ∘ λ⇐
    f-slide-α = begin
      α⇒ ∘ ((σ⇒ {Y} {X ⁻¹} ∘ ((f ⊗₁ id {X ⁻¹}) ∘ η {X})) ⊗₁ id {Y ⁻¹}) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ (f-slide ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      α⇒ ∘ (((id {X ⁻¹} ⊗₁ f) ∘ ηʳ) ⊗₁ id {Y ⁻¹}) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
      α⇒ ∘ (((id {X ⁻¹} ⊗₁ f) ⊗₁ id {Y ⁻¹}) ∘ (ηʳ ⊗₁ id {Y ⁻¹})) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ assoc ⟩
      α⇒ ∘ ((id {X ⁻¹} ⊗₁ f) ⊗₁ id {Y ⁻¹}) ∘ (ηʳ ⊗₁ id {Y ⁻¹}) ∘ λ⇐
        ≈˘⟨ assoc ⟩
      (α⇒ ∘ ((id {X ⁻¹} ⊗₁ f) ⊗₁ id {Y ⁻¹})) ∘ (ηʳ ⊗₁ id {Y ⁻¹}) ∘ λ⇐
        ≈⟨ assoc-commute-from {f = id {X ⁻¹}} {g = f} {h = id {Y ⁻¹}} ⟩∘⟨refl ⟩
      ((id {X ⁻¹} ⊗₁ (f ⊗₁ id {Y ⁻¹})) ∘ α⇒) ∘ (ηʳ ⊗₁ id {Y ⁻¹}) ∘ λ⇐
        ≈⟨ assoc ⟩
      (id {X ⁻¹} ⊗₁ (f ⊗₁ id {Y ⁻¹})) ∘ α⇒ ∘ (ηʳ ⊗₁ id {Y ⁻¹}) ∘ λ⇐ ∎

    proof : dual₁ f ≈ RightRigid.dual₁ (left⇒right R) f
    proof = begin
      dual₁ f
        ≈⟨ transposeˡ⇒ʳ {A = Y ⁻¹} {B = X ⁻¹} {Y = Y}
             {E = ε {Y}} {H = (f ⊗₁ id {X ⁻¹}) ∘ η {X}} ⟩
      ρ⇒ ∘ (id {X ⁻¹} ⊗₁ (ε {Y} ∘ σ⇒ {Y} {Y ⁻¹}))
        ∘ α⇒
        ∘ ((σ⇒ {Y} {X ⁻¹} ∘ ((f ⊗₁ id {X ⁻¹}) ∘ η {X})) ⊗₁ id {Y ⁻¹})
        ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ f-slide-α ⟩
      ρ⇒ ∘ (id {X ⁻¹} ⊗₁ (ε {Y} ∘ σ⇒ {Y} {Y ⁻¹}))
        ∘ (id {X ⁻¹} ⊗₁ (f ⊗₁ id {Y ⁻¹}))          ∘ α⇒
        ∘ ((σ⇒ {X} {X ⁻¹} ∘ η {X}) ⊗₁ id {Y ⁻¹})   ∘ λ⇐
        ∎

dual₁ˡ≈dual₁ʳ : (R : LeftRigid M) → ∀ {X Y} (f : X ⇒ Y) →
  LeftRigid.dual₁ R f ≈ RightRigid.dual₁ (left⇒right R) f
dual₁ˡ≈dual₁ʳ R f = Dual₁ˡ≈dual₁ʳProof.proof R f

private
  module Dual₁RoundtripʳProof (R : RightRigid M) {X Y} (f : X ⇒ Y) where
    open RightRigid R using (_⁻¹; η; ε)

    R′ : RightRigid M
    R′ = left⇒right (right⇒left R)

    ε-step :
      RightRigid.dual₁ R′ f
      ≈ ρ⇒ ∘ (id {X ⁻¹} ⊗₁ ε {Y})
          ∘ (id {X ⁻¹} ⊗₁ (f ⊗₁ id {Y ⁻¹}))
          ∘ α⇒ ∘ (RightRigid.η R′ {X} ⊗₁ id {Y ⁻¹}) ∘ λ⇐
    ε-step =
      refl⟩∘⟨ ((refl⟩⊗⟨ ε-roundtripʳ R {Y}) ⟩∘⟨refl)

    η-tail :
      α⇒ ∘ (RightRigid.η R′ {X} ⊗₁ id {Y ⁻¹}) ∘ λ⇐
      ≈ α⇒ ∘ (η {X} ⊗₁ id {Y ⁻¹}) ∘ λ⇐
    η-tail =
      refl⟩∘⟨ ((η-roundtripʳ R {X} ⟩⊗⟨refl) ⟩∘⟨refl)

    η-step :
      ρ⇒ ∘ (id {X ⁻¹} ⊗₁ ε {Y})
        ∘ (id {X ⁻¹} ⊗₁ (f ⊗₁ id {Y ⁻¹}))
        ∘ α⇒ ∘ (RightRigid.η R′ {X} ⊗₁ id {Y ⁻¹}) ∘ λ⇐
      ≈ RightRigid.dual₁ R f
    η-step =
      refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ η-tail

    proof : RightRigid.dual₁ R′ f ≈ RightRigid.dual₁ R f
    proof = begin
      RightRigid.dual₁ R′ f
        ≈⟨ ε-step ⟩
      ρ⇒ ∘ (id {X ⁻¹} ⊗₁ ε {Y})
        ∘ (id {X ⁻¹} ⊗₁ (f ⊗₁ id {Y ⁻¹}))
        ∘ α⇒ ∘ (RightRigid.η R′ {X} ⊗₁ id {Y ⁻¹}) ∘ λ⇐
        ≈⟨ η-step ⟩
      RightRigid.dual₁ R f
        ∎

dual₁-roundtripʳ : (R : RightRigid M) → ∀ {X Y} (f : X ⇒ Y) →
  RightRigid.dual₁ (left⇒right (right⇒left R)) f ≈ RightRigid.dual₁ R f
dual₁-roundtripʳ R f = Dual₁RoundtripʳProof.proof R f

dual₁-roundtripˡ : (R : LeftRigid M) → ∀ {X Y} (f : X ⇒ Y) →
  LeftRigid.dual₁ (right⇒left (left⇒right R)) f ≈ LeftRigid.dual₁ R f
dual₁-roundtripˡ R f = begin
  LeftRigid.dual₁ (right⇒left (left⇒right R)) f
    ≈⟨ dual₁ˡ≈dual₁ʳ (right⇒left (left⇒right R)) f ⟩
  RightRigid.dual₁ (left⇒right (right⇒left (left⇒right R))) f
    ≈⟨ dual₁-roundtripʳ (left⇒right R) f ⟩
  RightRigid.dual₁ (left⇒right R) f
    ≈˘⟨ dual₁ˡ≈dual₁ʳ R f ⟩
  LeftRigid.dual₁ R f
    ∎

dual₁ʳ≈dual₁ˡ : (R : RightRigid M) → ∀ {X Y} (f : X ⇒ Y) →
  RightRigid.dual₁ R f ≈ LeftRigid.dual₁ (right⇒left R) f
dual₁ʳ≈dual₁ˡ R f = begin
  RightRigid.dual₁ R f
    ≈˘⟨ dual₁-roundtripʳ R f ⟩
  RightRigid.dual₁ (left⇒right (right⇒left R)) f
    ≈˘⟨ dual₁ˡ≈dual₁ʳ (right⇒left R) f ⟩
  LeftRigid.dual₁ (right⇒left R) f
    ∎
