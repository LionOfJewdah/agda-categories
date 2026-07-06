{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)

module Categories.Category.Monoidal.CompactClosed.Trace.Construction
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C)
    (S : Symmetric M)
    (R : LeftRigid M) where

open import Data.Product using (_,_)

open import Categories.Category.Monoidal.CompactClosed.Trace.Definition M S R
  using (trace; trace-resp-≈; trace-expand; trace-tightenₗ; trace-whiskerˡ-expand)
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided S)
  using (braiding-coherenceʳ-inv)
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Symmetric.Properties S
  using (braiding-coherenceˡ-inv)

open Category C
open Monoidal M
open LeftRigid R using (_⁻¹; η; ε; snake₁)
open Symmetric S using (braiding; hexagon₁)

open import Categories.Category.Monoidal.Reasoning M
open TensorIdentity using (id⊗id; whisker-∘)
open import Categories.Morphism.Reasoning C
import Categories.Category.Monoidal.Properties M as MonoidalProps
open MonoidalProps using (coherence₂; coherence-inv₂; coherence₃; coherence-inv₃)
import Categories.Category.Monoidal.Utilities M as MonUtil
open MonUtil.Shorthands
open BraidShorthands using (σ⇒)
open MonoidalProps.Structural using (α-sweep; α⊗id-cancel; assoc-to-coherence)

private
  variable
    A B X Y : Obj

  cup-σ-unit : ∀ {X} →
    ((η {X} ⊗₁ id {X}) ∘ σ⇒ {X} {unit}) ∘ ρ⇐
    ≈ (η {X} ⊗₁ id {X}) ∘ λ⇐
  cup-σ-unit {X} = begin
    ((η {X} ⊗₁ id {X}) ∘ σ⇒ {X} {unit}) ∘ ρ⇐  ≈⟨ assoc ⟩
    (η {X} ⊗₁ id {X}) ∘ (σ⇒ {X} {unit} ∘ ρ⇐)  ≈⟨ refl⟩∘⟨ braiding-coherenceʳ-inv ⟩
    (η {X} ⊗₁ id {X}) ∘ λ⇐                    ∎

  unit-shuffle : ∀ {X} →
    λ⇒ {X ⊗₀ unit} ∘ α⇒ {unit} {X} {unit} ∘ ρ⇐ {unit ⊗₀ X}
    ≈ ρ⇐ {X} ∘ λ⇒ {X}
  unit-shuffle {X} = begin
    λ⇒ {X ⊗₀ unit} ∘ α⇒ {unit} {X} {unit} ∘ ρ⇐ {unit ⊗₀ X}
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₂ {X = unit} {Y = X} ⟩
    λ⇒ {X ⊗₀ unit} ∘ α⇒ {unit} {X} {unit}
      ∘ (α⇐ {unit} {X} {unit} ∘ (id {unit} ⊗₁ ρ⇐ {X}))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    λ⇒ {X ⊗₀ unit} ∘ (α⇒ {unit} {X} {unit} ∘ α⇐ {unit} {X} {unit})
      ∘ (id {unit} ⊗₁ ρ⇐ {X})
      ≈⟨ refl⟩∘⟨ associator.isoʳ ⟩∘⟨refl ⟩
    λ⇒ {X ⊗₀ unit} ∘ id ∘ (id {unit} ⊗₁ ρ⇐ {X})
      ≈⟨ refl⟩∘⟨ identityˡ ⟩
    λ⇒ {X ⊗₀ unit} ∘ (id {unit} ⊗₁ ρ⇐ {X})
      ≈⟨ unitorˡ-commute-from ⟩
    ρ⇐ {X} ∘ λ⇒ {X}
      ∎

  yank-spine : ∀ {X} →
      (id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ ∘ (σ⇒ {X} {X} ⊗₁ id) ∘ α⇐
        ∘ (id ⊗₁ η) ∘ ρ⇐
    ≈ ((id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ ∘ (σ⇒ {X} {X} ⊗₁ id) ∘ α⇐)
        ∘ (id ⊗₁ η) ∘ ρ⇐
  yank-spine {X} = begin
    (id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ ∘ (σ⇒ {X} {X} ⊗₁ id) ∘ α⇐
      ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈˘⟨ refl⟩∘⟨ assoc²βε ⟩
    (id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ (α⇒ ∘ (σ⇒ {X} {X} ⊗₁ id) ∘ α⇐)
      ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈˘⟨ assoc ⟩
    ((id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ ∘ (σ⇒ {X} {X} ⊗₁ id) ∘ α⇐)
      ∘ (id ⊗₁ η) ∘ ρ⇐
      ∎

braid-loop-collapse : ∀ {X} →
    (id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ ∘ (σ⇒ {X} {X} ⊗₁ id) ∘ α⇐
  ≈ α⇒ ∘ σ⇒ {X} {X ⊗₀ X ⁻¹}
braid-loop-collapse {X} =
  begin
  (id {X} ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ {X} {X} {X ⁻¹}
    ∘ (σ⇒ {X} {X} ⊗₁ id {X ⁻¹}) ∘ α⇐ {X} {X} {X ⁻¹}
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  (id {X} ⊗₁ σ⇒ {X} {X ⁻¹})
    ∘ (α⇒ {X} {X} {X ⁻¹} ∘ (σ⇒ {X} {X} ⊗₁ id {X ⁻¹}))
    ∘ α⇐ {X} {X} {X ⁻¹}
    ≈⟨ sym-assoc ⟩
  ((id {X} ⊗₁ σ⇒ {X} {X ⁻¹})
    ∘ (α⇒ {X} {X} {X ⁻¹} ∘ (σ⇒ {X} {X} ⊗₁ id {X ⁻¹})))
    ∘ α⇐ {X} {X} {X ⁻¹}
    ≈⟨ hexagon₁ {X = X} {Y = X} {Z = X ⁻¹} ⟩∘⟨refl ⟩
  (α⇒ {X} {X ⁻¹} {X}
    ∘ (σ⇒ {X} {X ⊗₀ X ⁻¹} ∘ α⇒ {X} {X} {X ⁻¹}))
    ∘ α⇐ {X} {X} {X ⁻¹}
    ≈⟨ assoc²βε ⟩
  α⇒ {X} {X ⁻¹} {X} ∘ σ⇒ {X} {X ⊗₀ X ⁻¹}
    ∘ α⇒ {X} {X} {X ⁻¹} ∘ α⇐ {X} {X} {X ⁻¹}
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ associator.isoʳ {X} {X} {X ⁻¹} ⟩
  α⇒ {X} {X ⁻¹} {X} ∘ σ⇒ {X} {X ⊗₀ X ⁻¹} ∘ id
    ≈⟨ refl⟩∘⟨ identityʳ ⟩
  α⇒ {X} {X ⁻¹} {X} ∘ σ⇒ {X} {X ⊗₀ X ⁻¹}
    ∎

yanking : ∀ {X} → trace (σ⇒ {X} {X}) ≈ id
yanking {X} = begin
    trace (σ⇒ {X} {X})                                              ≈⟨ trace-expand ⟩
    ρ⇒ ∘ (id ⊗₁ ε {X}) ∘ (id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒
      ∘ (σ⇒ {X} {X} ⊗₁ id {X ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ yank-spine ⟩
    ρ⇒ ∘ (id ⊗₁ ε {X})
      ∘ (((id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ ∘ (σ⇒ {X} {X} ⊗₁ id {X ⁻¹}) ∘ α⇐)
      ∘ (id ⊗₁ η {X}) ∘ ρ⇐)                                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braid-loop-collapse ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id ⊗₁ ε {X})
      ∘ ((α⇒ ∘ σ⇒ {X} {X ⊗₀ X ⁻¹}) ∘ (id ⊗₁ η {X}) ∘ ρ⇐)           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullʳ (pullˡ (braiding.⇒.commute (id , η))) ⟩
    ρ⇒ ∘ (id ⊗₁ ε {X}) ∘ α⇒
      ∘ ((η {X} ⊗₁ id {X}) ∘ σ⇒ {X} {unit}) ∘ ρ⇐                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cup-σ-unit ⟩
    ρ⇒ ∘ (id ⊗₁ ε {X}) ∘ α⇒ ∘ (η {X} ⊗₁ id {X}) ∘ λ⇐              ≈⟨ snake₁ ⟩
    id                                                             ∎

-- The compact-closed "dimension" of the monoidal unit is the identity scalar.
unit-dimension : ε {unit} ∘ σ⇒ {unit} {unit ⁻¹} ∘ η ≈ id
unit-dimension = begin
  ε {unit} ∘ σ⇒ {unit} {unit ⁻¹} ∘ η
    ≈⟨ refl⟩∘⟨ braiding-coherenceˡ-inv ⟩∘⟨refl ⟩
  ε {unit} ∘ (ρ⇐ {unit ⁻¹} ∘ λ⇒ {unit ⁻¹}) ∘ η {unit}
    ≈˘⟨ refl⟩∘⟨ unit-shuffle {unit ⁻¹} ⟩∘⟨refl ⟩
  ε {unit} ∘ (λ⇒ {unit ⁻¹ ⊗₀ unit} ∘ α⇒ {unit} {unit ⁻¹} {unit} ∘ ρ⇐ {unit ⊗₀ unit ⁻¹})
    ∘ η {unit}
    ≈⟨ refl⟩∘⟨ pullʳ (pullʳ unitorʳ-commute-to) ⟩
  ε {unit} ∘ λ⇒ {unit ⁻¹ ⊗₀ unit} ∘ α⇒ {unit} {unit ⁻¹} {unit}
    ∘ (η {unit} ⊗₁ id {unit}) ∘ ρ⇐ {unit}
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ coherence-inv₃ ⟩
  ε {unit} ∘ λ⇒ {unit ⁻¹ ⊗₀ unit} ∘ α⇒ {unit} {unit ⁻¹} {unit}
    ∘ (η {unit} ⊗₁ id {unit}) ∘ λ⇐ {unit}
    ≈⟨ pullˡ (⟺ unitorˡ-commute-from) ⟩
  (λ⇒ {unit} ∘ (id {unit} ⊗₁ ε {unit})) ∘ α⇒ {unit} {unit ⁻¹} {unit}
    ∘ (η {unit} ⊗₁ id {unit}) ∘ λ⇐ {unit}
    ≈⟨ (coherence₃ ⟩∘⟨refl) ⟩∘⟨refl ⟩
  (ρ⇒ {unit} ∘ (id {unit} ⊗₁ ε {unit})) ∘ α⇒ {unit} {unit ⁻¹} {unit}
    ∘ (η {unit} ⊗₁ id {unit}) ∘ λ⇐ {unit}
    ≈⟨ assoc ⟩
  ρ⇒ {unit} ∘ (id {unit} ⊗₁ ε {unit}) ∘ α⇒ {unit} {unit ⁻¹} {unit}
    ∘ (η {unit} ⊗₁ id {unit}) ∘ λ⇐ {unit}
    ≈⟨ snake₁ ⟩
  id
    ∎

private
  superpose-map : ∀ {X Y A B} → A ⊗₀ X ⇒ B ⊗₀ X → (Y ⊗₀ A) ⊗₀ X ⇒ (Y ⊗₀ B) ⊗₀ X
  superpose-map {X} {Y} {A} {B} f =
    α⇐ {Y} {B} {X} ∘ (id {Y} ⊗₁ f) ∘ α⇒ {Y} {A} {X}

  loop-map : ∀ {X A B} → A ⊗₀ X ⇒ B ⊗₀ X → A ⊗₀ (X ⊗₀ X ⁻¹) ⇒ B ⊗₀ (X ⊗₀ X ⁻¹)
  loop-map {X} {A} {B} f =
    α⇒ {B} {X} {X ⁻¹} ∘ (f ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}

  superpose-window : ∀ {X Y A B}
    → A ⊗₀ X ⇒ B ⊗₀ X
    → (Y ⊗₀ A) ⊗₀ (X ⊗₀ X ⁻¹) ⇒ Y ⊗₀ (B ⊗₀ (X ⊗₀ X ⁻¹))
  superpose-window {X} {Y} {A} {B} f =
    α⇒ {Y} {B} {X ⊗₀ X ⁻¹} ∘ α⇒ {Y ⊗₀ B} {X} {X ⁻¹}
      ∘ (superpose-map {Y = Y} f ⊗₁ id {X ⁻¹}) ∘ α⇐ {Y ⊗₀ A} {X} {X ⁻¹}

  vanish₁-loop : ∀ {A} →
                 ρ⇒ ∘ (id {A} ⊗₁ ε) ∘ (id ⊗₁ σ⇒ {unit} {unit ⁻¹}) ∘ (id ⊗₁ η) ∘ ρ⇐
                 ≈ id
  vanish₁-loop {A} = begin
    ρ⇒ ∘ (id {A} ⊗₁ ε) ∘ (id ⊗₁ σ⇒ {unit} {unit ⁻¹}) ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ʳ ⟩
    ρ⇒ ∘ (id {A} ⊗₁ ε) ∘ (id {A} ⊗₁ (σ⇒ {unit} {unit ⁻¹} ∘ η)) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ pullˡ merge₂ʳ ⟩
    ρ⇒ ∘ (id {A} ⊗₁ (ε ∘ σ⇒ {unit} {unit ⁻¹} ∘ η)) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ unit-dimension) ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id {A} ⊗₁ id) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ id⊗id ⟩∘⟨refl ⟩
    ρ⇒ ∘ id ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ identityˡ ⟩
    ρ⇒ ∘ ρ⇐
      ≈⟨ unitorʳ.isoʳ ⟩
    id
      ∎

  trace-unit-id : ∀ {A} → trace {X = unit} (id {A} ⊗₁ id {unit}) ≈ id
  trace-unit-id {A} = begin
    trace {X = unit} (id {A} ⊗₁ id {unit})
      ≈⟨ trace-expand ⟩
    ρ⇒ ∘ (id {A} ⊗₁ ε {unit}) ∘ (id {A} ⊗₁ σ⇒ {unit} {unit ⁻¹})
      ∘ α⇒ {A} {unit} {unit ⁻¹}
      ∘ ((id {A} ⊗₁ id {unit}) ⊗₁ id {unit ⁻¹})
      ∘ α⇐ {A} {unit} {unit ⁻¹} ∘ (id {A} ⊗₁ η {unit}) ∘ ρ⇐ {A}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (id⊗id {X = A} {Y = unit} ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id {A} ⊗₁ ε {unit}) ∘ (id {A} ⊗₁ σ⇒ {unit} {unit ⁻¹})
      ∘ α⇒ {A} {unit} {unit ⁻¹}
      ∘ (id {A ⊗₀ unit} ⊗₁ id {unit ⁻¹})
      ∘ α⇐ {A} {unit} {unit ⁻¹} ∘ (id {A} ⊗₁ η {unit}) ∘ ρ⇐ {A}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ id⊗id {X = A ⊗₀ unit} {Y = unit ⁻¹} ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id {A} ⊗₁ ε {unit}) ∘ (id {A} ⊗₁ σ⇒ {unit} {unit ⁻¹})
      ∘ α⇒ {A} {unit} {unit ⁻¹}
      ∘ id ∘ α⇐ {A} {unit} {unit ⁻¹} ∘ (id {A} ⊗₁ η {unit}) ∘ ρ⇐ {A}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ identityˡ ⟩
    ρ⇒ ∘ (id {A} ⊗₁ ε {unit}) ∘ (id {A} ⊗₁ σ⇒ {unit} {unit ⁻¹})
      ∘ α⇒ {A} {unit} {unit ⁻¹}
      ∘ α⇐ {A} {unit} {unit ⁻¹} ∘ (id {A} ⊗₁ η {unit}) ∘ ρ⇐ {A}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoʳ ⟩
    ρ⇒ ∘ (id {A} ⊗₁ ε {unit}) ∘ (id {A} ⊗₁ σ⇒ {unit} {unit ⁻¹})
      ∘ (id {A} ⊗₁ η {unit}) ∘ ρ⇐ {A}
      ≈⟨ vanish₁-loop {A} ⟩
    id
      ∎

vanishing₁ : ∀ {A B} {f : A ⇒ B} → trace {X = unit} (f ⊗₁ id) ≈ f
vanishing₁ {A} {B} {f} = begin
  trace {X = unit} (f ⊗₁ id)
    ≈˘⟨ trace-resp-≈ (elimʳ id⊗id) ⟩
  trace {X = unit} ((f ⊗₁ id {unit}) ∘ (id {A} ⊗₁ id {unit}))
    ≈⟨ trace-tightenₗ {X = unit} {f = f} {g = id {A} ⊗₁ id {unit}} ⟩
  f ∘ trace {X = unit} (id {A} ⊗₁ id {unit})
    ≈⟨ refl⟩∘⟨ trace-unit-id {A} ⟩
  f ∘ id
    ≈⟨ identityʳ ⟩
  f
    ∎

private
  superpose-assoc : ∀ {X Y A B} {f : A ⊗₀ X ⇒ B ⊗₀ X}
    → superpose-window {Y = Y} f ≈ (id {Y} ⊗₁ loop-map f) ∘ α⇒ {Y} {A} {X ⊗₀ X ⁻¹}
  superpose-assoc {X} {Y} {A} {B} {f} =
    (refl⟩∘⟨ refl⟩∘⟨ (split₁ˡ ○ (refl⟩∘⟨ split₁ˡ)) ⟩∘⟨refl)
    ○ sym-assoc
    ○ (⟺ pentagon) ⟩∘⟨refl
    ○ sym-assoc ⟩∘⟨ assoc
    ○ center α⊗id-cancel
    ○ refl⟩∘⟨ identityˡ
    ○ assoc
    ○ refl⟩∘⟨ refl⟩∘⟨ assoc
    ○ refl⟩∘⟨ pullˡ assoc-commute-from
    ○ refl⟩∘⟨ assoc
    ○ refl⟩∘⟨ refl⟩∘⟨ ⟺ assoc-to-coherence
    ○ refl⟩∘⟨ pullˡ (⟺ whisker-∘)
    ○ pullˡ (⟺ whisker-∘)

  superpose-core : ∀ {X Y A B} {f : A ⊗₀ X ⇒ B ⊗₀ X} →
      α⇒ {Y} {B} {X ⊗₀ X ⁻¹} ∘ α⇒ {Y ⊗₀ B} {X} {X ⁻¹}
        ∘ (superpose-map {Y = Y} f ⊗₁ id {X ⁻¹})
        ∘ α⇐ {Y ⊗₀ A} {X} {X ⁻¹}
        ∘ (id ⊗₁ η) ∘ ρ⇐
    ≈ (id {Y} ⊗₁ loop-map f)
        ∘ α⇒ {Y} {A} {X ⊗₀ X ⁻¹} ∘ (id ⊗₁ η) ∘ ρ⇐
  superpose-core {X} {Y} {A} {B} {f} = begin
    α⇒ {Y} {B} {X ⊗₀ X ⁻¹} ∘ α⇒ {Y ⊗₀ B} {X} {X ⁻¹}
      ∘ (superpose-map {Y = Y} f ⊗₁ id {X ⁻¹})
      ∘ α⇐ {Y ⊗₀ A} {X} {X ⁻¹} ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    α⇒ {Y} {B} {X ⊗₀ X ⁻¹} ∘ α⇒ {Y ⊗₀ B} {X} {X ⁻¹}
      ∘ ((superpose-map {Y = Y} f ⊗₁ id {X ⁻¹})
      ∘ α⇐ {Y ⊗₀ A} {X} {X ⁻¹}) ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    α⇒ {Y} {B} {X ⊗₀ X ⁻¹}
      ∘ (α⇒ {Y ⊗₀ B} {X} {X ⁻¹}
      ∘ (superpose-map {Y = Y} f ⊗₁ id {X ⁻¹})
      ∘ α⇐ {Y ⊗₀ A} {X} {X ⁻¹}) ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈⟨ sym-assoc ⟩
    superpose-window {Y = Y} f ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈⟨ superpose-assoc ⟩∘⟨refl ⟩
    ((id {Y} ⊗₁ loop-map f)
      ∘ α⇒ {Y} {A} {X ⊗₀ X ⁻¹}) ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈⟨ assoc ⟩
    (id {Y} ⊗₁ loop-map f)
      ∘ α⇒ {Y} {A} {X ⊗₀ X ⁻¹} ∘ (id ⊗₁ η) ∘ ρ⇐
      ∎

  superpose-cup : ∀ {Y A} →
    α⇒ {Y} {A} {unit} ∘ ρ⇐ {Y ⊗₀ A} ≈ id {Y} ⊗₁ ρ⇐ {A}
  superpose-cup {Y} {A} = begin
    α⇒ {Y} {A} {unit} ∘ ρ⇐ {Y ⊗₀ A}  ≈⟨ refl⟩∘⟨ ⟺ coherence-inv₂ ⟩
    α⇒ {Y} {A} {unit} ∘ α⇐ ∘ (id {Y} ⊗₁ ρ⇐ {A})
      ≈⟨ cancelˡ associator.isoʳ ⟩
    id {Y} ⊗₁ ρ⇐ {A}                  ∎

  superpose-expand : ∀ {X Y A B} {f : A ⊗₀ X ⇒ B ⊗₀ X}
    → trace {X = X} (α⇐ ∘ (id {Y} ⊗₁ f) ∘ α⇒)
      ≈ (id {Y} ⊗₁ ρ⇒)
        ∘ (id {Y} ⊗₁ (id ⊗₁ ε))
        ∘ (id {Y} ⊗₁ (id ⊗₁ σ⇒))
        ∘ (id {Y} ⊗₁ α⇒)
        ∘ (id {Y} ⊗₁ (f ⊗₁ id))
        ∘ (id {Y} ⊗₁ α⇐)
        ∘ (id {Y} ⊗₁ (id ⊗₁ η))
        ∘ (id {Y} ⊗₁ ρ⇐)
  superpose-expand {X} {Y} {A} {B} {f} =
    trace-expand
    ○ ⟺ coherence₂ ⟩∘⟨refl
    ○ assoc
    ○ refl⟩∘⟨ pullˡ α-sweep
    ○ refl⟩∘⟨ assoc
    ○ refl⟩∘⟨ refl⟩∘⟨ pullˡ α-sweep
    ○ refl⟩∘⟨ refl⟩∘⟨ assoc
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ superpose-core
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ α-sweep
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ superpose-cup
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
        (((whisker-∘ ○ (refl⟩∘⟨ whisker-∘)) ⟩∘⟨refl)
        ○ assoc
        ○ (refl⟩∘⟨ assoc)))

superposing : ∀ {X Y A B} {f : A ⊗₀ X ⇒ B ⊗₀ X}
  → trace {X = X} (α⇐ ∘ (id {Y} ⊗₁ f) ∘ α⇒)
    ≈ id {Y} ⊗₁ trace {X = X} f
superposing {X} {Y} {A} {B} {f} =
  begin
  trace {X = X} (α⇐ ∘ (id {Y} ⊗₁ f) ∘ α⇒)
    ≈⟨ superpose-expand ⟩
  (id {Y} ⊗₁ ρ⇒)
    ∘ (id {Y} ⊗₁ (id ⊗₁ ε))
    ∘ (id {Y} ⊗₁ (id ⊗₁ σ⇒))
    ∘ (id {Y} ⊗₁ α⇒)
    ∘ (id {Y} ⊗₁ (f ⊗₁ id))
    ∘ (id {Y} ⊗₁ α⇐)
    ∘ (id {Y} ⊗₁ (id ⊗₁ η))
    ∘ (id {Y} ⊗₁ ρ⇐)
    ≈˘⟨ trace-whiskerˡ-expand ⟩
  id {Y} ⊗₁ trace {X = X} f
    ∎
