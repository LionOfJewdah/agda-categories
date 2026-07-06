{-# OPTIONS --without-K --safe #-}


open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)

module Categories.Category.Monoidal.CompactClosed.TensorDual
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) (S : Symmetric M) (R : LeftRigid M) where

open import Data.Product using (_,_)

open Category C
open Monoidal M
open LeftRigid R using (_⁻¹; η; ε)
open Symmetric S using (braiding)
import Categories.Category.Monoidal.Utilities M as MonUtil
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided S)
  using () renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided S)
  using (module swapInner; swapInner-braiding)
open import Categories.Category.Monoidal.Reasoning M
open TensorIdentity using (id⊗id)
open import Categories.Morphism.Reasoning C
import Categories.Category.Monoidal.Properties M as MonoidalProps
open MonoidalProps using (coherence-inv₁; coherence-inv₂; coherence-inv₃)
open import Categories.Category.Monoidal.CompactClosed.CapInterchange M S R
  using (capʳ; mid-capˡ; mid-capʳ; mid-swapInnerˡ; paired-cap-interchangeʳ)
open import Categories.Category.Monoidal.Rigid.TensorDual M R
  using
    ( ⊗-cup; ⊗-cap; ⊗-snakeˡ; ξ; cap-factor ; module CupThreading )
open import Categories.Category.Monoidal.Rigid.Properties M as RigidProps
open RigidProps.Left R
  using (⊗-dual⇒; ⊗-dual-cup; ⊗-dual-cap)

open MonUtil.Shorthands
open BraidShorthands using (σ⇒)
open CupThreading using (η-thread; η-thread₂; η-unit-thread)
open MonoidalProps.Structural using
  ( cancel-middle; assoc-pair-coherence; assoc-to-coherence ; α-peel⊗id; α-inner
  ; cap-reassoc; ρ-peel; α-sweep; α-unit; α⊗id-cancel )

private variable A X Y : Obj

nested-cap-core : ∀ {X Y} →
  (X ⊗₀ Y) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹) ⇒ X ⊗₀ X ⁻¹
nested-cap-core {X} {Y} =
  (ρ⇒ ⊗₁ id {X ⁻¹})
    ∘ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹})
    ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹})
    ∘ ((α⇒ {X} {Y} {Y ⁻¹} ⊗₁ id {X ⁻¹}))
    ∘ α⇐ {X ⊗₀ Y} {Y ⁻¹} {X ⁻¹}

nested-cap : ∀ {X Y} →
  (X ⊗₀ Y) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹) ⇒ unit
nested-cap {X} {Y} =
  ε {X} ∘ σ⇒ {X} {X ⁻¹} ∘ nested-cap-core {X} {Y}

iterated-cap : ∀ {A X Y} →
  (A ⊗₀ (X ⊗₀ Y)) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹) ⇒ A
iterated-cap {A} {X} {Y} =
  ρ⇒ {A} ∘ (id ⊗₁ ε {X}) ∘ (id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒
    ∘ (ρ⇒ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹})
    ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹})
    ∘ (α⇒ ⊗₁ id {X ⁻¹})
    ∘ ((α⇐ ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹}) ∘ α⇐

nested-cap-context : ∀ {A X Y} →
  (A ⊗₀ (X ⊗₀ Y)) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹) ⇒ A
nested-cap-context {A} {X} {Y} =
  ρ⇒ {A} ∘ (id ⊗₁ nested-cap {X} {Y}) ∘ α⇒

private
  nested-cap-coherence : ∀ {A X Y} →
    ((id {A} ⊗₁ (ρ⇒ ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ (α⇒ ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ α⇐ {X ⊗₀ Y} {Y ⁻¹} {X ⁻¹}))
      ∘ α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ≈ α⇒ {A} {X} {X ⁻¹}
        ∘ (ρ⇒ ⊗₁ id {X ⁻¹})
        ∘ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹})
        ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹})
        ∘ (α⇒ ⊗₁ id {X ⁻¹})
        ∘ ((α⇐ ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
        ∘ α⇐
  nested-cap-coherence {A} {X} {Y} =
    (⟺ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
        ○ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
        ○ refl⟩∘⟨ sym-assoc
        ○ sym-assoc)
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-to-coherence)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ sym-assoc) ○ pullˡ (α-peel⊗id {A} {X} {Y} {Y ⁻¹} {X ⁻¹}) ○ assoc ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ assoc)))
    ○ (refl⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ sym-assoc) ○ pullˡ (α-inner {A} {X} {Y ⊗₀ Y ⁻¹} {Y ⁻¹ ⊗₀ Y} {X ⁻¹} {σ⇒ {Y} {Y ⁻¹}}) ○ assoc ○ (refl⟩∘⟨ assoc)))
    ○ (refl⟩∘⟨ ((refl⟩∘⟨ sym-assoc) ○ pullˡ (α-inner {A} {X} {Y ⁻¹ ⊗₀ Y} {unit} {X ⁻¹} {ε {Y}}) ○ assoc ○ (refl⟩∘⟨ assoc)))
    ○ ((refl⟩∘⟨ sym-assoc) ○ pullˡ (ρ-peel {A} {X} {X ⁻¹}) ○ assoc)

  nested-cap-core-split : ∀ {A X Y} →
    id {A} ⊗₁ nested-cap-core {X} {Y}
    ≈ (id {A} ⊗₁ (ρ⇒ ⊗₁ id {X ⁻¹}))
        ∘ (id {A} ⊗₁ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹}))
        ∘ (id {A} ⊗₁ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹}))
        ∘ (id {A} ⊗₁ (α⇒ ⊗₁ id {X ⁻¹}))
        ∘ (id {A} ⊗₁ α⇐ {X ⊗₀ Y} {Y ⁻¹} {X ⁻¹})
  nested-cap-core-split {A} {X} {Y} = begin
    id {A} ⊗₁ nested-cap-core {X} {Y}
      ≈⟨ split₂ˡ ⟩
    (id {A} ⊗₁ (ρ⇒ ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ (((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹})
        ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹})
        ∘ (α⇒ ⊗₁ id {X ⁻¹})
        ∘ α⇐ {X ⊗₀ Y} {Y ⁻¹} {X ⁻¹}))
      ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
    (id {A} ⊗₁ (ρ⇒ ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ (((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹})
        ∘ (α⇒ ⊗₁ id {X ⁻¹})
        ∘ α⇐ {X ⊗₀ Y} {Y ⁻¹} {X ⁻¹}))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩
    (id {A} ⊗₁ (ρ⇒ ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ ((α⇒ ⊗₁ id {X ⁻¹})
        ∘ α⇐ {X ⊗₀ Y} {Y ⁻¹} {X ⁻¹}))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩
    (id {A} ⊗₁ (ρ⇒ ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ (α⇒ ⊗₁ id {X ⁻¹}))
      ∘ (id {A} ⊗₁ α⇐ {X ⊗₀ Y} {Y ⁻¹} {X ⁻¹})
      ∎

nested-cap-factor : ∀ {A X Y} →
  (id {A} ⊗₁ nested-cap-core {X} {Y})
    ∘ α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
  ≈ α⇒ {A} {X} {X ⁻¹}
      ∘ (ρ⇒ ⊗₁ id {X ⁻¹})
      ∘ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹})
      ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ∘ (α⇒ ⊗₁ id {X ⁻¹})
      ∘ ((α⇐ ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ∘ α⇐
nested-cap-factor {A} {X} {Y} =
  begin
  (id {A} ⊗₁ nested-cap-core {X} {Y})
    ∘ α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ≈⟨ nested-cap-core-split {A} {X} {Y} ⟩∘⟨refl ⟩
  ((id {A} ⊗₁ (ρ⇒ ⊗₁ id {X ⁻¹}))
    ∘ (id {A} ⊗₁ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹}))
    ∘ (id {A} ⊗₁ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹}))
    ∘ (id {A} ⊗₁ (α⇒ ⊗₁ id {X ⁻¹}))
    ∘ (id {A} ⊗₁ α⇐ {X ⊗₀ Y} {Y ⁻¹} {X ⁻¹}))
    ∘ α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ≈⟨ nested-cap-coherence {A} {X} {Y} ⟩
  α⇒ {A} {X} {X ⁻¹}
    ∘ (ρ⇒ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹})
    ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹})
    ∘ (α⇒ ⊗₁ id {X ⁻¹}) ∘ ((α⇐ ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹}) ∘ α⇐
    ∎

private
  nested-cap-context-expand : ∀ {A X Y} →
    nested-cap-context {A} {X} {Y} ≈ iterated-cap {A} {X} {Y}
  nested-cap-context-expand {A} {X} {Y} = begin
    nested-cap-context {A} {X} {Y}
      ≈⟨ refl⟩∘⟨ split₂ˡ
           {f = id {A}}
           {g = ε {X}}
           {h = σ⇒ {X} {X ⁻¹} ∘ nested-cap-core {X} {Y}} ⟩∘⟨refl ⟩
    ρ⇒ {A} ∘ ((id {A} ⊗₁ ε {X})
      ∘ (id {A} ⊗₁ (σ⇒ {X} {X ⁻¹} ∘ nested-cap-core {X} {Y})))
      ∘ α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ split₂ˡ
           {f = id {A}}
           {g = σ⇒ {X} {X ⁻¹}}
           {h = nested-cap-core {X} {Y}}) ⟩∘⟨refl ⟩
    ρ⇒ {A} ∘ ((id {A} ⊗₁ ε {X})
      ∘ ((id {A} ⊗₁ σ⇒ {X} {X ⁻¹})
      ∘ (id {A} ⊗₁ nested-cap-core {X} {Y})))
      ∘ α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
      ≈⟨ refl⟩∘⟨ assoc ⟩
    ρ⇒ {A} ∘ (id {A} ⊗₁ ε {X})
      ∘ ((id {A} ⊗₁ σ⇒ {X} {X ⁻¹})
      ∘ (id {A} ⊗₁ nested-cap-core {X} {Y}))
      ∘ α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    ρ⇒ {A} ∘ (id {A} ⊗₁ ε {X}) ∘ (id {A} ⊗₁ σ⇒ {X} {X ⁻¹})
      ∘ (id {A} ⊗₁ nested-cap-core {X} {Y})
      ∘ α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ nested-cap-factor {A} {X} {Y} ⟩
    iterated-cap {A} {X} {Y}
      ∎

private
  α⊗-dual⇒ : ∀ {A X Y} →
    A ⊗₀ (X ⊗₀ (Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹))) ⇒ A ⊗₀ ((X ⊗₀ Y) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹))
  α⊗-dual⇒ {A} {X} {Y} =
    id {A} ⊗₁ α⇐ {X} {Y} {Y ⁻¹ ⊗₀ X ⁻¹}

  α-y-dual⇐ : ∀ {A X Y} →
    (A ⊗₀ X) ⊗₀ ((Y ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹) ⇒ (A ⊗₀ X) ⊗₀ (Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹))
  α-y-dual⇐ {A} {X} {Y} =
    id {A ⊗₀ X} ⊗₁ α⇒ {Y} {Y ⁻¹} {X ⁻¹}

  α⊗-dual⇐ : ∀ {A X Y} →
    A ⊗₀ (X ⊗₀ ((Y ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹)) ⇒ A ⊗₀ (X ⊗₀ (Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)))
  α⊗-dual⇐ {A} {X} {Y} =
    id {A} ⊗₁ (id {X} ⊗₁ α⇒ {Y} {Y ⁻¹} {X ⁻¹})

  cup-context : ∀ {A X Y Z} →
    Z ⇒ ((A ⊗₀ X) ⊗₀ (Y ⊗₀ Y ⁻¹)) ⊗₀ X ⁻¹ →
    Z ⇒ A ⊗₀ ((X ⊗₀ Y) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹))
  cup-context {A} {X} {Y} h =
    α⊗-dual⇒ {A} {X} {Y}
      ∘ α⇒ {A} {X} {Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)}
      ∘ α-y-dual⇐ {A} {X} {Y}
      ∘ α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
      ∘ h

  cup-context-grouped : ∀ {A X Y Z} →
    Z ⇒ ((A ⊗₀ X) ⊗₀ (Y ⊗₀ Y ⁻¹)) ⊗₀ X ⁻¹ →
    Z ⇒ A ⊗₀ ((X ⊗₀ Y) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹))
  cup-context-grouped {A} {X} {Y} h =
    (α⊗-dual⇒ {A} {X} {Y}
      ∘ α⇒ {A} {X} {Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)}
      ∘ α-y-dual⇐ {A} {X} {Y}
      ∘ α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹})
      ∘ h

  cup-context-assoc : ∀ {A X Y Z}
    {h : Z ⇒ ((A ⊗₀ X) ⊗₀ (Y ⊗₀ Y ⁻¹)) ⊗₀ X ⁻¹} →
    cup-context {A} {X} {Y} h ≈ cup-context-grouped {A} {X} {Y} h
  cup-context-assoc {A} {X} {Y} {h = h} = begin
    cup-context {A} {X} {Y} h
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    α⊗-dual⇒ {A} {X} {Y}
      ∘ α⇒ {A} {X} {Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)}
      ∘ ((α-y-dual⇐ {A} {X} {Y}
        ∘ α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹}) ∘ h)
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    α⊗-dual⇒ {A} {X} {Y}
      ∘ ((α⇒ {A} {X} {Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)}
        ∘ α-y-dual⇐ {A} {X} {Y}
        ∘ α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹}) ∘ h)
      ≈⟨ sym-assoc ⟩
    cup-context-grouped {A} {X} {Y} h
      ∎

  cup-cancel-from : ∀ {A X Y} →
    (((A ⊗₀ X) ⊗₀ Y) ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹
    ⇒ ((A ⊗₀ X) ⊗₀ (Y ⊗₀ Y ⁻¹)) ⊗₀ X ⁻¹
  cup-cancel-from {A} {X} {Y} = α⇒ {A ⊗₀ X} {Y} {Y ⁻¹} ⊗₁ id {X ⁻¹}

  cup-cancel-to : ∀ {A X Y} →
    ((A ⊗₀ X) ⊗₀ (Y ⊗₀ Y ⁻¹)) ⊗₀ X ⁻¹
    ⇒ (((A ⊗₀ X) ⊗₀ Y) ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹
  cup-cancel-to {A} {X} {Y} = α⇐ {A ⊗₀ X} {Y} {Y ⁻¹} ⊗₁ id {X ⁻¹}

  cup-spine : ∀ {A X Y} →
    A ⇒ ((A ⊗₀ X) ⊗₀ (Y ⊗₀ Y ⁻¹)) ⊗₀ X ⁻¹
  cup-spine {A} {X} {Y} =
    ((id {A ⊗₀ X} ⊗₁ η {Y}) ⊗₁ id {X ⁻¹}) ∘ (ρ⇐ ⊗₁ id {X ⁻¹})
      ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐

  cup-thread : ∀ {A X Y} →
      α⇒ {A} {X} {Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)}
        ∘ α-y-dual⇐ {A} {X} {Y}
        ∘ α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
        ∘ ((id ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
        ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐
    ≈ α⊗-dual⇐ {A} {X} {Y}
        ∘ (id {A} ⊗₁ (id {X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹})))
        ∘ (id {A} ⊗₁ (id {X} ⊗₁ λ⇐)) ∘ (id ⊗₁ η {X}) ∘ ρ⇐
  cup-thread {A} {X} {Y} =
    begin
    α⇒ {A} {X} {Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)}
      ∘ α-y-dual⇐ {A} {X} {Y}
      ∘ α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
      ∘ ((id ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈⟨ pullˡ (α-sweep
           {Y = A} {B = X}
           {P = (Y ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹}
           {Q = Y ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)}
           {k = α⇒ {Y} {Y ⁻¹} {X ⁻¹}}) ⟩
    ((id {A} ⊗₁ (id {X} ⊗₁ α⇒ {Y} {Y ⁻¹} {X ⁻¹}))
      ∘ α⇒ {A} {X} {(Y ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹})
      ∘ (α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
      ∘ ((id ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐)
      ≈⟨ assoc ⟩
    (id {A} ⊗₁ (id {X} ⊗₁ α⇒ {Y} {Y ⁻¹} {X ⁻¹}))
      ∘ α⇒ {A} {X} {(Y ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹}
      ∘ α⇒ {A ⊗₀ X} {Y ⊗₀ Y ⁻¹} {X ⁻¹}
      ∘ ((id ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ η-thread {A} {X} {Y} ⟩
    (id {A} ⊗₁ (id {X} ⊗₁ α⇒ {Y} {Y ⁻¹} {X ⁻¹}))
      ∘ α⇒ {A} {X} {(Y ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹}
      ∘ (id {A ⊗₀ X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹}))
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ η-thread₂ {A} {X} {Y} ⟩
    (id {A} ⊗₁ (id {X} ⊗₁ α⇒ {Y} {Y ⁻¹} {X ⁻¹}))
      ∘ (id {A} ⊗₁ (id {X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹})))
      ∘ α⇒ {A} {X} {unit ⊗₀ X ⁻¹}
      ∘ α⇒ {A ⊗₀ X} {unit} {X ⁻¹}
      ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ η-unit-thread {A} {X} ⟩
    α⊗-dual⇐ {A} {X} {Y}
      ∘ (id {A} ⊗₁ (id {X} ⊗₁ (η {Y} ⊗₁ id {X ⁻¹})))
      ∘ (id {A} ⊗₁ (id {X} ⊗₁ λ⇐)) ∘ (id ⊗₁ η {X}) ∘ ρ⇐
      ∎

  cup-cancel : ∀ {A X Y} →
    cup-context-grouped {A} {X} {Y} (cup-cancel-from {A} {X} {Y})
      ∘ (cup-cancel-to {A} {X} {Y} ∘ cup-spine {A} {X} {Y})
    ≈ cup-context-grouped {A} {X} {Y} (cup-spine {A} {X} {Y})
  cup-cancel {A} {X} {Y} = cancel-middle α⊗id-cancel

cup-fusion-coherence : ∀ {A X Y} →
  α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ∘ ((α⇒ {A} {X} {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ id {X ⁻¹})) ∘ α⇒)
    ∘ ((α⇐ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
       ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐)
  ≈ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ α⇒))
       ∘ (id ⊗₁ (id ⊗₁ (η {Y} ⊗₁ id))) ∘ (id ⊗₁ (id ⊗₁ λ⇐)) ∘ (id ⊗₁ η {X}) ∘ ρ⇐
cup-fusion-coherence {A} {X} {Y} =
  begin
  α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ∘ ((α⇒ {A} {X} {Y} ⊗₁ (id {Y ⁻¹} ⊗₁ id {X ⁻¹})) ∘ α⇒)
    ∘ ((α⇐ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
       ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐)
    ≈⟨ refl⟩∘⟨ ((refl⟩⊗⟨ id⊗id) ⟩∘⟨refl) ⟩∘⟨refl ⟩
  α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ∘ ((α⇒ {A} {X} {Y} ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇒)
    ∘ (cup-cancel-to {A} {X} {Y} ∘ cup-spine {A} {X} {Y})
    ≈⟨ sym-assoc ⟩
  (α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ∘ (α⇒ {A} {X} {Y} ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇒)
    ∘ (cup-cancel-to {A} {X} {Y} ∘ cup-spine {A} {X} {Y})
    ≈⟨ assoc-pair-coherence {A} {X} {Y} {Y ⁻¹} {X ⁻¹} ⟩∘⟨refl ⟩
  cup-context {A} {X} {Y} (cup-cancel-from {A} {X} {Y})
    ∘ (cup-cancel-to {A} {X} {Y} ∘ cup-spine {A} {X} {Y})
    ≈⟨ cup-context-assoc {A = A} {X = X} {Y = Y} {h = cup-cancel-from {A} {X} {Y}} ⟩∘⟨refl ⟩
  cup-context-grouped {A} {X} {Y} (cup-cancel-from {A} {X} {Y})
    ∘ (cup-cancel-to {A} {X} {Y} ∘ cup-spine {A} {X} {Y})
    ≈⟨ cup-cancel {A} {X} {Y} ⟩
  cup-context-grouped {A} {X} {Y} (cup-spine {A} {X} {Y})
    ≈˘⟨ cup-context-assoc {A = A} {X = X} {Y = Y} {h = cup-spine {A} {X} {Y}} ⟩
  cup-context {A} {X} {Y} (cup-spine {A} {X} {Y})
    ≈⟨ refl⟩∘⟨ cup-thread {A} {X} {Y} ⟩
  (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ α⇒))
    ∘ (id ⊗₁ (id ⊗₁ (η {Y} ⊗₁ id))) ∘ (id ⊗₁ (id ⊗₁ λ⇐)) ∘ (id ⊗₁ η {X}) ∘ ρ⇐
    ∎

iterated-cup : ∀ {A X Y} →
  A ⇒ (A ⊗₀ (X ⊗₀ Y)) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)
iterated-cup {A} {X} {Y} =
  α⇒ ∘ ((α⇒ {A} {X} {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
    ∘ (α⇐ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ η {Y}) ⊗₁ id {X ⁻¹})
    ∘ (ρ⇐ ⊗₁ id {X ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐

⊗-cup-context : ∀ {A X Y} →
  A ⇒ (A ⊗₀ (X ⊗₀ Y)) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹)
⊗-cup-context {A} {X} {Y} =
  α⇐ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ∘ (id ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐

⊗-cup-fusion : ∀ {A X Y} →
  iterated-cup {A} {X} {Y} ≈ ⊗-cup-context {A} {X} {Y}
⊗-cup-fusion {A} {X} {Y} = begin
  iterated-cup {A} {X} {Y}
    ≈⟨ pullˡ assoc-commute-from
      ○ (insertˡ (associator.isoˡ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹})
          ○ refl⟩∘⟨ cup-fusion-coherence {A} {X} {Y})
      ○ refl⟩∘⟨ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
        ○ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
        ○ refl⟩∘⟨ sym-assoc
        ○ sym-assoc)
      ○ ⟺ (refl⟩∘⟨ (split₂ˡ ○ (refl⟩∘⟨ split₂ˡ) ○ (refl⟩∘⟨ refl⟩∘⟨ split₂ˡ)
          ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ)) ⟩∘⟨refl) ⟩
  ⊗-cup-context {A} {X} {Y}
    ∎

⊗-cap-context : ∀ {A X Y} →
  (A ⊗₀ (X ⊗₀ Y)) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹) ⇒ A
⊗-cap-context {A} {X} {Y} =
  ρ⇒ {A} ∘ (id ⊗₁ ⊗-cap {X} {Y})
    ∘ (id ⊗₁ σ⇒ {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇒

⊗-cap-transport : ∀ {X Y} →
  (ε {X ⊗₀ Y} ∘ σ⇒ {X ⊗₀ Y} {(X ⊗₀ Y) ⁻¹})
    ∘ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y})
  ≈ ⊗-cap {X} {Y} ∘ σ⇒ {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
⊗-cap-transport {X} {Y} =
  begin
  (ε {X ⊗₀ Y} ∘ σ⇒ {X ⊗₀ Y} {(X ⊗₀ Y) ⁻¹})
    ∘ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y})
    ≈⟨ pullʳ (braiding.⇒.commute (id , ⊗-dual⇒ {X} {Y})) ⟩
  ε {X ⊗₀ Y}
    ∘ (⊗-dual⇒ {X} {Y} ⊗₁ id {X ⊗₀ Y})
    ∘ σ⇒ {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ≈⟨ pullˡ (⊗-dual-cap {X} {Y}) ⟩
  ⊗-cap {X} {Y} ∘ σ⇒ {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ∎

middle-four-braid : ∀ {X Y} →
  (X ⊗₀ Y) ⊗₀ (Y ⁻¹ ⊗₀ X ⁻¹) ⇒ (Y ⁻¹ ⊗₀ X ⁻¹) ⊗₀ (X ⊗₀ Y)
middle-four-braid {X} {Y} =
  swapInner.from {Y ⁻¹} {X} {X ⁻¹} {Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ∘ swapInner.from {X} {Y} {Y ⁻¹} {X ⁻¹}

middle-cap-core : ∀ {X Y} →
  (Y ⁻¹ ⊗₀ X ⁻¹) ⊗₀ (X ⊗₀ Y) ⇒ Y ⁻¹ ⊗₀ Y
middle-cap-core {X} {Y} =
  ((ρ⇒ ⊗₁ id {Y}) ∘ ((id {Y ⁻¹} ⊗₁ ε {X}) ⊗₁ id {Y}))
    ∘ (α⇒ {Y ⁻¹} {X ⁻¹} {X} ⊗₁ id {Y})
    ∘ α⇐ {Y ⁻¹ ⊗₀ X ⁻¹} {X} {Y}

middle-cap : ∀ {X Y} →
  (Y ⁻¹ ⊗₀ X ⁻¹) ⊗₀ (X ⊗₀ Y) ⇒ unit
middle-cap {X} {Y} = ε {Y} ∘ middle-cap-core {X} {Y}

middle-cap-factor : ∀ {X Y} →
  ε {Y} ∘ (id ⊗₁ ξ {X} {Y}) ∘ α⇒
    ≈ middle-cap {X} {Y}
middle-cap-factor {X} {Y} = begin
  ε {Y} ∘ (id ⊗₁ ξ {X} {Y}) ∘ α⇒
    ≈⟨ refl⟩∘⟨ cap-reassoc {A = Y ⁻¹} {P = X ⁻¹} {Q = X} {B = Y} {cap = ε {X}} ⟩
  middle-cap {X} {Y}
    ∎

private
  split-capʳ : ∀ {X Y} →
    (id {X} ⊗₁ capʳ {Y}) ⊗₁ id {X ⁻¹}
    ≈ ((id {X} ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹})
        ∘ ((id {X} ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹})
  split-capʳ {X} {Y} =
    begin
    (id {X} ⊗₁ capʳ {Y}) ⊗₁ id {X ⁻¹}
      ≈⟨ split₂ˡ {f = id {X}} {g = ε {Y}} {h = σ⇒ {Y} {Y ⁻¹}} ⟩⊗⟨refl ⟩
    ((id {X} ⊗₁ ε {Y}) ∘ (id {X} ⊗₁ σ⇒ {Y} {Y ⁻¹})) ⊗₁ id {X ⁻¹}
      ≈⟨ split₁ʳ ⟩
    ((id {X} ⊗₁ ε {Y}) ⊗₁ id {X ⁻¹})
      ∘ ((id {X} ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ∎

mid-cap-coreʳ : ∀ {X Y} →
  mid-capʳ {A = X} {X = Y} {B = X ⁻¹}
  ≈ nested-cap-core {X} {Y}
mid-cap-coreʳ {X} {Y} = begin
  mid-capʳ {A = X} {X = Y} {B = X ⁻¹}
    ≈⟨ assoc ⟩
  (ρ⇒ ⊗₁ id {X ⁻¹})
    ∘ ((id {X} ⊗₁ capʳ {Y}) ⊗₁ id {X ⁻¹})
    ∘ (α⇒ {X} {Y} {Y ⁻¹} ⊗₁ id {X ⁻¹})
    ∘ α⇐ {X ⊗₀ Y} {Y ⁻¹} {X ⁻¹}
    ≈⟨ push-center (split-capʳ {X} {Y}) ⟩
  nested-cap-core {X} {Y}
    ∎

middle-cap-swapInner : ∀ {X Y} →
  middle-cap {X} {Y}
    ∘ swapInner.from {Y ⁻¹} {X} {X ⁻¹} {Y}
  ≈ ε {Y} ∘ mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
middle-cap-swapInner {X} {Y} =
  begin
  middle-cap {X} {Y} ∘ swapInner.from {Y ⁻¹} {X} {X ⁻¹} {Y}
    ≈⟨ assoc ⟩
  ε {Y} ∘ middle-cap-core {X} {Y} ∘ swapInner.from {Y ⁻¹} {X} {X ⁻¹} {Y}
    ≈⟨ refl⟩∘⟨ mid-swapInnerˡ {A = Y ⁻¹} {X = X} {B = Y} ⟩
  ε {Y} ∘ mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∎

nested-cap-swapInner : ∀ {X Y} →
  capʳ {X}
    ∘ mid-capˡ {A = X} {X = Y} {B = X ⁻¹}
    ∘ swapInner.from {X} {Y} {Y ⁻¹} {X ⁻¹}
  ≈ nested-cap {X} {Y}
nested-cap-swapInner {X} {Y} =
  begin
  capʳ {X} ∘ mid-capˡ {A = X} {X = Y} {B = X ⁻¹}
    ∘ swapInner.from {X} {Y} {Y ⁻¹} {X ⁻¹}
    ≈⟨ refl⟩∘⟨ mid-swapInnerˡ {A = X} {X = Y} {B = X ⁻¹} ⟩
  capʳ {X} ∘ mid-capʳ {A = X} {X = Y} {B = X ⁻¹}
    ≈⟨ refl⟩∘⟨ mid-cap-coreʳ {X} {Y} ⟩
  capʳ {X} ∘ nested-cap-core {X} {Y}
    ≈⟨ assoc ⟩
  nested-cap {X} {Y}
    ∎

middle-four-cap : ∀ {X Y} →
  nested-cap {X} {Y} ≈ middle-cap {X} {Y} ∘ middle-four-braid {X} {Y}
middle-four-cap {X} {Y} =
  begin
  nested-cap {X} {Y}
    ≈˘⟨ nested-cap-swapInner {X} {Y} ⟩
  capʳ {X} ∘ mid-capˡ {A = X} {X = Y} {B = X ⁻¹}
    ∘ swapInner.from {X} {Y} {Y ⁻¹} {X ⁻¹}
    ≈˘⟨ assoc ⟩
  (capʳ {X} ∘ mid-capˡ {A = X} {X = Y} {B = X ⁻¹})
    ∘ swapInner.from {X} {Y} {Y ⁻¹} {X ⁻¹}
    ≈˘⟨ paired-cap-interchangeʳ {X} {Y} ⟩∘⟨refl ⟩
  (ε {Y} ∘ mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹}))
    ∘ swapInner.from {X} {Y} {Y ⁻¹} {X ⁻¹}
    ≈⟨ assoc ⟩
  ε {Y} ∘ ((mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹}))
    ∘ swapInner.from {X} {Y} {Y ⁻¹} {X ⁻¹})
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ε {Y} ∘ mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ∘ swapInner.from {X} {Y} {Y ⁻¹} {X ⁻¹}
    ≈˘⟨ assoc ⟩
  (ε {Y} ∘ mid-capʳ {A = Y ⁻¹} {X = X} {B = Y})
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ∘ swapInner.from {X} {Y} {Y ⁻¹} {X ⁻¹}
    ≈˘⟨ middle-cap-swapInner {X} {Y} ⟩∘⟨refl ⟩
  (middle-cap {X} {Y} ∘ swapInner.from {Y ⁻¹} {X} {X ⁻¹} {Y})
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ∘ swapInner.from {X} {Y} {Y ⁻¹} {X ⁻¹}
    ≈⟨ assoc ⟩
  middle-cap {X} {Y} ∘ middle-four-braid {X} {Y}
    ∎

middle-four-cap-fusion : ∀ {X Y} →
  nested-cap {X} {Y}
    ≈ (ε {Y} ∘ (id ⊗₁ ξ {X} {Y}) ∘ α⇒) ∘ middle-four-braid {X} {Y}
middle-four-cap-fusion {X} {Y} =
  begin
  nested-cap {X} {Y}
    ≈⟨ middle-four-cap {X} {Y} ⟩
  middle-cap {X} {Y} ∘ middle-four-braid {X} {Y}
    ≈˘⟨ middle-cap-factor {X} {Y} ⟩∘⟨refl ⟩
  (ε {Y} ∘ (id ⊗₁ ξ {X} {Y}) ∘ α⇒) ∘ middle-four-braid {X} {Y}
    ∎

nested-cap-fusion : ∀ {X Y} →
  nested-cap {X} {Y} ≈ ⊗-cap {X} {Y} ∘ σ⇒ {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
nested-cap-fusion {X} {Y} =
  begin
  nested-cap {X} {Y}
    ≈⟨ middle-four-cap-fusion {X} {Y} ⟩
  (ε {Y} ∘ (id ⊗₁ ξ {X} {Y}) ∘ α⇒) ∘ middle-four-braid {X} {Y}
    ≈˘⟨ cap-factor {X} {Y} ⟩∘⟨refl ⟩
  ⊗-cap {X} {Y} ∘ middle-four-braid {X} {Y}
    ≈⟨ refl⟩∘⟨ swapInner-braiding {W = X} {X = Y} {Y = Y ⁻¹} {Z = X ⁻¹} ⟩
  ⊗-cap {X} {Y} ∘ σ⇒ {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ∎

⊗-cap-fusion : ∀ {A X Y} →
  iterated-cap {A} {X} {Y} ≈ ⊗-cap-context {A} {X} {Y}
⊗-cap-fusion {A} {X} {Y} =
  begin
  iterated-cap {A} {X} {Y}
    ≈˘⟨ nested-cap-context-expand {A} {X} {Y} ⟩
  nested-cap-context {A} {X} {Y}
    ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ nested-cap-fusion {X} {Y}) ⟩∘⟨refl ⟩
  ρ⇒ {A} ∘ (id {A} ⊗₁ (⊗-cap {X} {Y} ∘ σ⇒ {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}))
    ∘ α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
  ρ⇒ {A} ∘ ((id {A} ⊗₁ ⊗-cap {X} {Y}) ∘ (id {A} ⊗₁ σ⇒ {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}))
    ∘ α⇒ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ⊗-cap-context {A} {X} {Y}
    ∎
