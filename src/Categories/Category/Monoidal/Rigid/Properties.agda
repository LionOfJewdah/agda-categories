{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Category.Monoidal.Rigid.Properties
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) where

import Categories.Category.Monoidal.Rigid M as Rigid
open Rigid using (LeftRigid; RightRigid)
import Categories.Category.Monoidal.Rigid as RigidModule
import Categories.Category.Monoidal.Rigid.Dual as RigidDual
import Categories.Category.Monoidal.Rigid.TensorDual as RigidTensorDual
open import Categories.Morphism.Reasoning C
open import Categories.Category.Monoidal.Properties M
  using (monoidal-Op)

open Category C
open Monoidal M
open HomReasoning

rigidʳ-Op : RightRigid → RigidModule.LeftRigid monoidal-Op
rigidʳ-Op R = record
  { _⁻¹ = Rigid.RightRigid._⁻¹ R
  ; η = Rigid.RightRigid.ε R
  ; ε = Rigid.RightRigid.η R
  ; snake₁ = assoc²αε ○ assoc ○ Rigid.RightRigid.snake₁ R
  ; snake₂ = assoc²αε ○ assoc ○ Rigid.RightRigid.snake₂ R
  }

rigidˡ-Op : LeftRigid → RigidModule.RightRigid monoidal-Op
rigidˡ-Op R = record
  { _⁻¹ = Rigid.LeftRigid._⁻¹ R
  ; η = Rigid.LeftRigid.ε R
  ; ε = Rigid.LeftRigid.η R
  ; snake₁ = assoc²αε ○ assoc ○ Rigid.LeftRigid.snake₁ R
  ; snake₂ = assoc²αε ○ assoc ○ Rigid.LeftRigid.snake₂ R
  }

module Left (R : LeftRigid) where
  open LeftRigid R using (_⁻¹; η; ε)
  open import Categories.Category.Monoidal.Rigid.Dual M R
    using (cap-ᵀ; cap-ᵀ-counit; cap-ᵀ-cup; cup-ᵀ; cup-ᵀ⇒)
  open import Categories.Category.Monoidal.Rigid.TensorDual M R
    using (⊗-cap; ⊗-cup; ⊗-snakeˡ)

  ⊗-dual⇒ : ∀ {X Y} → Y ⁻¹ ⊗₀ X ⁻¹ ⇒ (X ⊗₀ Y) ⁻¹
  ⊗-dual⇒ {X} {Y} = cap-ᵀ (⊗-cap {X} {Y})

  ⊗-dual⇐ : ∀ {X Y} → (X ⊗₀ Y) ⁻¹ ⇒ Y ⁻¹ ⊗₀ X ⁻¹
  ⊗-dual⇐ {X} {Y} = cup-ᵀ⇒ (⊗-cup {X} {Y})

  ⊗-dual-cup : ∀ {X Y} →
    (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇐ {X} {Y}) ∘ η {X ⊗₀ Y}
    ≈ ⊗-cup {X} {Y}
  ⊗-dual-cup {X} {Y} = cup-ᵀ (⊗-cup {X} {Y})

  ⊗-dual-cup⇒ : ∀ {X Y} →
    (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}) ∘ ⊗-cup {X} {Y}
    ≈ η {X ⊗₀ Y}
  ⊗-dual-cup⇒ {X} {Y} = cap-ᵀ-cup (⊗-snakeˡ {X} {Y})

  ⊗-dual-cap : ∀ {X Y} →
    ε {X ⊗₀ Y} ∘ (⊗-dual⇒ {X} {Y} ⊗₁ id {X ⊗₀ Y})
    ≈ ⊗-cap {X} {Y}
  ⊗-dual-cap {X} {Y} = cap-ᵀ-counit (⊗-cap {X} {Y})

module Right (R : RightRigid) where
  leftRigid-Op : RigidModule.LeftRigid monoidal-Op
  leftRigid-Op = rigidʳ-Op R

  module Dual = RigidDual monoidal-Op leftRigid-Op
  module TensorDual = RigidTensorDual monoidal-Op leftRigid-Op

  open Dual public
  open TensorDual public
