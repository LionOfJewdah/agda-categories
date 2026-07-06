{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Extra identities that hold only for symmetric monoidal categories.

module Categories.Category.Monoidal.Interchange.Symmetric
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (S : Symmetric M) where

open import Data.Product using (_,_)

import Categories.Category.Construction.Core C as Core
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
open import Categories.Category.Monoidal.Interchange using (HasInterchange)
import Categories.Category.Monoidal.Interchange.Braided as BraidedInterchange
  using (module swapInner; swapInner-braiding; swapˡ; swapˡ-hexagon)
import Categories.Category.Monoidal.Reasoning M as MonoidalReasoning
import Categories.Category.Monoidal.Utilities M as MonoidalUtilities
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (_≃_; niHelper)
open import Categories.Morphism.IsoEquiv C using (to-unique)
open import Categories.Morphism.Reasoning C
  using (elim-center; pushˡ; pullʳ; cancelInner; switch-fromtoˡ)

open Category C using
  ( Obj; _⇒_; _≈_; _∘_; id
  ; assoc; sym-assoc; identity²; identityʳ; ∘-resp-≈ʳ; module Equiv
  )
open Commutation C
open MonoidalReasoning
open MonoidalUtilities using (_⊗ᵢ_)
open Symmetric S renaming (associator to α; braided to B)
open BraidedInterchange B
open Core.Shorthands               -- for idᵢ, _∘ᵢ_, ...
open MonoidalUtilities.Shorthands  -- for λ⇒, ρ⇒, α⇒, ...
open BraidedProps.Shorthands B     -- for σ⇒, ...

private
  variable
    W W₁ W₂ X X₁ X₂ Y Y₁ Y₂ Z Z₁ Z₂ : Obj
    f g h i : X ⇒ Y

private
  i⇒ = swapInner.from
  i⇐ = swapInner.to

private
  id⊗σ-cancelʳ : ∀ {X Y Z} →
    ((id {X} ⊗₁ σ⇒ {Y} {Z}) ∘ (id {X} ⊗₁ σ⇒ {Z} {Y})) ≈ id
  id⊗σ-cancelʳ {X} {Y} {Z} = begin
    (id {X} ⊗₁ σ⇒ {Y} {Z}) ∘ (id {X} ⊗₁ σ⇒ {Z} {Y})
      ≈˘⟨ ⊗-distrib-over-∘ ⟩
    (id {X} ∘ id {X}) ⊗₁ (σ⇒ {Y} {Z} ∘ σ⇒ {Z} {Y})
      ≈⟨ identity² ⟩⊗⟨ commutative ⟩
    id {X} ⊗₁ id {Z ⊗₀ Y}
      ≈⟨ ⊗.identity ⟩
    id
      ∎

  σ-cancelʳ : ∀ {X Y} →
    (σ⇒ {Y} {X} ∘ σ⇒ {X} {Y}) ≈ id {X ⊗₀ Y}
  σ-cancelʳ {X} {Y} = commutative {X = Y} {Y = X}

  σ-cancel²ʳ : ∀ {X Y} →
    (σ⇒ {Y} {X} ∘ σ⇒ {X} {Y}) ≈ id {X ⊗₀ Y} ∘ id
  σ-cancel²ʳ {X} {Y} = begin
    σ⇒ {Y} {X} ∘ σ⇒ {X} {Y}
      ≈⟨ σ-cancelʳ {X} {Y} ⟩
    id {X ⊗₀ Y}
      ≈˘⟨ identity² ⟩
    id {X ⊗₀ Y} ∘ id
      ∎

  σ⊗σ-cancelʳ : ∀ {W X Y Z} →
    ((σ⇒ {W} {X} ⊗₁ σ⇒ {Z} {Y})
      ∘ (id {W ⊗₀ X} ⊗₁ σ⇒ {Y} {Z}))
    ≈ σ⇒ {W} {X} ⊗₁ id {Y ⊗₀ Z}
  σ⊗σ-cancelʳ {W} {X} {Y} {Z} = begin
    (σ⇒ {W} {X} ⊗₁ σ⇒ {Z} {Y})
      ∘ (id {W ⊗₀ X} ⊗₁ σ⇒ {Y} {Z})
      ≈⟨ parallel
        {f₁ = σ⇒ {W} {X}} {f₂ = σ⇒ {W} {X}}
        {g₁ = σ⇒ {Z} {Y}} {g₂ = id {Y ⊗₀ Z}}
        {h₁ = id {W ⊗₀ X}} {h₂ = id {W ⊗₀ X}}
        {i₁ = σ⇒ {Y} {Z}} {i₂ = id {Y ⊗₀ Z}}
        Equiv.refl (σ-cancel²ʳ {Y} {Z}) ⟩
    (σ⇒ {W} {X} ⊗₁ id {Y ⊗₀ Z})
      ∘ (id {W ⊗₀ X} ⊗₁ id {Y ⊗₀ Z})
      ≈⟨ refl⟩∘⟨ ⊗.identity ⟩
    (σ⇒ {W} {X} ⊗₁ id {Y ⊗₀ Z}) ∘ id
      ≈⟨ identityʳ ⟩
    σ⇒ {W} {X} ⊗₁ id {Y ⊗₀ Z}
      ∎

swapˡ-cancelʳ : ∀ {X Y Z} →
                 ((σ⇒ {X ⊗₀ Y} {Z} ∘ α⇐ {X} {Y} {Z})
                   ∘ (id {X} ⊗₁ σ⇒ {Z} {Y}))
                 ≈ swapˡ {X} {Z} {Y}
swapˡ-cancelʳ {X} {Y} {Z} = begin
  (σ⇒ {X ⊗₀ Y} {Z} ∘ α⇐) ∘ id {X} ⊗₁ σ⇒ {Z} {Y}
    ≈⟨ swapˡ-hexagon {X} {Y} {Z} ⟩∘⟨refl ⟩
  (swapˡ {X} {Z} {Y} ∘ id {X} ⊗₁ σ⇒ {Y} {Z})
    ∘ id {X} ⊗₁ σ⇒ {Z} {Y}
    ≈⟨ assoc ⟩
  swapˡ {X} {Z} {Y}
    ∘ ((id {X} ⊗₁ σ⇒ {Y} {Z}) ∘ id {X} ⊗₁ σ⇒ {Z} {Y})
    ≈⟨ refl⟩∘⟨ id⊗σ-cancelʳ {X} {Y} {Z} ⟩
  swapˡ {X} {Z} {Y} ∘ id
    ≈⟨ identityʳ ⟩
  swapˡ {X} {Z} {Y}
    ∎

swapInner-commutative : [ (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ⇒
                          (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ]⟨
                           i⇒    ⇒⟨ (X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂) ⟩
                           i⇒
                        ≈ id
                        ⟩
swapInner-commutative = begin
    i⇒ ∘ i⇒                                                               ≈⟨ pullʳ (cancelInner α.isoʳ) ⟩
    α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒  ≈˘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    α⇐ ∘ id ⊗₁ ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ ∘-resp-≈ʳ sym-assoc ⟩∘⟨refl ⟩
    α⇐ ∘ id ⊗₁ ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ (α⇒ ∘ σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ α[σ⊗1]α⁻¹.isoʳ ⟩∘⟨refl ⟩
    α⇐ ∘ id ⊗₁ id ∘ α⇒                                                    ≈⟨ elim-center ⊗.identity ⟩
    α⇐ ∘ α⇒                                                               ≈⟨ α.isoˡ ⟩
    id                                                                     ∎
  where module α[σ⊗1]α⁻¹ = _≅_ (α ∘ᵢ braided-iso ⊗ᵢ idᵢ ∘ᵢ α ⁻¹) using (isoʳ)

swapInner-iso : (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ≅ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z)
swapInner-iso = record
  { from = i⇒
  ; to   = i⇒
  ; iso  = record
    { isoˡ = swapInner-commutative
    ; isoʳ = swapInner-commutative
    }
  }

swapInner-selfInverse : [ (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ⇒
                          (X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂) ]⟨
                          i⇒
                        ≈ i⇐
                        ⟩
swapInner-selfInverse =
  to-unique (iso swapInner-iso) swapInner.iso Equiv.refl

swapInner-braiding′ : [ (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ⇒ (Y ⊗₀ W) ⊗₀ (Z ⊗₀ X) ]⟨
                        i⇒         ⇒⟨ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z) ⟩
                        σ⇒ ⊗₁ σ⇒
                      ≈ σ⇒         ⇒⟨ (Y ⊗₀ Z) ⊗₀ (W ⊗₀ X) ⟩
                        i⇒
                      ⟩
swapInner-braiding′ = switch-fromtoˡ swapInner-iso swapInner-braiding

swapInner-braidˡ : ∀ {W X Y Z} →
  swapInner.from {X} {W} {Y} {Z} ∘ (σ⇒ {W} {X} ⊗₁ id {Y ⊗₀ Z})
  ≈ σ⇒ {W ⊗₀ Z} {X ⊗₀ Y}
      ∘ swapInner.from {W} {X} {Z} {Y}
      ∘ (id {W ⊗₀ X} ⊗₁ σ⇒ {Y} {Z})
swapInner-braidˡ {W} {X} {Y} {Z} = Equiv.sym (begin
  σ⇒ {W ⊗₀ Z} {X ⊗₀ Y}
    ∘ swapInner.from {W} {X} {Z} {Y}
    ∘ (id {W ⊗₀ X} ⊗₁ σ⇒ {Y} {Z})
    ≈˘⟨ assoc ⟩
  (σ⇒ {W ⊗₀ Z} {X ⊗₀ Y}
    ∘ swapInner.from {W} {X} {Z} {Y})
    ∘ (id {W ⊗₀ X} ⊗₁ σ⇒ {Y} {Z})
    ≈⟨ ((⟺ (swapInner-braiding {W = W} {X = Z} {Y = X} {Z = Y}))
        ⟩∘⟨refl) ⟩∘⟨refl ⟩
  ((swapInner.from {X} {W} {Y} {Z}
    ∘ (σ⇒ {W} {X} ⊗₁ σ⇒ {Z} {Y})
    ∘ swapInner.from {W} {Z} {X} {Y})
    ∘ swapInner.from {W} {X} {Z} {Y})
    ∘ (id {W ⊗₀ X} ⊗₁ σ⇒ {Y} {Z})
    ≈⟨ ((sym-assoc ⟩∘⟨refl)
        ○ pullʳ (swapInner-commutative {X₁ = W} {X₂ = X} {Y₁ = Z} {Y₂ = Y})
        ○ identityʳ) ⟩∘⟨refl ⟩
  (swapInner.from {X} {W} {Y} {Z}
    ∘ (σ⇒ {W} {X} ⊗₁ σ⇒ {Z} {Y}))
    ∘ (id {W ⊗₀ X} ⊗₁ σ⇒ {Y} {Z})
    ≈⟨ assoc ⟩
  swapInner.from {X} {W} {Y} {Z}
    ∘ ((σ⇒ {W} {X} ⊗₁ σ⇒ {Z} {Y})
      ∘ (id {W ⊗₀ X} ⊗₁ σ⇒ {Y} {Z}))
    ≈⟨ refl⟩∘⟨ σ⊗σ-cancelʳ {W} {X} {Y} {Z} ⟩
  swapInner.from {X} {W} {Y} {Z}
    ∘ (σ⇒ {W} {X} ⊗₁ id {Y ⊗₀ Z})
    ∎)
