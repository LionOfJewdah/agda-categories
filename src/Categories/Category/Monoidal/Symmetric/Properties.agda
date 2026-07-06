{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Category.Monoidal.Symmetric.Properties
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (SM : Symmetric M) where

import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
import Categories.Category.Monoidal.Utilities M as MonoidalUtilities

open import Categories.Category.Monoidal.Properties M using (monoidal-Op)
open import Categories.Morphism.Reasoning C
open import Data.Product using (_,_)

open Category C
open HomReasoning
open Symmetric SM

-- Shorthands for the braiding

open BraidedProperties braided public using (Obj-⊗-Comm-Monoid; module Shorthands)
open BraidedProperties braided using (inv-braiding-coherence)
open MonoidalUtilities.Shorthands using (λ⇒; ρ⇒; ρ⇐)
open Shorthands using (σ⇒; σ⇐)

-- Extra properties of the braiding in a symmetric monoidal category

braiding-selfInverse : ∀ {X Y} → braiding.⇐.η (X , Y) ≈ braiding.⇒.η (Y , X)
braiding-selfInverse {X} {Y} = begin
  braiding.⇐.η (X , Y)                                      ≈⟨ introʳ commutative ⟩
  braiding.⇐.η (X , Y) ∘ braiding.⇒.η (X , Y) ∘ braiding.⇒.η (Y , X)
                                                               ≈⟨ cancelˡ (braiding.iso.isoˡ _) ⟩
  braiding.⇒.η (Y , X)                                      ∎

inv-commutative : ∀ {X Y} → braiding.⇐.η (X , Y) ∘ braiding.⇐.η (Y , X) ≈ id
inv-commutative {X} {Y} = begin
  braiding.⇐.η (X , Y) ∘ braiding.⇐.η (Y , X)  ≈⟨ ∘-resp-≈ braiding-selfInverse braiding-selfInverse ⟩
  braiding.⇒.η (Y , X) ∘ braiding.⇒.η (X , Y)  ≈⟨ commutative ⟩
  id                                           ∎

braiding-coherenceˡ-inv : ∀ {X} → σ⇒ {unit} {X} ≈ ρ⇐ ∘ λ⇒
braiding-coherenceˡ-inv {X} = begin
  σ⇒ {unit} {X}                ≈˘⟨ braiding-selfInverse {X = X} {Y = unit} ⟩
  σ⇐ {X} {unit}                ≈˘⟨ identityˡ ⟩
  id ∘ σ⇐ {X} {unit}           ≈˘⟨ unitorʳ.isoˡ ⟩∘⟨refl ⟩
  (ρ⇐ ∘ ρ⇒) ∘ σ⇐ {X} {unit}    ≈⟨ assoc ⟩
  ρ⇐ ∘ (ρ⇒ ∘ σ⇐ {X} {unit})    ≈⟨ refl⟩∘⟨ inv-braiding-coherence {X = X} ⟩
  ρ⇐ ∘ λ⇒                      ∎

-- The opposite monoidal category is symmetric

open BraidedProperties braided using (braided-Op)

symmetric-Op : Symmetric monoidal-Op
symmetric-Op = record
    { braided = braided-Op
    ; commutative = inv-commutative
    }
