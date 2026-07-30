{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Opposites of enriched functors.

module Categories.Enriched.Functor.Opposite
  {o ℓ e} {V : Category o ℓ e} {M : Monoidal V} (S : Symmetric M) where

import Categories.Enriched.Category as Enriched
import Categories.Enriched.Category.Opposite as Opposite

open Category V
open HomReasoning
open Monoidal M
open Symmetric S using (braided; commutative)
open import Categories.Category.Monoidal.Braided.Properties braided using (module Shorthands)
open import Categories.Enriched.Category M using (_[_,_])
open import Categories.Enriched.Functor M using (Functor)
open import Categories.Enriched.Category.Opposite S renaming (op to opE)
open import Categories.Morphism.Reasoning V
open Shorthands

opF : ∀ {c d} {𝒞 : Enriched.Category M c} {𝒟 : Enriched.Category M d} →
  Functor 𝒞 𝒟 → Functor (Opposite.op S 𝒞) (Opposite.op S 𝒟)
opF {𝒞 = 𝒞} {𝒟} F = record
  { map₀ = F.₀
  ; map₁ = F.₁
  ; identity = op-identity
  ; homomorphism = op-homomorphism
  }
  where
  module 𝒞 = Enriched.Category 𝒞
  module 𝒟 = Enriched.Category 𝒟
  module F = Functor F

  abstract
    op-identity : ∀ {X} →
      F.₁ {X = X} ∘ 𝒞.id ≈ 𝒟.id
    op-identity = F.identity

    op-homomorphism : ∀ {X Y Z} →
      F.₁ {X = Z} {Y = X} ∘ (𝒞.⊚ {A = Z} {B = Y} {C = X} ∘ σ⇒)
      ≈ (𝒟.⊚ ∘ σ⇒) ∘ (F.₁ ⊗₁ F.₁)
    op-homomorphism = begin
      F.₁ ∘ (𝒞.⊚ ∘ σ⇒)                  ≈⟨ pullˡ F.homomorphism ⟩
      (𝒟.⊚ ∘ (F.₁ ⊗₁ F.₁)) ∘ σ⇒         ≈⟨ extendˡ (⟺ σ⇒-comm) ⟩
      (𝒟.⊚ ∘ σ⇒) ∘ (F.₁ ⊗₁ F.₁)         ∎

op²F : ∀ {c} {𝒞 : Enriched.Category M c} → Functor 𝒞 (opE (opE 𝒞))
op²F {𝒞 = 𝒞} = record
  { map₀ = λ X → X
  ; map₁ = id
  ; identity = op²-identity
  ; homomorphism = op²-homomorphism
  }
  where
  module 𝒞 = Enriched.Category 𝒞

  abstract
    op²-identity : ∀ {X} → id ∘ 𝒞.id {X} ≈ 𝒞.id
    op²-identity = identityˡ

    op²-homomorphism : ∀ {X Y Z} →
      id ∘ 𝒞.⊚ {A = X} {B = Y} {C = Z}
      ≈ ((𝒞.⊚ ∘ σ⇒) ∘ σ⇒) ∘ (id ⊗₁ id)
    op²-homomorphism = begin
      id ∘ 𝒞.⊚                        ≈⟨ identityˡ ⟩
      𝒞.⊚                             ≈⟨ introʳ commutative ⟩
      𝒞.⊚ ∘ σ⇒ ∘ σ⇒                   ≈⟨ sym-assoc ⟩
      (𝒞.⊚ ∘ σ⇒) ∘ σ⇒                 ≈⟨ introʳ ⊗.identity ⟩
      ((𝒞.⊚ ∘ σ⇒) ∘ σ⇒) ∘ (id ⊗₁ id)  ∎
