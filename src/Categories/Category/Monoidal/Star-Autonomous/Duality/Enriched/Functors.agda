{-# OPTIONS --without-K --safe --lossy-unification #-}

-- --lossy-unification keeps enriched functor composition under 4s instead of over 1min.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Enriched dualization and its action on named morphisms.

module Categories.Category.Monoidal.Star-Autonomous.Duality.Enriched.Functors
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (S : Symmetric M) (Cl : Closed M) where

import Categories.Enriched.Category as Enriched
import Categories.Morphism as Morphism

open Category 𝒞
open Monoidal M
open Symmetric S using (braided)
open Closed Cl using ([_,_]₀)

open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Closed.Currying Cl
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment S Cl
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Symmetric.Properties S using (unitʳ-braiding)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Category.Opposite S renaming (op to opE)
open import Categories.Enriched.Category.Underlying M using (Underlying)
open import Categories.Enriched.Functor M
  using (Functor; Endofunctor; UnderlyingFunctor; _∘F_)
open import Categories.Enriched.Functor.Opposite S using (opF; op²F)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism; niHelper)
open import Categories.Enriched.NaturalTransformation M using (NTHelper)
open import Categories.Morphism 𝒞 using (_≅_)
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Functor.Properties using ([_]-resp-Iso)
open Shorthands
open BraidShorthands
open SelfEnriched
  using (homˡ₁; homʳ₁; homˡFunctor; whisker-comm)
  renaming (homʳFunctor to homʳ)

private
  variable
    A B C : Obj -- closed arguments
    W X Y Z : Obj -- source, comparison, and codomain roles


module Dualized (⊥ : Obj) where
  dualᵒF : Functor selfEnrichment (opE selfEnrichment)
  dualᵒF = opF (homʳ ⊥) ∘F op²F

  dual²F : Endofunctor selfEnrichment
  dual²F = homʳ ⊥ ∘F dualᵒF

  private
    module Dualᵒ = Functor dualᵒF

  abstract
    dualᵒβ : uncurry (Dualᵒ.₁ {X = A} {Y = B}) ≈ internal-∘ ∘ σ⇒
    dualᵒβ = begin
      uncurry (curry (internal-∘ ∘ σ⇒) ∘ id)          ≈⟨ uncurry-∘ ⟩
      uncurry (curry (internal-∘ ∘ σ⇒)) ∘ (id ⊗₁ id)  ≈⟨ eval-curry ⟩∘⟨refl ⟩
      (internal-∘ ∘ σ⇒) ∘ (id ⊗₁ id)                  ≈⟨ elimʳ ⊗.identity ⟩
      internal-∘ ∘ σ⇒                                 ∎

    dualᵒ-action : Dualᵒ.₁ {X = A} {Y = B} ≈ homʳ₁ A B ⊥
    dualᵒ-action = uncurry-injective (dualᵒβ ○ ⟺ eval-curry)

    op-dual²₁ : Functor.₁ (opF dual²F) {X = A} {Y = B}
                  ≈ Functor.₁ (dualᵒF ∘F homʳ ⊥) {X = A} {Y = B}
    op-dual²₁ = (refl⟩∘⟨ identityʳ) ○ (⟺ identityʳ ⟩∘⟨refl)

  private
    ⌜_⌝ʳ : (f : A ⇒ B) → unit ⇒ [ [ X , A ]₀ , [ X , B ]₀ ]₀
    ⌜ f ⌝ʳ = homˡ₁ _ _ _ ∘ ⌜ f ⌝

    σ-unit : {f : unit ⇒ A} →
      (f ⊗₁ id {W}) ∘ λ⇐ ≈ σ⇒ ∘ (id ⊗₁ f) ∘ ρ⇐
    σ-unit {f = f} = begin
      (f ⊗₁ id) ∘ λ⇐       ≈˘⟨ refl⟩∘⟨ unitʳ-braiding ⟩
      (f ⊗₁ id) ∘ σ⇒ ∘ ρ⇐  ≈˘⟨ extendʳ σ⇒-comm ⟩
      σ⇒ ∘ (id ⊗₁ f) ∘ ρ⇐  ∎

    homʳNT : (f : A ⇒ B) → NTHelper (homʳ A) (homʳ B)
    homʳNT {A} {B} f = record
      { comp = λ X → ⌜ f ⌝ʳ
      ; commute = λ { {W} {X} → begin
          internal-∘ ∘ (⌜ f ⌝ʳ ⊗₁ homʳ₁ X W A) ∘ λ⇐
            ≈⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟩
          internal-∘ ∘ (homˡ₁ X A B ⊗₁ homʳ₁ X W A) ∘ (⌜ f ⌝ ⊗₁ id) ∘ λ⇐
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ σ-unit ⟩
          internal-∘ ∘ (homˡ₁ X A B ⊗₁ homʳ₁ X W A) ∘
            σ⇒ ∘ ((id ⊗₁ ⌜ f ⌝) ∘ ρ⇐)
            ≈⟨ assoc²εα ⟩
          ((internal-∘ ∘ (homˡ₁ X A B ⊗₁ homʳ₁ X W A)) ∘ σ⇒) ∘
            ((id ⊗₁ ⌜ f ⌝) ∘ ρ⇐)
            ≈˘⟨ whisker-comm W X A B ⟩∘⟨refl ⟩
          (internal-∘ ∘ (homʳ₁ X W B ⊗₁ homˡ₁ W A B)) ∘
            ((id ⊗₁ ⌜ f ⌝) ∘ ρ⇐)
            ≈⟨ pullʳ (pullˡ merge₂ʳ) ⟩
          internal-∘ ∘ (homʳ₁ X W B ⊗₁ ⌜ f ⌝ʳ) ∘ ρ⇐ ∎ }
      }

    ⌜_⌝ᵢ : A ≅ B → Morphism._≅_ (Underlying selfEnrichment) A B
    ⌜ i ⌝ᵢ = record
      { from = ⌜ _≅_.from i ⌝
      ; to = ⌜ _≅_.to i ⌝
      ; iso = record
        { isoˡ = ⌜∘⌝ ○ ⌜⌝-resp-≈ (_≅_.isoˡ i)
        ; isoʳ = ⌜∘⌝ ○ ⌜⌝-resp-≈ (_≅_.isoʳ i)
        }
      }

  homʳ≃ : A ≅ B → NaturalIsomorphism (homʳ A) (homʳ B)
  homʳ≃ i = niHelper record
    { F⇒G = homʳNT (_≅_.from i)
    ; F⇐G = homʳNT (_≅_.to i)
    ; iso = λ X →
        [ UnderlyingFunctor (homˡFunctor X) ]-resp-Iso (Morphism._≅_.iso ⌜ i ⌝ᵢ)
    }
