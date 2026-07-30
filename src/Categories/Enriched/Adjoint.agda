{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (module Commutation)
  renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Enriched adjunctions are adjunctions in V-Cat; see Kelly,
-- "Basic Concepts of Enriched Category Theory", Section 1.11.

module Categories.Enriched.Adjoint
  {o ℓ e} {𝒱 : Setoid-Category o ℓ e} {M : Monoidal 𝒱} (S : Symmetric M) where

open import Level using (_⊔_; levelOfTerm)

open import Categories.Enriched.Category M using (Category; _[_,_])
open import Categories.Enriched.Functor M using (Functor)
open import Categories.Morphism 𝒱 using (_≅_)

open Setoid-Category 𝒱
open Commutation 𝒱
open Monoidal M
open Symmetric S using (braided)
open import Categories.Category.Monoidal.Braided.Properties braided using (module Shorthands)
open Shorthands

record Adjoint {c d} {𝒞 : Category c} {𝒟 : Category d}
  (L : Functor 𝒞 𝒟) (R : Functor 𝒟 𝒞) : Set (levelOfTerm L ⊔ levelOfTerm R) where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module L = Functor L
    module R = Functor R

  field
    hom-iso : ∀ {A B} → 𝒟 [ L.₀ A , B ] ≅ 𝒞 [ A , R.₀ B ]

    naturalˡ : (A X : 𝒞.Obj) (B : 𝒟.Obj) →
      [ 𝒞 [ X , A ] ⊗₀ 𝒟 [ L.₀ A , B ] ⇒ 𝒞 [ X , R.₀ B ] ]⟨
        L.₁ ⊗₁ id                         ⇒⟨ 𝒟 [ L.₀ X , L.₀ A ] ⊗₀ 𝒟 [ L.₀ A , B ] ⟩
        σ⇒                               ⇒⟨ 𝒟 [ L.₀ A , B ] ⊗₀ 𝒟 [ L.₀ X , L.₀ A ] ⟩
        𝒟.⊚                              ⇒⟨ 𝒟 [ L.₀ X , B ] ⟩
        _≅_.from (hom-iso {X} {B})
      ≈ id ⊗₁ _≅_.from (hom-iso {A} {B})  ⇒⟨ 𝒞 [ X , A ] ⊗₀ 𝒞 [ A , R.₀ B ] ⟩
        σ⇒                               ⇒⟨ 𝒞 [ A , R.₀ B ] ⊗₀ 𝒞 [ X , A ] ⟩
        𝒞.⊚
      ⟩

    naturalʳ : (A : 𝒞.Obj) (B Y : 𝒟.Obj) →
      [ 𝒟 [ B , Y ] ⊗₀ 𝒟 [ L.₀ A , B ] ⇒ 𝒞 [ A , R.₀ Y ] ]⟨
        𝒟.⊚                              ⇒⟨ 𝒟 [ L.₀ A , Y ] ⟩
        _≅_.from (hom-iso {A} {Y})
      ≈ R.₁ ⊗₁ _≅_.from (hom-iso {A} {B})  ⇒⟨ 𝒞 [ R.₀ B , R.₀ Y ] ⊗₀ 𝒞 [ A , R.₀ B ] ⟩
        𝒞.⊚
      ⟩

infix 5 _⊣_

_⊣_ : ∀ {c d} {𝒞 : Category c} {𝒟 : Category d} →
  Functor 𝒞 𝒟 → Functor 𝒟 𝒞 → Set _
_⊣_ = Adjoint
