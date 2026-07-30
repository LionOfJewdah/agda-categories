{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Extraordinary enriched transformations in the sense of Eilenberg--Kelly.

module Categories.Enriched.Extraordinary
  {o ℓ e} {V : Category o ℓ e} {M : Monoidal V} (S : Symmetric M) where

open import Level using (_⊔_)
open import Data.Product using (_,_)
open import Relation.Unary using (Pred)

import Categories.Category.Monoidal.Interchange.Braided as BraidedInterchange
import Categories.Enriched.Category as Enriched

open import Categories.Enriched.Category.Opposite S renaming (op to opE)
open import Categories.Enriched.Category M using (_[_,_])
open import Categories.Enriched.Bifunctor S
  using (BifunctorHelper; bifunctorHelper; module FromHelper)
open import Categories.Enriched.Functor M using (Functor)
open import Categories.Enriched.NaturalTransformation M using (NaturalTransformation)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Properties M using (module Kelly's)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Morphism.Reasoning V

open Category V renaming (Obj to ObjV; id to idV)
open Monoidal M
open Symmetric S using (braided)
open BraidedInterchange braided using () renaming (hasInterchange to interchange)
open import Categories.Enriched.Category.TensorProduct interchange using (_⊠_)
open Shorthands

module Calculus {a b} (𝒜 : Enriched.Category M a) (ℬ : Enriched.Category M b) where

  private
    module 𝒜 = Enriched.Category 𝒜
    module ℬ = Enriched.Category ℬ

    𝒜ᵉ : Enriched.Category M a
    𝒜ᵉ = opE 𝒜 ⊠ 𝒜
    module 𝒜ᵉ = Enriched.Category 𝒜ᵉ

    variable
      X Y : 𝒜.Obj -- extraordinary arguments
      A B C Z : ℬ.Obj -- source, intermediate, and target roles
      P Q : 𝒜ᵉ.Obj -- naturality source and target
      H : ObjV

    infixr 9 _⊚ˡ_ _⊚ʳ_ _⊚₀_

    _⊚ˡ_ : (unit ⇒ ℬ [ B , C ]) → (H ⇒ ℬ [ A , B ]) → H ⇒ ℬ [ A , C ]
    g ⊚ˡ f = ℬ.⊚ ∘ (g ⊗₁ f) ∘ λ⇐

    _⊚ʳ_ : (H ⇒ ℬ [ B , C ]) → (unit ⇒ ℬ [ A , B ]) → H ⇒ ℬ [ A , C ]
    g ⊚ʳ f = ℬ.⊚ ∘ (g ⊗₁ f) ∘ ρ⇐

    _⊚₀_ : (unit ⇒ ℬ [ B , C ]) → (unit ⇒ ℬ [ A , B ]) → unit ⇒ ℬ [ A , C ]
    g ⊚₀ f = ℬ.⊚ ∘ (g ⊗₁ f) ∘ λ⇐

    abstract
      ⊚-assocʳ : (g : H ⇒ ℬ [ C , Z ]) (h : unit ⇒ ℬ [ B , C ])
        (i : unit ⇒ ℬ [ A , B ]) → (g ⊚ʳ h) ⊚ʳ i ≈ g ⊚ʳ (h ⊚₀ i)
      ⊚-assocʳ g h i = begin
        ℬ.⊚ ∘ (ℬ.⊚ ∘ (g ⊗₁ h) ∘ ρ⇐) ⊗₁ i ∘ ρ⇐
          ≈˘⟨ refl⟩∘⟨ assoc ⟩⊗⟨refl ⟩∘⟨refl ⟩
        ℬ.⊚ ∘ ((ℬ.⊚ ∘ (g ⊗₁ h)) ∘ ρ⇐) ⊗₁ i ∘ ρ⇐
          ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
        ℬ.⊚ ∘ ((ℬ.⊚ ∘ (g ⊗₁ h)) ⊗₁ i ∘ (ρ⇐ ⊗₁ idV)) ∘ ρ⇐
          ≈⟨ pullˡ (pullˡ ℬ.⊚-assoc-var) ⟩
        ((ℬ.⊚ ∘ (g ⊗₁ (ℬ.⊚ ∘ (h ⊗₁ i))) ∘ α⇒) ∘ (ρ⇐ ⊗₁ idV)) ∘ ρ⇐
          ≈˘⟨ pushʳ (pushʳ (switch-tofromˡ associator triangle-inv)) ⟩∘⟨refl ⟩
        (ℬ.⊚ ∘ (g ⊗₁ (ℬ.⊚ ∘ (h ⊗₁ i))) ∘ (idV ⊗₁ λ⇐)) ∘ ρ⇐
          ≈˘⟨ pushʳ (split₂ʳ ⟩∘⟨refl) ⟩
        ℬ.⊚ ∘ (g ⊗₁ ((ℬ.⊚ ∘ (h ⊗₁ i)) ∘ λ⇐)) ∘ ρ⇐
          ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl ⟩
        ℬ.⊚ ∘ (g ⊗₁ (ℬ.⊚ ∘ (h ⊗₁ i) ∘ λ⇐)) ∘ ρ⇐  ∎

      ⊚-assocˡ : (g : unit ⇒ ℬ [ C , Z ]) (h : H ⇒ ℬ [ B , C ])
        (i : unit ⇒ ℬ [ A , B ]) → (g ⊚ˡ h) ⊚ʳ i ≈ g ⊚ˡ (h ⊚ʳ i)
      ⊚-assocˡ g h i = begin
        ℬ.⊚ ∘ (ℬ.⊚ ∘ (g ⊗₁ h) ∘ λ⇐) ⊗₁ i ∘ ρ⇐
          ≈˘⟨ refl⟩∘⟨ assoc ⟩⊗⟨refl ⟩∘⟨refl ⟩
        ℬ.⊚ ∘ ((ℬ.⊚ ∘ (g ⊗₁ h)) ∘ λ⇐) ⊗₁ i ∘ ρ⇐
          ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
        ℬ.⊚ ∘ ((ℬ.⊚ ∘ (g ⊗₁ h)) ⊗₁ i ∘ (λ⇐ ⊗₁ idV)) ∘ ρ⇐
          ≈⟨ pullˡ (pullˡ ℬ.⊚-assoc-var) ⟩
        ((ℬ.⊚ ∘ (g ⊗₁ (ℬ.⊚ ∘ (h ⊗₁ i))) ∘ α⇒) ∘ (λ⇐ ⊗₁ idV)) ∘ ρ⇐
          ≈˘⟨ pushʳ (pushʳ (switch-tofromˡ associator Kelly's.coherence-inv₁)) ⟩∘⟨refl ⟩
        (ℬ.⊚ ∘ (g ⊗₁ (ℬ.⊚ ∘ (h ⊗₁ i))) ∘ λ⇐) ∘ ρ⇐
          ≈⟨ pullʳ (pullʳ unitorˡ-commute-to) ⟩
        ℬ.⊚ ∘ (g ⊗₁ (ℬ.⊚ ∘ (h ⊗₁ i))) ∘ (idV ⊗₁ ρ⇐) ∘ λ⇐
          ≈˘⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
        ℬ.⊚ ∘ (g ⊗₁ ((ℬ.⊚ ∘ (h ⊗₁ i)) ∘ ρ⇐)) ∘ λ⇐
          ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl ⟩
        ℬ.⊚ ∘ (g ⊗₁ (ℬ.⊚ ∘ (h ⊗₁ i) ∘ ρ⇐)) ∘ λ⇐  ∎

  module Actions (F : Functor (opE 𝒜 ⊠ 𝒜) ℬ) where
    module F = Functor F

    F₁ʳ : 𝒜 [ X , Y ] ⇒ ℬ [ F.₀ (X , X) , F.₀ (X , Y) ]
    F₁ʳ = F.₁ ∘ (𝒜.id ⊗₁ idV) ∘ λ⇐

    F₁ˡ : 𝒜 [ X , Y ] ⇒ ℬ [ F.₀ (Y , Y) , F.₀ (X , Y) ]
    F₁ˡ = F.₁ ∘ (idV ⊗₁ 𝒜.id) ∘ ρ⇐

  open Actions

  module Definition (F : Functor 𝒜ᵉ ℬ) (B : ℬ.Obj) where
    private module ℱ = Functor F

    Extraordinary : Pred (∀ X → unit ⇒ ℬ [ B , ℱ.₀ (X , X) ]) (a ⊔ e)
    Extraordinary α = ∀ {X Y} →
      ℬ.⊚ ∘ (F₁ʳ F ⊗₁ α X) ∘ ρ⇐ ≈ ℬ.⊚ ∘ (F₁ˡ F ⊗₁ α Y) ∘ ρ⇐

    extraordinary :
      {α : ∀ X → unit ⇒ ℬ [ B , ℱ.₀ (X , X) ]} →
      (∀ {X Y} →
        ℬ.⊚ ∘ (F₁ʳ F ⊗₁ α X) ∘ ρ⇐ ≈ ℬ.⊚ ∘ (F₁ˡ F ⊗₁ α Y) ∘ ρ⇐) →
      Extraordinary α
    extraordinary equation = equation

    extraordinary-equation :
      {α : ∀ X → unit ⇒ ℬ [ B , ℱ.₀ (X , X) ]} →
      Extraordinary α →
      ∀ {X Y} →
      ℬ.⊚ ∘ (F₁ʳ F ⊗₁ α X) ∘ ρ⇐ ≈ ℬ.⊚ ∘ (F₁ˡ F ⊗₁ α Y) ∘ ρ⇐
    extraordinary-equation extra = extra

    extraordinary-resp-≈ :
      {α β : ∀ X → unit ⇒ ℬ [ B , ℱ.₀ (X , X) ]} →
      (∀ X → α X ≈ β X) → Extraordinary α → Extraordinary β
    extraordinary-resp-≈ {α = α} {β} α≈β extra = extraordinary λ {X} {Y} → begin
      F₁ʳ F ⊚ʳ β X  ≈˘⟨ refl⟩∘⟨ (refl⟩⊗⟨ α≈β X) ⟩∘⟨refl ⟩
      F₁ʳ F ⊚ʳ α X  ≈⟨ extraordinary-equation extra ⟩
      F₁ˡ F ⊚ʳ α Y  ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ α≈β Y) ⟩∘⟨refl ⟩
      F₁ˡ F ⊚ʳ β Y  ∎

  open Definition public using (Extraordinary; extraordinary; extraordinary-resp-≈)

  module ActionCriterion (F : Functor 𝒜ᵉ ℬ) where
    private module F′ = Functor F

    abstract
      from-actions :
        (mapʳ : (X Y : 𝒜.Obj) →
          𝒜 [ X , Y ] ⇒ ℬ [ F′.₀ (X , X) , F′.₀ (X , Y) ]) →
        (mapˡ : (X Y : 𝒜.Obj) →
          𝒜 [ X , Y ] ⇒ ℬ [ F′.₀ (Y , Y) , F′.₀ (X , Y) ]) →
        ((X Y : 𝒜.Obj) → F₁ʳ F ≈ mapʳ X Y) →
        ((X Y : 𝒜.Obj) → F₁ˡ F ≈ mapˡ X Y) →
        (C : ℬ.Obj) →
        (α : ∀ X → unit ⇒ ℬ [ C , F′.₀ (X , X) ]) →
        ((X Y : 𝒜.Obj) → mapʳ X Y ⊚ʳ α X ≈ mapˡ X Y ⊚ʳ α Y) →
        Extraordinary F C α
      from-actions mapʳ mapˡ reduceʳ reduceˡ C α extra =
        extraordinary F C λ {X} {Y} → begin
          F₁ʳ F ⊚ʳ α X    ≈⟨ refl⟩∘⟨ (reduceʳ X Y ⟩⊗⟨refl) ⟩∘⟨refl ⟩
          mapʳ X Y ⊚ʳ α X  ≈⟨ extra X Y ⟩
          mapˡ X Y ⊚ʳ α Y  ≈˘⟨ refl⟩∘⟨ (reduceˡ X Y ⟩⊗⟨refl) ⟩∘⟨refl ⟩
          F₁ˡ F ⊚ʳ α Y    ∎

  open ActionCriterion public

  module HelperCriterion
    (H : BifunctorHelper (opE 𝒜) 𝒜 ℬ) where

    private module H = BifunctorHelper H

    abstract
      from-helper :
        (C : ℬ.Obj) →
        (α : ∀ X → unit ⇒ ℬ [ C , H.map₀ X X ]) →
        ((X Y : 𝒜.Obj) →
          H.mapʳ X X Y ⊚ʳ α X ≈ H.mapˡ Y X Y ⊚ʳ α Y) →
        Extraordinary (bifunctorHelper H) C α
      from-helper C α extra = extraordinary (bifunctorHelper H) C λ {X} {Y} → begin
        F₁ʳ (bifunctorHelper H) ⊚ʳ α X
          ≈⟨ refl⟩∘⟨ (FromHelper.diagonal-appˡ H ⟩⊗⟨refl) ⟩∘⟨refl ⟩
        H.mapʳ X X Y ⊚ʳ α X  ≈⟨ extra X Y ⟩
        H.mapˡ Y X Y ⊚ʳ α Y
          ≈˘⟨ refl⟩∘⟨ (FromHelper.diagonal-appʳ H ⟩⊗⟨refl) ⟩∘⟨refl ⟩
        F₁ˡ (bifunctorHelper H) ⊚ʳ α Y  ∎

  open HelperCriterion public

  module Mapping {F G : Functor 𝒜ᵉ ℬ} (β : NaturalTransformation F G) where
    private
      module F′ = Functor F
      module G′ = Functor G
      module β′ = NaturalTransformation β

      abstract
        β-natural : (j : H ⇒ 𝒜ᵉ [ P , Q ]) →
          β′.comp Q ⊚ˡ (F′.₁ ∘ j) ≈ (G′.₁ ∘ j) ⊚ʳ β′.comp P
        β-natural {P = P} {Q = Q} j = begin
          ℬ.⊚ ∘ (β′.comp Q ⊗₁ (F′.₁ ∘ j)) ∘ λ⇐
            ≈⟨ refl⟩∘⟨ split₂ʳ ⟩∘⟨refl ⟩
          ℬ.⊚ ∘ ((β′.comp Q ⊗₁ F′.₁) ∘ (idV ⊗₁ j)) ∘ λ⇐
            ≈˘⟨ refl⟩∘⟨ extendˡ unitorˡ-commute-to ⟩
          ℬ.⊚ ∘ ((β′.comp Q ⊗₁ F′.₁) ∘ λ⇐) ∘ j
            ≈⟨ extendʳ β′.commute ⟩
          ℬ.⊚ ∘ ((G′.₁ ⊗₁ β′.comp P) ∘ ρ⇐) ∘ j
            ≈⟨ refl⟩∘⟨ extendˡ unitorʳ-commute-to ⟩
          ℬ.⊚ ∘ ((G′.₁ ⊗₁ β′.comp P) ∘ (j ⊗₁ idV)) ∘ ρ⇐
            ≈˘⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
          ℬ.⊚ ∘ ((G′.₁ ∘ j) ⊗₁ β′.comp P) ∘ ρ⇐  ∎

      naturalityʳ :
        (X Y : 𝒜.Obj) →
        (α : ∀ X → unit ⇒ ℬ [ B , F′.₀ (X , X) ]) →
        F₁ʳ G ⊚ʳ (β′.comp (X , X) ⊚₀ α X)
        ≈ β′.comp (X , Y) ⊚ˡ (F₁ʳ F ⊚ʳ α X)
      naturalityʳ X Y α = begin
        F₁ʳ G ⊚ʳ (β′.comp (X , X) ⊚₀ α X)
          ≈˘⟨ ⊚-assocʳ (F₁ʳ G) (β′.comp (X , X)) (α X) ⟩
        (F₁ʳ G ⊚ʳ β′.comp (X , X)) ⊚ʳ α X
          ≈˘⟨ refl⟩∘⟨ ((β-natural ((𝒜.id ⊗₁ idV) ∘ λ⇐)) ⟩⊗⟨refl) ⟩∘⟨refl ⟩
        (β′.comp (X , Y) ⊚ˡ F₁ʳ F) ⊚ʳ α X
          ≈⟨ ⊚-assocˡ (β′.comp (X , Y)) (F₁ʳ F) (α X) ⟩
        β′.comp (X , Y) ⊚ˡ (F₁ʳ F ⊚ʳ α X)  ∎

      naturalityˡ :
        (X Y : 𝒜.Obj) →
        (α : ∀ X → unit ⇒ ℬ [ B , F′.₀ (X , X) ]) →
        F₁ˡ G ⊚ʳ (β′.comp (Y , Y) ⊚₀ α Y)
        ≈ β′.comp (X , Y) ⊚ˡ (F₁ˡ F ⊚ʳ α Y)
      naturalityˡ X Y α = begin
        F₁ˡ G ⊚ʳ (β′.comp (Y , Y) ⊚₀ α Y)
          ≈˘⟨ ⊚-assocʳ (F₁ˡ G) (β′.comp (Y , Y)) (α Y) ⟩
        (F₁ˡ G ⊚ʳ β′.comp (Y , Y)) ⊚ʳ α Y
          ≈˘⟨ refl⟩∘⟨ ((β-natural ((idV ⊗₁ 𝒜.id) ∘ ρ⇐)) ⟩⊗⟨refl) ⟩∘⟨refl ⟩
        (β′.comp (X , Y) ⊚ˡ F₁ˡ F) ⊚ʳ α Y
          ≈⟨ ⊚-assocˡ (β′.comp (X , Y)) (F₁ˡ F) (α Y) ⟩
        β′.comp (X , Y) ⊚ˡ (F₁ˡ F ⊚ʳ α Y)  ∎

    map-extraordinary : {B : ℬ.Obj}
      {α : ∀ X → unit ⇒ ℬ [ B , F′.₀ (X , X) ]} →
      (∀ {X Y} →
        ℬ.⊚ ∘ (F₁ʳ F ⊗₁ α X) ∘ ρ⇐ ≈ ℬ.⊚ ∘ (F₁ˡ F ⊗₁ α Y) ∘ ρ⇐) →
      Extraordinary G B
        (λ X → ℬ.⊚ ∘ (β′.comp (X , X) ⊗₁ α X) ∘ λ⇐)
    map-extraordinary {B = B} {α = α} extra =
      extraordinary G B λ {X} {Y} → begin
        F₁ʳ G ⊚ʳ (β′.comp (X , X) ⊚₀ α X)             ≈⟨ naturalityʳ X Y α ⟩
        β′.comp (X , Y) ⊚ˡ (F₁ʳ F ⊚ʳ α X)
          ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ extra) ⟩∘⟨refl ⟩
        β′.comp (X , Y) ⊚ˡ (F₁ˡ F ⊚ʳ α Y)             ≈˘⟨ naturalityˡ X Y α ⟩
        F₁ˡ G ⊚ʳ (β′.comp (Y , Y) ⊚₀ α Y)             ∎

  open Mapping public

open Calculus public
