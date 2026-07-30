{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Variable-by-variable enriched naturality follows Kelly,
-- "Basic Concepts of Enriched Category Theory", Sections 1.5--1.6, (1.21).

module Categories.Enriched.Bifunctor.NaturalTransformation
  {o ℓ e} {V : Category o ℓ e} {M : Monoidal V} (S : Symmetric M) where

open import Level using (levelOfTerm)
open import Data.Product using (_,_)

import Categories.Enriched.Category as Enriched

open Category V renaming (id to idV)
open Monoidal M
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reassociation M using (ρ⇐-assoc)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Category M using (_[_,_])
open import Categories.Enriched.Bifunctor S
  using (BifunctorHelper; bifunctorHelper; module FromHelper)
open import Categories.Enriched.NaturalTransformation M using (NTHelper)
open import Categories.Morphism.Reasoning V
open Shorthands

private module Composition {c} (𝒬 : Enriched.Category M c) where
  private
    module 𝒬 = Enriched.Category 𝒬
    open 𝒬 using (⊚; ⊚-assoc-var)

    variable
      A B C D : 𝒬.Obj
      W X : Obj

  abstract
    associateˡ : {f : unit ⇒ 𝒬 [ C , D ]} {g : W ⇒ 𝒬 [ B , C ]}
                  {h : X ⇒ 𝒬 [ A , B ]} →
                  ⊚ ∘ ((⊚ ∘ (f ⊗₁ g) ∘ λ⇐) ⊗₁ h)
                  ≈ ⊚ ∘ (f ⊗₁ (⊚ ∘ (g ⊗₁ h))) ∘ λ⇐
    associateˡ {f = f} {g} {h} = let
      assoc-cohere = switch-tofromˡ associator coherence-inv₁
      in begin
      ⊚ ∘ ((⊚ ∘ (f ⊗₁ g) ∘ λ⇐) ⊗₁ h)                    ≈˘⟨ refl⟩∘⟨ assoc ⟩⊗⟨refl ⟩
      ⊚ ∘ (((⊚ ∘ (f ⊗₁ g)) ∘ λ⇐) ⊗₁ h)                  ≈⟨ refl⟩∘⟨ split₁ʳ ⟩
      ⊚ ∘ (((⊚ ∘ (f ⊗₁ g)) ⊗₁ h) ∘ (λ⇐ ⊗₁ idV))         ≈⟨ extendʳ ⊚-assoc-var ⟩
      ⊚ ∘ (((f ⊗₁ (⊚ ∘ (g ⊗₁ h))) ∘ α⇒) ∘ (λ⇐ ⊗₁ idV))  ≈˘⟨ refl⟩∘⟨ pushʳ assoc-cohere ⟩
      ⊚ ∘ (f ⊗₁ (⊚ ∘ (g ⊗₁ h))) ∘ λ⇐                    ∎

    associateᵐ : {f : W ⇒ 𝒬 [ C , D ]} {g : unit ⇒ 𝒬 [ B , C ]}
                  {h : X ⇒ 𝒬 [ A , B ]} →
                  ⊚ ∘ ((⊚ ∘ (f ⊗₁ g) ∘ ρ⇐) ⊗₁ h)
                  ≈ ⊚ ∘ (f ⊗₁ (⊚ ∘ (g ⊗₁ h) ∘ λ⇐))
    associateᵐ {f = f} {g} {h} = begin
      ⊚ ∘ ((⊚ ∘ (f ⊗₁ g) ∘ ρ⇐) ⊗₁ h)                    ≈˘⟨ refl⟩∘⟨ assoc ⟩⊗⟨refl ⟩
      ⊚ ∘ (((⊚ ∘ (f ⊗₁ g)) ∘ ρ⇐) ⊗₁ h)                  ≈⟨ refl⟩∘⟨ split₁ʳ ⟩
      ⊚ ∘ (((⊚ ∘ (f ⊗₁ g)) ⊗₁ h) ∘ (ρ⇐ ⊗₁ idV))         ≈⟨ extendʳ ⊚-assoc-var ⟩
      ⊚ ∘ (((f ⊗₁ (⊚ ∘ (g ⊗₁ h))) ∘ α⇒) ∘ (ρ⇐ ⊗₁ idV))  ≈⟨ refl⟩∘⟨ pullʳ triangle-inv′ ⟩
      ⊚ ∘ ((f ⊗₁ (⊚ ∘ (g ⊗₁ h))) ∘ (idV ⊗₁ λ⇐))         ≈˘⟨ refl⟩∘⟨ split₂ʳ ⟩
      ⊚ ∘ (f ⊗₁ ((⊚ ∘ (g ⊗₁ h)) ∘ λ⇐))                  ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩
      ⊚ ∘ (f ⊗₁ (⊚ ∘ (g ⊗₁ h) ∘ λ⇐))                    ∎

    associateʳ : {f : W ⇒ 𝒬 [ C , D ]} {g : X ⇒ 𝒬 [ B , C ]}
                  {h : unit ⇒ 𝒬 [ A , B ]} →
                  ⊚ ∘ (f ⊗₁ (⊚ ∘ (g ⊗₁ h) ∘ ρ⇐))
                  ≈ ⊚ ∘ ((⊚ ∘ (f ⊗₁ g)) ⊗₁ h) ∘ ρ⇐
    associateʳ {f = f} {g} {h} = begin
      ⊚ ∘ (f ⊗₁ (⊚ ∘ (g ⊗₁ h) ∘ ρ⇐))              ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩
      ⊚ ∘ (f ⊗₁ ((⊚ ∘ (g ⊗₁ h)) ∘ ρ⇐))            ≈⟨ refl⟩∘⟨ split₂ʳ ⟩
      ⊚ ∘ ((f ⊗₁ (⊚ ∘ (g ⊗₁ h))) ∘ (idV ⊗₁ ρ⇐))   ≈⟨ refl⟩∘⟨ pushʳ ρ⇐-assoc ⟩
      ⊚ ∘ (((f ⊗₁ (⊚ ∘ (g ⊗₁ h))) ∘ α⇒) ∘ ρ⇐)     ≈˘⟨ extendʳ ⊚-assoc-var ⟩
      ⊚ ∘ ((⊚ ∘ (f ⊗₁ g)) ⊗₁ h) ∘ ρ⇐              ∎

record BifunctorNTHelper {a b c}
  {𝒩 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒬 : Enriched.Category M c}
  (F G : BifunctorHelper 𝒩 ℬ 𝒬) : Set (levelOfTerm (F , G)) where
  private
    module 𝒩 = Enriched.Category 𝒩
    module ℬ = Enriched.Category ℬ
    module 𝒬 = Enriched.Category 𝒬
    module F = BifunctorHelper F
    module G = BifunctorHelper G

  open 𝒬 using (⊚)

  field
    comp : (A : 𝒩.Obj) (X : ℬ.Obj) → unit ⇒ 𝒬 [ F.map₀ A X , G.map₀ A X ]

    naturalˡ : ∀ {A B} (X : ℬ.Obj) →
                ⊚ ∘ (comp B X ⊗₁ F.mapˡ A B X) ∘ λ⇐
                ≈ ⊚ ∘ (G.mapˡ A B X ⊗₁ comp A X) ∘ ρ⇐

    naturalʳ : ∀ (A : 𝒩.Obj) {X Y} →
                ⊚ ∘ (comp A Y ⊗₁ F.mapʳ A X Y) ∘ λ⇐
                ≈ ⊚ ∘ (G.mapʳ A X Y ⊗₁ comp A X) ∘ ρ⇐

bifunctorNTHelper : ∀ {a b c}
  {𝒩 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒬 : Enriched.Category M c} {F G : BifunctorHelper 𝒩 ℬ 𝒬} →
  BifunctorNTHelper F G → NTHelper (bifunctorHelper F) (bifunctorHelper G)
bifunctorNTHelper {𝒬 = 𝒬} {F = F} {G} α = record
  { comp = λ { (A , X) → α.comp A X }
  ; commute = λ { {A , X} {B , Y} → begin
    ⊚ ∘ (α.comp B Y ⊗₁ F′.diagonal) ∘ λ⇐                          ≈˘⟨ associateˡ ⟩
    ⊚ ∘ ((⊚ ∘ (α.comp B Y ⊗₁ F.mapˡ A B Y) ∘ λ⇐) ⊗₁ F.mapʳ A X Y) ≈⟨ refl⟩∘⟨ α.naturalˡ Y ⟩⊗⟨refl ⟩
    ⊚ ∘ ((⊚ ∘ (G.mapˡ A B Y ⊗₁ α.comp A Y) ∘ ρ⇐) ⊗₁ F.mapʳ A X Y) ≈⟨ associateᵐ ⟩
    ⊚ ∘ (G.mapˡ A B Y ⊗₁ (⊚ ∘ (α.comp A Y ⊗₁ F.mapʳ A X Y) ∘ λ⇐)) ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ α.naturalʳ A ⟩
    ⊚ ∘ (G.mapˡ A B Y ⊗₁ (⊚ ∘ (G.mapʳ A X Y ⊗₁ α.comp A X) ∘ ρ⇐)) ≈⟨ associateʳ ⟩
    ⊚ ∘ (G′.diagonal ⊗₁ α.comp A X) ∘ ρ⇐                          ∎ }
  }
  where
  module α = BifunctorNTHelper α
  module F = BifunctorHelper F
  module G = BifunctorHelper G
  module F′ = FromHelper F
  module G′ = FromHelper G
  module 𝒬 = Enriched.Category 𝒬
  open Composition 𝒬 using (associateˡ; associateᵐ; associateʳ)
  open 𝒬 using (⊚)
