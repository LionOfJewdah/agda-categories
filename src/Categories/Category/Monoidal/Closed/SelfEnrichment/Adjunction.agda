{-# OPTIONS --without-K --safe --lossy-unification #-}

-- --lossy-unification keeps the enriched naturality check under 20s instead of over 90s.

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Enriched swap-currying follows Kelly 1982, Section 1.11, especially (1.51)
-- and the closed-base example (1.27).

module Categories.Category.Monoidal.Closed.SelfEnrichment.Adjunction
  {o ℓ e} {𝒱 : Category o ℓ e} {M : Monoidal 𝒱}
  (S : Symmetric M) (Cl : Closed M) where

open import Data.Product using (_,_)

import Categories.Category.Construction.Core 𝒱 as Core

open Category 𝒱
open Commutation 𝒱
open Core.Shorthands using (idᵢ)
open Monoidal M
open Symmetric S using (braided; commutative; hexagon₁)
open Closed Cl using ([_,_]₀; [_,_]₁; [-,_]; [-,-])

open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Closed.Currying Cl
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment S Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Tensor S Cl
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M
  using (α⇒-id⊗-commute; α⇒-⊗id-commute; α⇐-⊗id-commute; assoc-to-coherence; whisker-comm)
open import Categories.Category.Monoidal.Symmetric.Properties S using (module Rotation)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Category.Opposite S renaming (op to opE)
open import Categories.Enriched.Functor M using (Functor; _∘F_)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism)
open import Categories.Morphism 𝒱 using (_≅_; module ≅)
open import Categories.Morphism.Duality 𝒱 using (≅⇒op-≅)
open import Categories.Morphism.Reasoning 𝒱
open import Categories.Functor.Properties using ([_]-resp-≅)
open Shorthands
open BraidShorthands
open Rotation using (cycle; cycle-cancel)
open SelfEnriched using () renaming (homʳFunctor to homʳ)

private
  variable
    A B C : Obj -- closed arguments
    W X Y Z : Obj -- source, comparison, and codomain roles

  abstract
    braid-past-pair : α⇒ ∘ ((σ⇒ {A} {B ⊗₀ C} ∘ α⇒) ∘ ((σ⇒ {B} {A} ⊗₁ id) ∘ α⇐))
      ≈ id ⊗₁ σ⇒ {A} {C}
    braid-past-pair {A} {B} {C} = begin
      α⇒ ∘ ((σ⇒ ∘ α⇒) ∘ ((σ⇒ ⊗₁ id) ∘ α⇐))                  ≈⟨ extendʳ (⟺ hexagon₁) ⟩
      (id ⊗₁ σ⇒) ∘ ((α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ ((σ⇒ ⊗₁ id) ∘ α⇐))  ≈⟨ sym-assoc ⟩
      cycle ∘ ((σ⇒ ⊗₁ id) ∘ α⇐)                             ≈⟨ extendʳ cycle-cancel ⟩
      (id ⊗₁ σ⇒) ∘ (α⇒ ∘ α⇐)                                ≈⟨ elimʳ associator.isoʳ ⟩
      id ⊗₁ σ⇒ ∎

    rebracket-four : α⇐ {X} {W ⊗₀ Z} {Y} ∘ (id ⊗₁ α⇐ {W} {Z} {Y}) ∘ α⇒ {X} {W} {Z ⊗₀ Y}
      ≈ (α⇒ {X} {W} {Z} ⊗₁ id) ∘ α⇐ {X ⊗₀ W} {Z} {Y}
    rebracket-four = begin
      α⇐ ∘ (id ⊗₁ α⇐) ∘ α⇒        ≈⟨ refl⟩∘⟨ assoc-to-coherence ⟩
      α⇐ ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐   ≈⟨ cancelˡ associator.isoˡ ⟩
      (α⇒ ⊗₁ id) ∘ α⇐             ∎

    rebracket-pair-swaps : α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ σ⇒ {Y} {Z}))
        ∘ α⇒ ∘ (σ⇒ {W} {X} ⊗₁ id)
      ≈ (α⇒ ⊗₁ id) ∘ ((σ⇒ {W} {X} ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒ {Y} {Z})
    rebracket-pair-swaps {W} {X} {Y} {Z} = begin
      α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ σ⇒)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (⟺ α⇒-id⊗-commute) ⟩
      α⇐ ∘ (id ⊗₁ α⇐) ∘ α⇒ ∘ ((id ⊗₁ σ⇒) ∘ (σ⇒ ⊗₁ id))
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ serialize₂₁ ⟩
      α⇐ ∘ (id ⊗₁ α⇐) ∘ α⇒ ∘ (σ⇒ ⊗₁ σ⇒)
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      α⇐ ∘ (((id ⊗₁ α⇐) ∘ α⇒) ∘ (σ⇒ ⊗₁ σ⇒))
        ≈⟨ extendʳ rebracket-four ⟩
      (α⇒ ⊗₁ id) ∘ (α⇐ ∘ (σ⇒ ⊗₁ σ⇒))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ serialize₁₂ ⟩
      (α⇒ ⊗₁ id) ∘ α⇐ ∘ (σ⇒ ⊗₁ id) ∘ (id ⊗₁ σ⇒)
        ≈⟨ refl⟩∘⟨ extendʳ α⇐-⊗id-commute ⟩
      (α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∎

abstract
  evalᵀ : (A B C : Obj) → σ⇒ {A} {C} ∘
      ((id {A} ⊗₁ eval {B} {C}) ∘ α⇒ ∘ (σ⇒ { [ B , C ]₀ } {A} ⊗₁ id) ∘ α⇐)
    ≈ (eval {B} {C} ⊗₁ id {A}) ∘ α⇐ ∘ (id ⊗₁ σ⇒ {A} {B})
  evalᵀ A B C = begin
    σ⇒ ∘ ((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)
      ≈⟨ extendʳ σ⇒-comm ⟩
    (eval ⊗₁ id) ∘ (σ⇒ ∘ (α⇒ ∘ ((σ⇒ ⊗₁ id) ∘ α⇐)))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    (eval ⊗₁ id) ∘ ((σ⇒ ∘ α⇒) ∘ ((σ⇒ ⊗₁ id) ∘ α⇐))
      ≈⟨ refl⟩∘⟨ switch-fromtoˡ associator braid-past-pair ⟩
    (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∎

-- A function of `A ⊗ B` is a function of `B` returning a function of `A`.
swap-curry-≅ : [ A ⊗₀ B , C ]₀ ≅ [ B , [ A , C ]₀ ]₀
swap-curry-≅ {A} {B} {C} = ≅.trans ([ [-, C ] ]-resp-≅ (≅⇒op-≅ σ)) curry₂-iso

module swap-curry-≅ {A B C} where
  open _≅_ (swap-curry-≅ {A} {B} {C}) public

  abstract
    β : uncurry to ≈ ((eval ∘ (eval ⊗₁ id)) ∘ α⇐) ∘ (id ⊗₁ σ⇒)
    β = begin
      uncurry to                                ≈⟨ uncurry-∘ ⟩
      uncurry [ σ⇒ , id ]₁ ∘ (uncurry₂ ⊗₁ id)   ≈⟨ eval-comm-dom ⟩∘⟨refl ⟩
      (eval ∘ (id ⊗₁ σ⇒)) ∘ (uncurry₂ ⊗₁ id)    ≈⟨ pullʳ merge₂ˡ ⟩
      eval ∘ (uncurry₂ ⊗₁ (σ⇒ ∘ id))            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ identityʳ ⟩
      eval ∘ (uncurry₂ ⊗₁ σ⇒)                   ≈⟨ pushʳ serialize₁₂ ⟩
      uncurry uncurry₂ ∘ (id ⊗₁ σ⇒)             ≈⟨ eval-curry ⟩∘⟨refl ⟩
      ((eval ∘ (eval ⊗₁ id)) ∘ α⇐) ∘ (id ⊗₁ σ⇒) ∎

    β⁻¹ : uncurry (uncurry from) ≈ eval ∘ (id ⊗₁ σ⇐ {A} {B}) ∘ α⇒
    β⁻¹ = begin
      uncurry (uncurry from)                                  ≈⟨ uncurry²-∘ ⟩
      uncurry (uncurry curry₂) ∘ (([ σ⇐ , id ]₁ ⊗₁ id) ⊗₁ id) ≈⟨ uncurry²-curry₂ ⟩∘⟨refl ⟩
      (eval ∘ α⇒) ∘ (([ σ⇐ , id ]₁ ⊗₁ id) ⊗₁ id)
        ≈⟨ pullʳ assoc-commute-from ⟩
      eval ∘ ([ σ⇐ , id ]₁ ⊗₁ (id ⊗₁ id)) ∘ α⇒      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩
      eval ∘ ([ σ⇐ , id ]₁ ⊗₁ id) ∘ α⇒              ≈⟨ extendʳ eval-comm-dom ⟩
      eval ∘ (id ⊗₁ σ⇐) ∘ α⇒                        ∎

swap-curry-natural : (f : X ⇒ A) (g : Y ⇒ B) (h : C ⇒ Z) →
  [ g , [ f , h ]₁ ]₁ ∘ swap-curry-≅.from
  ≈ swap-curry-≅.from ∘ [ f ⊗₁ g , h ]₁
swap-curry-natural f g h = begin
  [ g , [ f , h ]₁ ]₁ ∘ (curry₂ ∘ [ σ⇐ , id ]₁)  ≈⟨ pullˡ curry₂-natural ⟩
  (curry₂ ∘ [ g ⊗₁ f , h ]₁) ∘ [ σ⇐ , id ]₁      ≈⟨ pullʳ (⟺ [-,-].homomorphism) ⟩
  curry₂ ∘ [ σ⇐ ∘ (g ⊗₁ f) , h ∘ id ]₁           ≈⟨ refl⟩∘⟨ [-,-].F-resp-≈ (σ⇐-comm , id-comm) ⟩
  curry₂ ∘ [ (f ⊗₁ g) ∘ σ⇐ , id ∘ h ]₁           ≈⟨ pushʳ [-,-].homomorphism ⟩
  (curry₂ ∘ [ σ⇐ , id ]₁) ∘ [ f ⊗₁ g , h ]₁      ∎

swap-curry⇐-commʳ : (g : Y ⇒ B) →
  swap-curry-≅.to {A = A} {B = Y} {C = C} ∘ [ g , id ]₁
  ≈ [ id ⊗₁ g , id ]₁ ∘ swap-curry-≅.to {A = A} {B = B} {C = C}
swap-curry⇐-commʳ g = begin
  swap-curry-≅.to ∘ [ g , id ]₁
    ≈˘⟨ refl⟩∘⟨ [-,-].F-resp-≈ (Equiv.refl , [-,-].identity) ⟩
  swap-curry-≅.to ∘ [ g , [ id , id ]₁ ]₁
    ≈⟨ conjugate-from swap-curry-≅ swap-curry-≅ (swap-curry-natural id g id) ⟩
  [ id ⊗₁ g , id ]₁ ∘ swap-curry-≅.to       ∎

private module Naturality (A B C X : Obj) where
  Selfᵒ = opE selfEnrichment

  K* K⊗ : Functor Selfᵒ selfEnrichment
  K* = homʳ [ A , C ]₀
  K⊗ = homʳ C ∘F (A ⊗Fᵒᵖ-)

  module K* = Functor K*
  module K⊗ = Functor K⊗
  module C* = Functor (homʳ C)
  module A⊗- = Functor (A ⊗Fᵒᵖ-)

  abstract
    K⊗β : uncurry (K⊗.₁ {X = B} {Y = X})
      ≈ (internal-∘ {Y = A ⊗₀ B} {Z = C} {X = A ⊗₀ X} ∘ σ⇒) ∘
        (A⊗-.₁ {X = B} {Y = X} ⊗₁ id)
    K⊗β = begin
      uncurry K⊗.₁                      ≈⟨ uncurry-∘ ⟩
      uncurry C*.₁ ∘ (A⊗-.₁ ⊗₁ id)      ≈⟨ eval-curry ⟩∘⟨refl ⟩
      (internal-∘ ∘ σ⇒) ∘ (A⊗-.₁ ⊗₁ id) ∎

    split-composition-evaluation : {f : W ⇒ (([ B , [ A , C ]₀ ]₀ ⊗₀ [ X , B ]₀) ⊗₀ X) ⊗₀ A} →
      ((eval {B} { [ A , C ]₀ } ∘ (id ⊗₁ eval {X} {B}) ∘ α⇒) ⊗₁ id) ∘ f
      ≈ (eval {B} { [ A , C ]₀ } ⊗₁ id) ∘
        (((id ⊗₁ eval {X} {B}) ⊗₁ id) ∘ ((α⇒ ⊗₁ id) ∘ f))
    split-composition-evaluation {f = f} = begin
      ((eval ∘ (id ⊗₁ eval) ∘ α⇒) ⊗₁ id) ∘ f                    ≈⟨ split₁³ ⟩∘⟨refl ⟩
      ((eval ⊗₁ id) ∘ ((id ⊗₁ eval) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ f    ≈⟨ assoc²βε ⟩
      (eval ⊗₁ id) ∘ (((id ⊗₁ eval) ⊗₁ id) ∘ ((α⇒ ⊗₁ id) ∘ f))  ∎

    ⊚ᵒ-β : uncurry (internal-∘ {Y = B} {Z = [ A , C ]₀} {X = X} ∘ σ⇒)
      ≈ (eval {B} {[ A , C ]₀} ∘ (id ⊗₁ eval {X} {B}) ∘ α⇒) ∘ (σ⇒ ⊗₁ id)
    ⊚ᵒ-β = uncurry-∘ ○ (eval-internal-∘ ⟩∘⟨refl)

  abstract
    swap-curry-⊚ : uncurry (swap-curry-≅.to {A} {X} {C}) ∘
        (uncurry (K*.₁ {X = B} {Y = X}) ⊗₁ id)
      ≈ eval ∘ (uncurry (internal-∘ ∘ σ⇒) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
    swap-curry-⊚ = begin
      uncurry swap-curry-≅.to ∘ (uncurry K*.₁ ⊗₁ id)
        ≈⟨ swap-curry-≅.β ⟩∘⟨ eval-curry ⟩⊗⟨refl ⟩
      (((eval ∘ (eval ⊗₁ id)) ∘ α⇐) ∘ (id ⊗₁ σ⇒)) ∘ ((internal-∘ ∘ σ⇒) ⊗₁ id)
        ≈⟨ assoc²αε ⟩
      (eval ∘ (eval ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ ((internal-∘ ∘ σ⇒) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ whisker-comm ⟩
      (eval ∘ (eval ⊗₁ id)) ∘ α⇐ ∘ ((internal-∘ ∘ σ⇒) ⊗₁ id) ∘ (id ⊗₁ σ⇒)
        ≈⟨ refl⟩∘⟨ extendʳ α⇐-⊗id-commute ⟩
      (eval ∘ (eval ⊗₁ id)) ∘ (((internal-∘ ∘ σ⇒) ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
        ≈⟨ center merge₁ˡ ⟩
      eval ∘ (uncurry (internal-∘ ∘ σ⇒) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∎

    evaluate-⊚ᵒ : eval {A} {C} ∘
        (uncurry (internal-∘ ∘ σ⇒) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
      ≈ uncurry (eval {B} {[ A , C ]₀}) ∘ (((id ⊗₁ eval {X} {B}) ⊗₁ id) ∘
        ((α⇒ ⊗₁ id) ∘ (((σ⇒ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ σ⇒)))))
    evaluate-⊚ᵒ = begin
      eval ∘ (uncurry (internal-∘ ∘ σ⇒) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
        ≈⟨ refl⟩∘⟨ (⊚ᵒ-β ⟩⊗⟨refl ⟩∘⟨refl) ⟩
      eval ∘ (((eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (σ⇒ ⊗₁ id)) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
        ≈⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
      eval ∘ (((eval ∘ (id ⊗₁ eval) ∘ α⇒) ⊗₁ id) ∘
        (((σ⇒ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ σ⇒))))
        ≈⟨ pushʳ split-composition-evaluation ⟩
      uncurry eval ∘ (((id ⊗₁ eval) ⊗₁ id) ∘
        ((α⇒ ⊗₁ id) ∘ (((σ⇒ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ σ⇒))))) ∎

    transpose-⊗-eval : uncurry (eval {B} {[ A , C ]₀}) ∘
        (((id ⊗₁ eval {X} {B}) ⊗₁ id) ∘
        ((α⇒ ⊗₁ id) ∘ (((σ⇒ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ σ⇒)))))
      ≈ uncurry (swap-curry-≅.to {A} {B} {C}) ∘
        (id ⊗₁ uncurry (A⊗-.₁ {X = B} {Y = X})) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
    transpose-⊗-eval = begin
      uncurry eval ∘ (((id ⊗₁ eval) ⊗₁ id) ∘
        ((α⇒ ⊗₁ id) ∘ (((σ⇒ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ σ⇒)))))
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ rebracket-pair-swaps ⟩
      uncurry eval ∘ (((id ⊗₁ eval) ⊗₁ id) ∘ (α⇐ ∘
        ((id ⊗₁ α⇐) ∘ ((id ⊗₁ (id ⊗₁ σ⇒)) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))))))
        ≈⟨ refl⟩∘⟨ extendʳ (⟺ assoc-commute-to) ⟩
      uncurry eval ∘ (α⇐ ∘ ((id ⊗₁ (eval ⊗₁ id)) ∘
        ((id ⊗₁ α⇐) ∘ ((id ⊗₁ (id ⊗₁ σ⇒)) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))))))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc²εβ ⟩
      uncurry eval ∘ (α⇐ ∘ (((id ⊗₁ (eval ⊗₁ id)) ∘ (id ⊗₁ α⇐) ∘
        (id ⊗₁ (id ⊗₁ σ⇒))) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (merge₂³ ⟩∘⟨refl) ⟩
      uncurry eval ∘ (α⇐ ∘ ((id ⊗₁ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))) ∘
        (α⇒ ∘ (σ⇒ ⊗₁ id))))
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ evalᵀ A X B) ⟩∘⟨refl ⟩
      uncurry eval ∘ (α⇐ ∘ ((id ⊗₁ (σ⇒ ∘ ((id ⊗₁ eval) ∘ α⇒ ∘
        (σ⇒ ⊗₁ id) ∘ α⇐))) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      uncurry eval ∘ (α⇐ ∘ ((id ⊗₁ σ⇒) ∘
        ((id ⊗₁ ((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id)))))
        ≈⟨ assoc²εα ⟩
      ((uncurry eval ∘ α⇐) ∘ (id ⊗₁ σ⇒)) ∘
        (id ⊗₁ ((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
        ≈˘⟨ swap-curry-≅.β ⟩∘⟨refl ⟩
      uncurry swap-curry-≅.to ∘ (id ⊗₁ ((id ⊗₁ eval) ∘ α⇒ ∘
        (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
        ≈˘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗F-eval ⟩∘⟨refl) ⟩
      uncurry swap-curry-≅.to ∘ (id ⊗₁ uncurry A⊗-.₁) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∎

    ⊚-swap-curry : eval ∘ (uncurry (internal-∘ ∘ σ⇒) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
      ≈ uncurry (swap-curry-≅.to {A} {B} {C}) ∘
        (id ⊗₁ uncurry (A⊗-.₁ {X = B} {Y = X})) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
    ⊚-swap-curry = begin
      eval ∘ (uncurry (internal-∘ ∘ σ⇒) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
        ≈⟨ evaluate-⊚ᵒ ⟩
      uncurry eval ∘ (((id ⊗₁ eval) ⊗₁ id) ∘
        ((α⇒ ⊗₁ id) ∘ (((σ⇒ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ σ⇒)))))
        ≈⟨ transpose-⊗-eval ⟩
      uncurry swap-curry-≅.to ∘ (id ⊗₁ uncurry A⊗-.₁) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∎

  swap-curry-evaluation : uncurry (swap-curry-≅.to {A} {X} {C}) ∘
      (uncurry (K*.₁ {X = B} {Y = X}) ⊗₁ id)
    ≈ uncurry (swap-curry-≅.to {A} {B} {C}) ∘
      (id ⊗₁ uncurry (A⊗-.₁ {X = B} {Y = X})) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
  swap-curry-evaluation = begin
    uncurry swap-curry-≅.to ∘ (uncurry K*.₁ ⊗₁ id)                      ≈⟨ swap-curry-⊚ ⟩
    eval ∘ (uncurry (internal-∘ ∘ σ⇒) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)          ≈⟨ ⊚-swap-curry ⟩
    uncurry swap-curry-≅.to ∘ (id ⊗₁ uncurry A⊗-.₁) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)   ∎

  swap-curry□ : swap-curry-≅.to {A} {X} {C} ∘ uncurry (K*.₁ {X = B} {Y = X})
    ≈ uncurry (K⊗.₁ {X = B} {Y = X}) ∘ (id ⊗₁ swap-curry-≅.to {A} {B} {C})
  swap-curry□ = uncurry-injective (begin
    uncurry (swap-curry-≅.to ∘ uncurry K*.₁)                  ≈⟨ uncurry-∘ ⟩
    uncurry swap-curry-≅.to ∘ (uncurry K*.₁ ⊗₁ id)            ≈⟨ swap-curry-evaluation ⟩
    uncurry swap-curry-≅.to ∘ (id ⊗₁ uncurry A⊗-.₁) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈˘⟨ evaluate-precomposition ⟩
    uncurry (uncurry K⊗.₁) ∘ ((id ⊗₁ swap-curry-≅.to) ⊗₁ id)  ≈˘⟨ uncurry-∘ ⟩
    uncurry (uncurry K⊗.₁ ∘ (id ⊗₁ swap-curry-≅.to))          ∎)

  swap-curry□⁻¹ : swap-curry-≅.from {A} {X} {C} ∘ uncurry (K⊗.₁ {X = B} {Y = X})
    ≈ uncurry (K*.₁ {X = B} {Y = X}) ∘ (id ⊗₁ swap-curry-≅.from {A} {B} {C})
  swap-curry□⁻¹ = ⟺ (conjugate-to
    (idᵢ ⊗ᵢ swap-curry-≅) swap-curry-≅ swap-curry□)

-- Naturality of transposition with a fixed result object.
private
  module SwapCurryNatural (A C : Obj) =
    SelfNatural {F = homʳ [ A , C ]₀} {G = homʳ C ∘F (A ⊗Fᵒᵖ-)}

swap-curry-NI : NaturalIsomorphism (homʳ [ A , C ]₀) (homʳ C ∘F (A ⊗Fᵒᵖ-))
swap-curry-NI {A} {C} = SwapCurryNatural.pointwise-iso A C
  (≅.sym swap-curry-≅)
  λ { {X} {Y} → Naturality.swap-curry□ A X C Y }
