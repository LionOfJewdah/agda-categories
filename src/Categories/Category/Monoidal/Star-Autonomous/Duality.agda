{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Dualizing objects and Barr's canonical double-dual map.

module Categories.Category.Monoidal.Star-Autonomous.Duality
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (S : Symmetric M) (Cl : Closed M) where

open import Data.Product using (_,_)
open import Relation.Unary using (Pred)

open Category 𝒞
open Monoidal M
open Symmetric S using (braided)
open Closed Cl using ([_,_]₀; [_,_]₁; [-,_]; [_,-]; [-,-])

open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Closed.Currying Cl
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Adjunction S Cl public
  using (swap-curry-≅; swap-curry-natural; swap-curry⇐-commʳ)
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Symmetric.Properties S using (unitʳ-braiding)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Morphism 𝒞 using (_≅_; Iso; IsIso; module ≅)
open import Categories.Morphism.Duality 𝒞 using (≅⇒op-≅)
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Functor.Properties using ([_]-resp-≅)
open Shorthands
open BraidShorthands

private
  variable
    A B C : Obj -- closed arguments
    W X Y Z : Obj -- source, comparison, and codomain roles

-- Barr's canonical map into the double dual.
δ : (D : Obj) → A ⇒ [ [ A , D ]₀ , D ]₀
δ D = curry (eval ∘ σ⇒)

δ-natural : {D : Obj} (f : A ⇒ B) →
  [ [ f , id ]₁ , id ]₁ ∘ δ D ≈ δ {A = B} D ∘ f
δ-natural {D = D} f = begin
  [ [ f , id ]₁ , id ]₁ ∘ δ D                 ≈⟨ hom-curryᵣ ⟩
  curry ((eval ∘ σ⇒) ∘ (id ⊗₁ [ f , id ]₁))   ≈⟨ curry-resp-≈ (pullʳ σ⇒-comm) ⟩
  curry (eval ∘ ([ f , id ]₁ ⊗₁ id) ∘ σ⇒)     ≈⟨ curry-resp-≈ (extendʳ eval-comm-dom) ⟩
  curry (eval ∘ (id ⊗₁ f) ∘ σ⇒)               ≈˘⟨ curry-resp-≈ (pullʳ σ⇒-comm) ⟩
  curry ((eval ∘ σ⇒) ∘ (f ⊗₁ id))             ≈⟨ curry-∘ ⟩
  δ D ∘ f ∎

private
  δ-name-eval : {D : Obj} {f : unit ⇒ A} →
    (eval {A} {D} ∘ σ⇒) ∘ (f ⊗₁ id)
    ≈ (eval ∘ (id ⊗₁ f) ∘ ρ⇐) ∘ λ⇒
  δ-name-eval {f = f} = begin
    (eval ∘ σ⇒) ∘ (f ⊗₁ id)         ≈⟨ pullʳ σ⇒-comm ⟩
    eval ∘ (id ⊗₁ f) ∘ σ⇒           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding-coherence-σ′ ⟩
    eval ∘ (id ⊗₁ f) ∘ ρ⇐ ∘ λ⇒      ≈⟨ assoc²εβ ⟩
    (eval ∘ (id ⊗₁ f) ∘ ρ⇐) ∘ λ⇒    ∎

  unit-braid : {f : unit ⇒ A} →
    σ⇒ ∘ (id {W} ⊗₁ f) ∘ ρ⇐ ≈ (f ⊗₁ id {W}) ∘ λ⇐
  unit-braid {f = f} = begin
    σ⇒ ∘ (id ⊗₁ f) ∘ ρ⇐      ≈⟨ extendʳ σ⇒-comm ⟩
    (f ⊗₁ id) ∘ σ⇒ ∘ ρ⇐      ≈⟨ refl⟩∘⟨ unitʳ-braiding ⟩
    (f ⊗₁ id) ∘ λ⇐           ∎

δ-name : {D : Obj} {f : unit ⇒ A} →
  δ D ∘ f ≈ ⌜ eval ∘ (id ⊗₁ f) ∘ ρ⇐ ⌝
δ-name = ⟺ curry-∘ ○ curry-resp-≈ δ-name-eval

uncurry-δ : {f : A ⇒ [ B , C ]₀} {g : W ⇒ B} →
  uncurry ([ f , id ]₁ ∘ δ C ∘ g) ≈ eval ∘ (f ⊗₁ g) ∘ σ⇒
uncurry-δ {f = f} {g} = begin
  uncurry ([ f , id ]₁ ∘ δ _ ∘ g)           ≈⟨ uncurry-∘ ⟩
  uncurry [ f , id ]₁ ∘ ((δ _ ∘ g) ⊗₁ id)   ≈⟨ eval-comm-dom ⟩∘⟨refl ⟩
  (eval ∘ (id ⊗₁ f)) ∘ ((δ _ ∘ g) ⊗₁ id)    ≈⟨ pullʳ merge₂ˡ ⟩
  eval ∘ ((δ _ ∘ g) ⊗₁ (f ∘ id))            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ identityʳ ⟩
  eval ∘ ((δ _ ∘ g) ⊗₁ f)                   ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  eval ∘ (δ _ ⊗₁ id) ∘ (g ⊗₁ f)             ≈⟨ pullˡ eval-curry ⟩
  (eval ∘ σ⇒) ∘ (g ⊗₁ f)                    ≈⟨ pullʳ σ⇒-comm ⟩
  eval ∘ (f ⊗₁ g) ∘ σ⇒                      ∎

uncurry-δ-at : {f : A ⇒ [ B , C ]₀} {g : W ⇒ B} {x : unit ⇒ A} →
  uncurry ([ f , id ]₁ ∘ δ C ∘ g) ∘ (id ⊗₁ x) ∘ ρ⇐
  ≈ (eval ∘ ((f ∘ x) ⊗₁ g)) ∘ λ⇐
uncurry-δ-at {f = f} {g} {x} = begin
  uncurry ([ f , id ]₁ ∘ δ _ ∘ g) ∘ (id ⊗₁ x) ∘ ρ⇐  ≈⟨ uncurry-δ ⟩∘⟨refl ⟩
  (eval ∘ (f ⊗₁ g) ∘ σ⇒) ∘ (id ⊗₁ x) ∘ ρ⇐           ≈⟨ assoc²βε ⟩
  eval ∘ (f ⊗₁ g) ∘ σ⇒ ∘ (id ⊗₁ x) ∘ ρ⇐             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unit-braid ⟩
  eval ∘ (f ⊗₁ g) ∘ (x ⊗₁ id) ∘ λ⇐                  ≈⟨ pushʳ (pullˡ merge₁ʳ) ⟩
  (eval ∘ ((f ∘ x) ⊗₁ g)) ∘ λ⇐                      ∎

IsDualizing : Pred Obj _
IsDualizing D = ∀ {A} → IsIso (δ {A} D)

module Dualized (⊥ : Obj) (dualizing : IsDualizing ⊥) where
  infix 30 _*
  _* : Obj → Obj
  A * = [ A , ⊥ ]₀

  -- Every object is canonically isomorphic to its double dual.
  **-≅ : A ≅ (A *) *
  **-≅ = record
    { from = δ ⊥
    ; to = IsIso.inv dualizing
    ; iso = IsIso.iso dualizing
    }
  module **-≅ {A} = _≅_ (**-≅ {A})

  -- The dual of the dualizing object is the tensor unit.
  ⊥*-≅ : (⊥ *) ≅ unit
  ⊥*-≅ = ≅.trans ([ [-, ⊥ ] ]-resp-≅ (≅⇒op-≅ (unit-hom {⊥}))) (≅.sym **-≅)
  module ⊥*-≅ = _≅_ ⊥*-≅
