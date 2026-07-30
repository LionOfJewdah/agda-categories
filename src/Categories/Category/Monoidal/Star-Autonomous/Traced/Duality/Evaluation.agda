{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Traced using (Traced)

-- The enriched extranaturality hexagon for the compact-closed unit constructed
-- from a trace and a dualizing object (Hajgató & Hasegawa, TAC 28(7), 2013,
-- Lemma 3.3 and Corollary 3.4).

module Categories.Category.Monoidal.Star-Autonomous.Traced.Duality.Evaluation
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (Cl : Closed M) (T : Traced M) where

open import Data.Product using (_,_)
open import Relation.Unary using (Pred)

open import Categories.Category.Monoidal.Braided M using (Braided)
open import Categories.Category.Monoidal.Symmetric M using (Symmetric)
import Categories.Category.Monoidal.Symmetric.Properties as SymProps
import Categories.Category.Construction.Core 𝒞 as Core
import Categories.Category.Monoidal.Interchange.Braided as BraidedInterchange
import Categories.Category.Monoidal.Interchange.Symmetric as SymmetricInterchange

open Category 𝒞
open Monoidal M
open Traced T using (trace; trace⟨_⟩; slide; tightenₗ; tightenᵣ; vanishing₁; superposing; symmetric)
open Symmetric symmetric using (braided; braiding; commutative)
open Braided braided using (hexagon₂)
open Closed Cl using ([_,_]₀; [_,_]₁; [-,_]; [_,-]; [-,-])

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.CupCap M
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided symmetric)
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Morphism 𝒞 using (_≅_; Iso; IsIso; module ≅)
open import Categories.Morphism.Duality 𝒞 using (≅⇒op-≅)
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Category.Product using (Product; _※_; πˡ; πʳ)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper; _ⓘᵥ_)
open Shorthands
open BraidShorthands
open Core.Shorthands using (idᵢ)
open SymProps symmetric using (braiding-selfInverse; cup-swap)

open import Categories.Category.Monoidal.Star-Autonomous.Traced.Base Cl T public

private
  variable
    A A′ B B′ C C′ D E F P Q R W X Y Z : Obj

import Categories.Category.Monoidal.Star-Autonomous.Traced.Duality.Construction as Construction

module Dualized (⊥ : Obj) (dualizing : IsDualizing ⊥) where

  open Construction.Dualized Cl T ⊥ dualizing

  private
    module Interchange = BraidedInterchange braided
    module SymmetricSwap = SymmetricInterchange symmetric

    i⇒ : (A ⊗₀ B) ⊗₀ (C ⊗₀ D) ⇒ (A ⊗₀ C) ⊗₀ (B ⊗₀ D)
    i⇒ = Interchange.swapInner.from

    j⇒ : (A ⊗₀ B) ⊗₀ (C ⊗₀ D) ⇒ (A ⊗₀ C) ⊗₀ (B ⊗₀ D)
    j⇒ = Interchange.swapInner′.from

  -- Uncurrying `φ⁻¹ ∘ M` (for any `M` into `X ⊗₀ [ Y , unit ]₀`): fold `φ⁻¹ = [ Ψ , id ]₁ ∘ δ⇒`
  -- and `δ⇒ = curry (eval ∘ σ⇒)`, so the two `curry`-reindexings collect on the argument side.
  uncurry-φ⇐ : {M : W ⇒ X ⊗₀ [ Y , unit ]₀} →
      uncurry (φ⇐′ X Y ∘ M) ≈ (eval ∘ σ⇒) ∘ (M ⊗₁ id) ∘ (id ⊗₁ Ψ′ X Y)
  uncurry-φ⇐ {M = M} = begin
    uncurry (φ⇐′ _ _ ∘ M)                              ≈⟨ uncurry-resp-≈ (φ⇐-merge′ _ _ ⟩∘⟨refl) ⟩
    uncurry (([ Ψ′ _ _ , id ]₁ ∘ δ⇒) ∘ M)              ≈⟨ uncurry-resp-≈ assoc ⟩
    uncurry ([ Ψ′ _ _ , id ]₁ ∘ δ⇒ ∘ M)                ≈⟨ uncurry-resp-≈ (refl⟩∘⟨ ⟺ curry-∘) ⟩
    uncurry ([ Ψ′ _ _ , id ]₁ ∘ curry ((eval ∘ σ⇒) ∘ (M ⊗₁ id)))
      ≈⟨ uncurry-resp-≈ hom-curryᵣ ⟩
    uncurry (curry (((eval ∘ σ⇒) ∘ (M ⊗₁ id)) ∘ (id ⊗₁ Ψ′ _ _)))
      ≈⟨ eval-curry ⟩
    ((eval ∘ σ⇒) ∘ (M ⊗₁ id)) ∘ (id ⊗₁ Ψ′ _ _)        ≈⟨ assoc ⟩
    (eval ∘ σ⇒) ∘ (M ⊗₁ id) ∘ (id ⊗₁ Ψ′ _ _)          ∎

  -- The two variable layers of `φ⁻¹` at general `Y`, fused: swap-curry after folding `[⊥,⊥]₀ ≅ unit`.
  sᵍ : (Y : Obj) → [ Y , unit ]₀ ⇒ [ ⊥ ⊗₀ Y , ⊥ ]₀
  sᵍ Y = _≅_.to (swap-curry-≅ {⊥} {Y} {⊥}) ∘ [ id , _≅_.to ⊥*-≅ ]₁

  swap-curry-to-uncurry :
      uncurry (_≅_.to (swap-curry-≅ {P} {Q} {R}))
    ≈ eval ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
  swap-curry-to-uncurry = begin
    uncurry ([ σ⇒ , id ]₁ ∘ uncurry₂)             ≈⟨ uncurry-∘ ⟩
    uncurry [ σ⇒ , id ]₁ ∘ (uncurry₂ ⊗₁ id)       ≈⟨ (eval-comm ○ identityˡ) ⟩∘⟨refl ⟩
    (eval ∘ (id ⊗₁ σ⇒)) ∘ (uncurry₂ ⊗₁ id)        ≈⟨ assoc ⟩
    eval ∘ (id ⊗₁ σ⇒) ∘ (uncurry₂ ⊗₁ id)          ≈⟨ refl⟩∘⟨ ⟺ whisker-comm ⟩
    eval ∘ (uncurry₂ ⊗₁ id) ∘ (id ⊗₁ σ⇒)          ≈⟨ pullˡ eval-curry ⟩
    (uncurry eval ∘ α⇐) ∘ (id ⊗₁ σ⇒)              ≈⟨ assoc ⟩
    uncurry eval ∘ α⇐ ∘ (id ⊗₁ σ⇒)                ≈⟨ assoc ⟩
    eval ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)         ∎

  sᵍ-reindex :
      (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
        ∘ ([ id , _≅_.to ⊥*-≅ ]₁ ⊗₁ id {⊥ ⊗₀ Y})
    ≈ ((_≅_.to ⊥*-≅ ∘ eval {Y} {unit}) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
  sᵍ-reindex {Y} = begin
    (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ ([ id , _≅_.to ⊥*-≅ ]₁ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ whisker-comm ⟩
    (eval ⊗₁ id) ∘ α⇐ ∘ ([ id , _≅_.to ⊥*-≅ ]₁ ⊗₁ id) ∘ (id ⊗₁ σ⇒)
      ≈⟨ refl⟩∘⟨ extendʳ α⇐-⊗id-commute ⟩
    (eval ⊗₁ id) ∘ (([ id , _≅_.to ⊥*-≅ ]₁ ⊗₁ id) ⊗₁ id)
      ∘ α⇐ ∘ (id ⊗₁ σ⇒)
      ≈⟨ pullˡ merge₁ˡ ⟩
    ((eval ∘ ([ id , _≅_.to ⊥*-≅ ]₁ ⊗₁ id)) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
      ≈⟨ (eval-comm-cod ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    ((_≅_.to ⊥*-≅ ∘ eval) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)  ∎

  sᵍ-eval :
      uncurry (sᵍ Y)
    ≈ (ρ⇒ {⊥} ∘ σ⇒) ∘ (eval {Y} {unit} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
  sᵍ-eval {Y} = begin
    uncurry (_≅_.to (swap-curry-≅ {⊥} {Y} {⊥}) ∘ [ id , _≅_.to ⊥*-≅ ]₁)
      ≈⟨ uncurry-∘ ⟩
    uncurry (_≅_.to (swap-curry-≅ {⊥} {Y} {⊥}))
      ∘ ([ id , _≅_.to ⊥*-≅ ]₁ ⊗₁ id)
      ≈⟨ swap-curry-to-uncurry ⟩∘⟨refl ⟩
    (eval ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
      ∘ ([ id , _≅_.to ⊥*-≅ ]₁ ⊗₁ id)
      ≈⟨ assoc ⟩
    eval ∘ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
      ∘ ([ id , _≅_.to ⊥*-≅ ]₁ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ assoc²βε ⟩
    eval ∘ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
      ∘ ([ id , _≅_.to ⊥*-≅ ]₁ ⊗₁ id))
      ≈⟨ refl⟩∘⟨ sᵍ-reindex ⟩
    eval ∘ ((_≅_.to ⊥*-≅ ∘ eval) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
      ≈⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
    eval ∘ (_≅_.to ⊥*-≅ ⊗₁ id) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)
      ≈⟨ pullˡ (refl⟩∘⟨ (⊥to-fold ⟩⊗⟨refl) ○ eval-curry) ⟩
    (ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)  ∎

  sᵍ-internal-∘ :
      uncurry (sᵍ X ∘ internal-∘ {Y} {unit} {X})
    ≈ ((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
        ∘ (internal-∘ ⊗₁ id)
  sᵍ-internal-∘ = uncurry-∘ ○ (sᵍ-eval ⟩∘⟨refl)

  sᵍ-internal-evaluate :
      uncurry (sᵍ X ∘ internal-∘ {Y} {unit} {X}) ∘ (id ⊗₁ eval {Y} {⊥ ⊗₀ X}) ∘ σ⇒
    ≈ (((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
        ∘ (internal-∘ ⊗₁ id)) ∘ (id ⊗₁ eval) ∘ σ⇒
  sᵍ-internal-evaluate = begin
    uncurry (sᵍ _ ∘ internal-∘) ∘ (id ⊗₁ eval) ∘ σ⇒
      ≈⟨ sᵍ-internal-∘ ⟩∘⟨refl ⟩
    (((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
      ∘ (internal-∘ ⊗₁ id)) ∘ (id ⊗₁ eval) ∘ σ⇒
      ∎

  swap-evaluate : {f : A ⇒ B} {g : C ⇒ [ B , D ]₀} →
    (eval ∘ σ⇒) ∘ (f ⊗₁ g) ≈ uncurry g ∘ (id ⊗₁ f) ∘ σ⇒
  swap-evaluate {f = f} {g} = begin
    (eval ∘ σ⇒) ∘ (f ⊗₁ g)       ≈⟨ assoc ⟩
    eval ∘ σ⇒ ∘ (f ⊗₁ g)         ≈⟨ refl⟩∘⟨ σ⇒-comm ⟩
    eval ∘ (g ⊗₁ f) ∘ σ⇒         ≈⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
    eval ∘ (g ⊗₁ id) ∘ (id ⊗₁ f) ∘ σ⇒  ≈⟨ sym-assoc ⟩
    uncurry g ∘ (id ⊗₁ f) ∘ σ⇒  ∎

  sᵍ-read : {f : A ⇒ ⊥ ⊗₀ B} →
      (eval {⊥ ⊗₀ B} {⊥} ∘ σ⇒) ∘ (f ⊗₁ sᵍ B)
    ≈ ((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
        ∘ (id ⊗₁ f) ∘ σ⇒
  sᵍ-read {f = f} = begin
    (eval ∘ σ⇒) ∘ (f ⊗₁ sᵍ _)       ≈⟨ swap-evaluate ⟩
    uncurry (sᵍ _) ∘ (id ⊗₁ f) ∘ σ⇒  ≈⟨ sᵍ-eval ⟩∘⟨refl ⟩
    ((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
      ∘ (id ⊗₁ f) ∘ σ⇒               ∎

  rotate : A ⊗₀ (B ⊗₀ C) ⇒ (A ⊗₀ C) ⊗₀ B
  rotate = α⇐ ∘ (id ⊗₁ σ⇒)

  rotate-natural :
    {f : A ⇒ A′} {g : B ⇒ B′} {h : C ⇒ C′} →
    rotate ∘ (f ⊗₁ (g ⊗₁ h)) ≈ ((f ⊗₁ h) ⊗₁ g) ∘ rotate
  rotate-natural {f = f} {g} {h} = begin
    (α⇐ ∘ (id ⊗₁ σ⇒)) ∘ (f ⊗₁ (g ⊗₁ h))    ≈⟨ assoc ⟩
    α⇐ ∘ (id ⊗₁ σ⇒) ∘ (f ⊗₁ (g ⊗₁ h))      ≈⟨ refl⟩∘⟨ parallel id-comm-sym σ⇒-comm ⟩
    α⇐ ∘ (f ⊗₁ (h ⊗₁ g)) ∘ (id ⊗₁ σ⇒)      ≈⟨ sym-assoc ⟩
    (α⇐ ∘ (f ⊗₁ (h ⊗₁ g))) ∘ (id ⊗₁ σ⇒)    ≈⟨ assoc-commute-to ⟩∘⟨refl ⟩
    (((f ⊗₁ h) ⊗₁ g) ∘ α⇐) ∘ (id ⊗₁ σ⇒)    ≈⟨ assoc ⟩
    ((f ⊗₁ h) ⊗₁ g) ∘ α⇐ ∘ (id ⊗₁ σ⇒)      ≡⟨⟩
    ((f ⊗₁ h) ⊗₁ g) ∘ rotate                 ∎

  rotate-middle : {f : B ⇒ B′} →
    rotate ∘ (id {A} ⊗₁ (f ⊗₁ id {C})) ≈ (id ⊗₁ f) ∘ rotate
  rotate-middle = rotate-natural ○ ((⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl)

  split-read :
      ((eval {Y} {unit} ∘ (id ⊗₁ eval {X} {Y}) ∘ α⇒) ⊗₁ id {⊥}) ∘ rotate
    ≈ ((eval {Y} {unit} ⊗₁ id {⊥})
        ∘ (((id ⊗₁ eval {X} {Y}) ∘ α⇒) ⊗₁ id)
      ) ∘ rotate
  split-read = split₁ˡ ⟩∘⟨refl

  compose-read :
      ((eval {X} {unit} ⊗₁ id {⊥}) ∘ rotate)
        ∘ (internal-∘ {Y} {unit} {X} ⊗₁ id {⊥ ⊗₀ X})
    ≈ (eval {Y} {unit} ⊗₁ id {⊥})
        ∘ (((id ⊗₁ eval {X} {Y}) ∘ α⇒) ⊗₁ id)
        ∘ rotate
  compose-read {X} {Y} = begin
    ((eval ⊗₁ id) ∘ rotate) ∘ (internal-∘ ⊗₁ id)       ≈⟨ assoc ⟩
    (eval ⊗₁ id) ∘ rotate ∘ (internal-∘ ⊗₁ id)         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⟺ ⊗.identity) ⟩
    (eval ⊗₁ id) ∘ rotate ∘ (internal-∘ ⊗₁ (id ⊗₁ id)) ≈⟨ refl⟩∘⟨ rotate-natural ⟩
    (eval ⊗₁ id) ∘ ((internal-∘ ⊗₁ id) ⊗₁ id) ∘ rotate ≈⟨ pullˡ merge₁ˡ ⟩
    ((eval ∘ (internal-∘ ⊗₁ id)) ⊗₁ id) ∘ rotate       ≈⟨ (eval-internal-∘ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    ((eval {Y} {unit} ∘ (id ⊗₁ eval {X} {Y}) ∘ α⇒) ⊗₁ id {⊥}) ∘ rotate
      ≈⟨ split-read ⟩
    ((eval {Y} {unit} ⊗₁ id {⊥})
      ∘ (((id ⊗₁ eval {X} {Y}) ∘ α⇒) ⊗₁ id)) ∘ rotate  ≈⟨ assoc ⟩
    (eval {Y} {unit} ⊗₁ id {⊥})
      ∘ (((id ⊗₁ eval {X} {Y}) ∘ α⇒) ⊗₁ id) ∘ rotate  ∎

  compose-read-closed :
      (((ρ⇒ {⊥} ∘ σ⇒) ∘ (eval {X} {unit} ⊗₁ id) ∘ rotate)
        ∘ (internal-∘ {Y} {unit} {X} ⊗₁ id {⊥ ⊗₀ X}))
    ≈ (ρ⇒ ∘ σ⇒) ∘ (eval {Y} {unit} ⊗₁ id)
        ∘ (((id ⊗₁ eval {X} {Y}) ∘ α⇒) ⊗₁ id)
        ∘ rotate
  compose-read-closed = begin
    ((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ rotate) ∘ (internal-∘ ⊗₁ id)
      ≈⟨ assoc ⟩
    (ρ⇒ ∘ σ⇒) ∘ (((eval ⊗₁ id) ∘ rotate) ∘ (internal-∘ ⊗₁ id))
      ≈⟨ refl⟩∘⟨ compose-read ⟩
    (ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (((id ⊗₁ eval) ∘ α⇒) ⊗₁ id) ∘ rotate  ∎

  middle-cup : {u : unit ⇒ Y ⊗₀ Q} →
      α⇐ ∘ (id {P} ⊗₁ α⇒) ∘ (id ⊗₁ (u ⊗₁ id {F})) ∘ (id ⊗₁ λ⇐)
    ≈ α⇐ ∘ (id ⊗₁ cup-bendˡ u)
  middle-cup = refl⟩∘⟨ merge₂³

  cup-bendʳ-expand : {u : unit ⇒ Y ⊗₀ Q} →
    cup-bendʳ {A = P} u ≈ α⇐ {P} {Y} {Q} ∘ (id {P} ⊗₁ u) ∘ ρ⇐
  cup-bendʳ-expand = Equiv.refl

  reverse-assoc-core :
    α⇐ {A} {B} {C} ∘ (id ⊗₁ σ⇒) ∘ σ⇒ ∘ α⇐ ≈ σ⇒ ∘ (id ⊗₁ σ⇒)
  reverse-assoc-core = ⟺ (switch-fromtoˡ associator
    (switch-tofromˡ (idᵢ ⊗ᵢ σ) (switch-tofromˡ σ assoc-reverse)))

  reverse-assoc :
      α⇐ {A} {B} {C} ∘ (id ⊗₁ σ⇒) ∘ σ⇒
    ≈ (σ⇒ ∘ (id ⊗₁ σ⇒)) ∘ α⇒
  reverse-assoc = switch-tofromʳ associator (⟺ assoc²εβ ○ reverse-assoc-core)

  rotate-assoc-expanded :
    ∀ {A B C D} →
      (α⇒ {A} {D} {C} ⊗₁ id {B})
        ∘ (α⇐ ∘ (id ⊗₁ σ⇒ {B} {C}))
        ∘ (α⇐ ∘ (id ⊗₁ σ⇒ {B ⊗₀ C} {D}))
    ≈ (α⇐ {A} {D ⊗₀ C} {B} ∘ (id ⊗₁ σ⇒ {B} {D ⊗₀ C}))
        ∘ (id ⊗₁ (id ⊗₁ σ⇒ {C} {D}))
        ∘ (id ⊗₁ α⇒ {B} {C} {D})
  rotate-assoc-expanded {A} {B} {C} {D} = begin
    (α⇒ {A} {D} {C} ⊗₁ id {B})
      ∘ (α⇐ ∘ (id ⊗₁ σ⇒ {B} {C}))
      ∘ (α⇐ ∘ (id ⊗₁ σ⇒ {B ⊗₀ C} {D}))
      ≈⟨ refl⟩∘⟨ assoc ⟩
    (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒ {B} {C}) ∘ α⇐
      ∘ (id ⊗₁ σ⇒ {B ⊗₀ C} {D})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨
        extendʳ (α⇐-id⊗-commute {A = A} {B = D} {k = σ⇒ {B} {C}}) ⟩
    (α⇒ ⊗₁ id) ∘ α⇐ ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ σ⇒ {B} {C}))
      ∘ (id ⊗₁ σ⇒ {B ⊗₀ C} {D})
      ≈˘⟨ assoc²βε ⟩
    ((α⇒ ⊗₁ id) ∘ α⇐ ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ σ⇒ {B} {C}))
      ∘ (id ⊗₁ σ⇒ {B ⊗₀ C} {D})
      ≈⟨ pentagon-collapse-inv {A = A} {B = D} {C = C} {D = B} ⟩∘⟨refl ⟩
    (α⇐ {A} {D ⊗₀ C} {B} ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ (id ⊗₁ σ⇒ {B} {C}))
      ∘ (id ⊗₁ σ⇒ {B ⊗₀ C} {D})
      ≈⟨ assoc ⟩
    α⇐ {A} {D ⊗₀ C} {B} ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ σ⇒ {B} {C}))
      ∘ (id ⊗₁ σ⇒ {B ⊗₀ C} {D})
      ≈⟨ refl⟩∘⟨ merge₂³ ⟩
    α⇐ {A} {D ⊗₀ C} {B} ∘ (id ⊗₁
      (α⇐ ∘ (id ⊗₁ σ⇒ {B} {C}) ∘ σ⇒ {B ⊗₀ C} {D}))
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ reverse-assoc {A = D} {B = C} {C = B}) ⟩
    α⇐ {A} {D ⊗₀ C} {B} ∘ (id ⊗₁
      ((σ⇒ {B} {D ⊗₀ C} ∘ (id ⊗₁ σ⇒ {C} {D})) ∘ α⇒))
      ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
    α⇐ {A} {D ⊗₀ C} {B} ∘ (id ⊗₁
      (σ⇒ {B} {D ⊗₀ C} ∘ (id ⊗₁ σ⇒ {C} {D})))
      ∘ (id ⊗₁ α⇒)
      ≈⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
    α⇐ {A} {D ⊗₀ C} {B} ∘
      ((id ⊗₁ σ⇒ {B} {D ⊗₀ C}) ∘ (id ⊗₁ (id ⊗₁ σ⇒ {C} {D})))
      ∘ (id ⊗₁ α⇒)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    α⇐ {A} {D ⊗₀ C} {B} ∘ (id ⊗₁ σ⇒ {B} {D ⊗₀ C})
      ∘ (id ⊗₁ (id ⊗₁ σ⇒ {C} {D}))
      ∘ (id ⊗₁ α⇒ {B} {C} {D})
      ≈⟨ sym-assoc ⟩
    (α⇐ {A} {D ⊗₀ C} {B} ∘ (id ⊗₁ σ⇒ {B} {D ⊗₀ C}))
      ∘ (id ⊗₁ (id ⊗₁ σ⇒ {C} {D})) ∘ (id ⊗₁ α⇒ {B} {C} {D})  ∎

  rotate-assoc :
      (α⇒ {A} {D} {C} ⊗₁ id {B})
        ∘ rotate {A = A ⊗₀ D} {B} {C}
        ∘ rotate {A} {B ⊗₀ C} {D}
    ≈ rotate {A = A} {B = B} {C = D ⊗₀ C}
        ∘ (id ⊗₁ (id ⊗₁ σ⇒ {C} {D}))
        ∘ (id ⊗₁ α⇒ {B} {C} {D})
  rotate-assoc = rotate-assoc-expanded

  split-rotate-head : {g : D ⊗₀ C ⇒ E} →
      ((id {A} ⊗₁ g) ∘ α⇒ {A} {D} {C}) ⊗₁ id {B}
    ≈ ((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
  split-rotate-head = split₁ʳ

  rotate-read : {g : D ⊗₀ C ⇒ E} →
      (((id {A} ⊗₁ g) ∘ α⇒) ⊗₁ id {B})
        ∘ rotate {A = A ⊗₀ D} {B} {C}
        ∘ rotate {A} {B ⊗₀ C} {D}
    ≈ rotate {A} {B} {E}
        ∘ (id ⊗₁ ((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒))
  rotate-read {g = g} = begin
    (((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ rotate ∘ rotate
      ≈⟨ split-rotate-head ⟩∘⟨refl ⟩
    (((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ rotate ∘ rotate
      ≈⟨ assoc ⟩
    ((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ rotate ∘ rotate
      ≈⟨ refl⟩∘⟨ rotate-assoc ⟩
    ((id ⊗₁ g) ⊗₁ id) ∘ rotate
      ∘ (id ⊗₁ (id ⊗₁ σ⇒)) ∘ (id ⊗₁ α⇒)
      ≈⟨ sym-assoc ⟩
    (((id ⊗₁ g) ⊗₁ id) ∘ rotate)
      ∘ (id ⊗₁ (id ⊗₁ σ⇒)) ∘ (id ⊗₁ α⇒)
      ≈˘⟨ rotate-natural ⟩∘⟨refl ⟩
    (rotate ∘ (id ⊗₁ (id ⊗₁ g)))
      ∘ (id ⊗₁ (id ⊗₁ σ⇒)) ∘ (id ⊗₁ α⇒)
      ≈⟨ assoc ⟩
    rotate ∘ (id ⊗₁ (id ⊗₁ g))
      ∘ (id ⊗₁ (id ⊗₁ σ⇒)) ∘ (id ⊗₁ α⇒)
      ≈⟨ refl⟩∘⟨ merge₂³ ⟩
    rotate ∘ (id ⊗₁ ((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒))  ∎

  cup-route-braid :
      (σ⇒ {Y} {P} ⊗₁ id {Q}) ∘ rotate {A = Y} {B = Q} {C = P} ∘ α⇒
    ≈ α⇐ {P} {Y} {Q} ∘ σ⇐ {P} {Y ⊗₀ Q}
  cup-route-braid {Y = Y} {P = P} {Q = Q} = begin
    (σ⇒ {Y} {P} ⊗₁ id {Q}) ∘ rotate ∘ α⇒ {Y} {Q} {P}
      ≈⟨ refl⟩∘⟨ assoc ⟩
    (σ⇒ {Y} {P} ⊗₁ id {Q}) ∘ α⇐ {Y} {P} {Q}
      ∘ (id {Y} ⊗₁ σ⇒ {Q} {P}) ∘ α⇒ {Y} {Q} {P}          ≈˘⟨ assoc²αε ⟩
    (((σ⇒ {Y} {P} ⊗₁ id {Q}) ∘ α⇐ {Y} {P} {Q})
      ∘ (id {Y} ⊗₁ σ⇒ {Q} {P})) ∘ α⇒ {Y} {Q} {P}
      ≈⟨ hexagon₂ ⟩∘⟨refl ⟩
    ((α⇐ {P} {Y} {Q} ∘ σ⇒ {Y ⊗₀ Q} {P}) ∘ α⇐ {Y} {Q} {P})
      ∘ α⇒ {Y} {Q} {P}                         ≈⟨ cancelʳ associator.isoˡ ⟩
    α⇐ ∘ σ⇒                                  ≈˘⟨ refl⟩∘⟨ braiding-selfInverse ⟩
    α⇐ ∘ σ⇐                                  ∎

  j⇒-expand :
      j⇒ {A} {B} {C} {D}
    ≈ α⇒ {A ⊗₀ C} {B} {D}
        ∘ ((α⇐ {A} {C} {B} ∘ (id ⊗₁ σ⇒ {B} {C}) ∘ α⇒ {A} {B} {C}) ⊗₁ id)
        ∘ α⇐ {A ⊗₀ B} {C} {D}
  j⇒-expand = Equiv.refl

  cup-open-route : {u : unit ⇒ Y ⊗₀ Q} →
      (σ⇒ {Y} {P} ⊗₁ id {Q ⊗₀ F})
        ∘ i⇒ {A = Y} {B = Q} {C = P} {D = F}
        ∘ cup-openˡ {A = P ⊗₀ F} u
    ≈ α⇒ ∘ (cup-bendʳ {A = P} u ⊗₁ id {F})
  cup-open-route {Y = Y} {Q = Q} {P = P} {F = F} {u = u} = begin
    (σ⇒ ⊗₁ id) ∘ i⇒ ∘ cup-openˡ u
      ≈⟨ refl⟩∘⟨ (Interchange.swapInner-coherent ⟩∘⟨refl) ⟩
    (σ⇒ {Y} {P} ⊗₁ id {Q ⊗₀ F}) ∘ j⇒ {Y} {Q} {P} {F}
      ∘ cup-openˡ {A = P ⊗₀ F} u
      ≈⟨ extendʳ (refl⟩∘⟨ j⇒-expand) ⟩
    (σ⇒ ⊗₁ id)
      ∘ ((α⇒ ∘ ((α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id) ∘ α⇐) ∘ cup-openˡ u)
      ≈⟨ refl⟩∘⟨ assoc²βε ⟩
    (σ⇒ {Y} {P} ⊗₁ id {Q ⊗₀ F}) ∘ α⇒ {Y ⊗₀ P} {Q} {F}
      ∘ ((α⇐ {Y} {P} {Q} ∘ (id ⊗₁ σ⇒ {Q} {P}) ∘ α⇒ {Y} {Q} {P}) ⊗₁ id)
      ∘ α⇐ {Y ⊗₀ Q} {P} {F} ∘ cup-openˡ {A = P ⊗₀ F} u
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ((sym-assoc ⟩⊗⟨refl) ⟩∘⟨refl) ⟩
    (σ⇒ ⊗₁ id) ∘ α⇒ ∘ ((rotate ∘ α⇒) ⊗₁ id) ∘ α⇐ ∘ cup-openˡ u
      ≈˘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
    (σ⇒ ⊗₁ (id ⊗₁ id)) ∘ α⇒
      ∘ ((rotate ∘ α⇒) ⊗₁ id) ∘ α⇐ ∘ cup-openˡ u
      ≈˘⟨ extendʳ assoc-commute-from ⟩
    α⇒ ∘ ((σ⇒ ⊗₁ id) ⊗₁ id) ∘ ((rotate ∘ α⇒) ⊗₁ id) ∘ α⇐ ∘ cup-openˡ u
      ≈⟨ refl⟩∘⟨ pullˡ merge₁ˡ ⟩
    α⇒ ∘ (((σ⇒ ⊗₁ id) ∘ rotate ∘ α⇒) ⊗₁ id) ∘ α⇐ ∘ cup-openˡ u
      ≈⟨ refl⟩∘⟨ (cup-route-braid ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    α⇒ {P ⊗₀ Y} {Q} {F}
      ∘ ((α⇐ {P} {Y} {Q} ∘ σ⇐ {P} {Y ⊗₀ Q}) ⊗₁ id {F})
      ∘ α⇐ {Y ⊗₀ Q} {P} {F} ∘ cup-openˡ u
      ≈⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
    α⇒ {P ⊗₀ Y} {Q} {F} ∘ (α⇐ {P} {Y} {Q} ⊗₁ id {F})
      ∘ (σ⇐ {P} {Y ⊗₀ Q} ⊗₁ id {F})
      ∘ α⇐ {Y ⊗₀ Q} {P} {F} ∘ cup-openˡ u
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ switch-fromtoˡ associator cup-openˡ-natural ⟩
    α⇒ ∘ (α⇐ ⊗₁ id) ∘ (σ⇐ ⊗₁ id) ∘ (cup-openˡ u ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ˡ ⟩
    α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((σ⇐ ∘ cup-openˡ u) ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (cup-swap ⟩⊗⟨refl) ⟩
    α⇒ ∘ (α⇐ ⊗₁ id) ∘ (cup-openʳ u ⊗₁ id)
      ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
    α⇒ ∘ (cup-bendʳ u ⊗₁ id)  ∎

  cup-route-left : {u : unit ⇒ Y ⊗₀ Q} →
      σ⇒ ∘ α⇐ ∘ (id {P} ⊗₁ cup-bendˡ {A = F} u)
    ≈ σ⇒ ∘ α⇒ ∘ (cup-bendʳ {A = P} u ⊗₁ id {F})
  cup-route-left {Y = Y} {Q = Q} {P = P} {F = F} {u = u} = begin
    σ⇒ ∘ α⇐ ∘ (id ⊗₁ cup-bendˡ u)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ merge₂ˡ ⟩
    σ⇒ ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ cup-openˡ u)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cup-openʳ-whisker ⟩
    σ⇒ {P ⊗₀ Y} {Q ⊗₀ F} ∘ α⇐ {P} {Y} {Q ⊗₀ F}
      ∘ (id ⊗₁ α⇒ {Y} {Q} {F}) ∘ α⇒ {P} {Y ⊗₀ Q} {F}
      ∘ (cup-openʳ {A = P} u ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    σ⇒ {P ⊗₀ Y} {Q ⊗₀ F} ∘ α⇐ {P} {Y} {Q ⊗₀ F}
      ∘ ((id ⊗₁ α⇒ {Y} {Q} {F}) ∘ α⇒ {P} {Y ⊗₀ Q} {F})
      ∘ (cup-openʳ {A = P} u ⊗₁ id)
      ≈⟨ refl⟩∘⟨ pullˡ (⟺ assoc-from-coherence) ⟩
    σ⇒ {P ⊗₀ Y} {Q ⊗₀ F} ∘ ((α⇒ {P ⊗₀ Y} {Q} {F}
      ∘ (α⇐ {P} {Y} {Q} ⊗₁ id)) ∘ (cup-openʳ {A = P} u ⊗₁ id))
      ≈⟨ refl⟩∘⟨ assoc ⟩
    σ⇒ ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ (cup-openʳ u ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ˡ ⟩
    σ⇒ ∘ α⇒ ∘ (cup-bendʳ u ⊗₁ id)  ∎

  j⇒-rotate :
      j⇒ {A} {B} {C} {D}
    ≈ α⇒ {A ⊗₀ C} {B} {D}
        ∘ ((rotate {A = A} {B = B} {C = C} ∘ α⇒ {A} {B} {C}) ⊗₁ id)
        ∘ α⇐ {A ⊗₀ B} {C} {D}
  j⇒-rotate =
    j⇒-expand ○ (refl⟩∘⟨ ((sym-assoc ⟩⊗⟨refl) ⟩∘⟨refl))

  cup-bend-interchange : {u : unit ⇒ Y ⊗₀ Q} →
      α⇒ {P ⊗₀ Y} {F} {Q}
        ∘ ((rotate {A = P} {B = F} {C = Y} ∘ α⇒) ⊗₁ id)
        ∘ cup-bendʳ {A = P ⊗₀ F} u
    ≈ j⇒ {P} {F} {Y} {Q} ∘ cup-openʳ u
  cup-bend-interchange {u = u} = begin
    α⇒ ∘ ((rotate ∘ α⇒) ⊗₁ id) ∘ cup-bendʳ u
      ≈˘⟨ refl⟩∘⟨ assoc ⟩
    α⇒ ∘ (((rotate ∘ α⇒) ⊗₁ id) ∘ α⇐) ∘ cup-openʳ u
      ≈˘⟨ pushˡ j⇒-rotate ⟩
    j⇒ ∘ cup-openʳ u  ∎

  cancel-routed-braid :
      (id {P ⊗₀ Y} ⊗₁ σ⇒ {F} {Q}) ∘ (σ⇒ {Y} {P} ⊗₁ σ⇒ {Q} {F})
    ≈ σ⇒ {Y} {P} ⊗₁ id {Q ⊗₀ F}
  cancel-routed-braid = begin
    (id ⊗₁ σ⇒) ∘ (σ⇒ ⊗₁ σ⇒)  ≈˘⟨ ⊗-distrib-over-∘ ⟩
    (id ∘ σ⇒) ⊗₁ (σ⇒ ∘ σ⇒)    ≈⟨ identityˡ ⟩⊗⟨ commutative ⟩
    σ⇒ ⊗₁ id                    ∎

  cup-bend-route : {u : unit ⇒ Y ⊗₀ Q} →
      (id {P ⊗₀ Y} ⊗₁ σ⇒ {F} {Q}) ∘ α⇒
        ∘ ((rotate {A = P} {B = F} {C = Y} ∘ α⇒) ⊗₁ id {Q})
        ∘ cup-bendʳ {A = P ⊗₀ F} u
    ≈ α⇒ ∘ (cup-bendʳ {A = P} u ⊗₁ id {F})
  cup-bend-route {Y = Y} {Q = Q} {P = P} {F = F} {u = u} = begin
    (id ⊗₁ σ⇒) ∘ α⇒ ∘ ((rotate ∘ α⇒) ⊗₁ id) ∘ cup-bendʳ u
      ≈⟨ refl⟩∘⟨ cup-bend-interchange ⟩
    (id {P ⊗₀ Y} ⊗₁ σ⇒ {F} {Q}) ∘ j⇒ {P} {F} {Y} {Q} ∘ cup-openʳ u
      ≈˘⟨ refl⟩∘⟨ (Interchange.swapInner-coherent
        {X₁ = P} {X₂ = F} {Y₁ = Y} {Y₂ = Q} ⟩∘⟨refl) ⟩
    (id {P ⊗₀ Y} ⊗₁ σ⇒ {F} {Q}) ∘ i⇒ {P} {F} {Y} {Q} ∘ cup-openʳ u
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cup-swap ⟩
    (id ⊗₁ σ⇒) ∘ i⇒ ∘ σ⇐ ∘ cup-openˡ u
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding-selfInverse ⟩∘⟨refl ⟩
    (id {P ⊗₀ Y} ⊗₁ σ⇒ {F} {Q}) ∘ i⇒ {P} {F} {Y} {Q}
      ∘ σ⇒ {Y ⊗₀ Q} {P ⊗₀ F} ∘ cup-openˡ u
      ≈˘⟨ refl⟩∘⟨ extendʳ SymmetricSwap.swapInner-braiding′ ⟩
    (id ⊗₁ σ⇒) ∘ (σ⇒ ⊗₁ σ⇒) ∘ i⇒ ∘ cup-openˡ u
      ≈⟨ pullˡ cancel-routed-braid ⟩
    (σ⇒ ⊗₁ id) ∘ i⇒ ∘ cup-openˡ u
      ≈⟨ cup-open-route ⟩
    α⇒ ∘ (cup-bendʳ u ⊗₁ id)  ∎

  route-reverse-assoc :
      rotate {A = Q} {B = P ⊗₀ Y} {C = F} ∘ σ⇒ {(P ⊗₀ Y) ⊗₀ F} {Q}
    ≈ (σ⇒ {P ⊗₀ Y} {Q ⊗₀ F} ∘ (id ⊗₁ σ⇒ {F} {Q}))
        ∘ α⇒ {P ⊗₀ Y} {F} {Q}
  route-reverse-assoc {Q = Q} {P = P} {Y = Y} {F = F} = begin
    (α⇐ ∘ (id ⊗₁ σ⇒)) ∘ σ⇒  ≈⟨ assoc ⟩
    α⇐ ∘ (id ⊗₁ σ⇒) ∘ σ⇒    ≈⟨ reverse-assoc {A = Q} {B = F} {C = P ⊗₀ Y} ⟩
    (σ⇒ ∘ (id ⊗₁ σ⇒)) ∘ α⇒  ∎

  cup-route-right : {u : unit ⇒ Y ⊗₀ Q} →
      rotate {A = Q} {B = P ⊗₀ Y} {C = F}
        ∘ (id ⊗₁ (rotate {A = P} {B = F} {C = Y} ∘ α⇒))
        ∘ σ⇒ ∘ cup-bendʳ u
    ≈ σ⇒ ∘ α⇒ ∘ (cup-bendʳ {A = P} u ⊗₁ id {F})
  cup-route-right {Y = Y} {Q = Q} {P = P} {F = F} {u = u} = begin
    rotate ∘ (id ⊗₁ (rotate ∘ α⇒)) ∘ σ⇒ ∘ cup-bendʳ u
      ≈⟨ refl⟩∘⟨ extendʳ (⟺ σ⇒-comm) ⟩
    rotate {A = Q} {B = P ⊗₀ Y} {C = F} ∘ σ⇒
      ∘ ((rotate {A = P} {B = F} {C = Y} ∘ α⇒) ⊗₁ id)
      ∘ cup-bendʳ u
      ≈⟨ extendʳ route-reverse-assoc ⟩
    (σ⇒ ∘ (id ⊗₁ σ⇒)) ∘ α⇒
      ∘ ((rotate ∘ α⇒) ⊗₁ id) ∘ cup-bendʳ u
      ≈⟨ assoc ⟩
    σ⇒ ∘ (id ⊗₁ σ⇒) ∘ α⇒
      ∘ ((rotate ∘ α⇒) ⊗₁ id) ∘ cup-bendʳ u
      ≈⟨ refl⟩∘⟨ cup-bend-route ⟩
    σ⇒ ∘ α⇒ ∘ (cup-bendʳ u ⊗₁ id)  ∎

  cup-route : {u : unit ⇒ Y ⊗₀ Q} →
      σ⇒ ∘ α⇐ ∘ (id {P} ⊗₁ cup-bendˡ {A = F} u)
    ≈ rotate {A = Q} {B = P ⊗₀ Y} {C = F}
        ∘ (id ⊗₁ (rotate {A = P} {B = F} {C = Y} ∘ α⇒))
        ∘ σ⇒ ∘ cup-bendʳ u
  cup-route = cup-route-left ○ ⟺ cup-route-right

  merge-route :
    {f : P ⊗₀ Y ⇒ B ⊗₀ X} {g : F ⊗₀ X ⇒ Z} →
      (id {Q} ⊗₁ ((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒))
        ∘ (id ⊗₁ ((f ⊗₁ id) ∘ rotate ∘ α⇒))
    ≈ id ⊗₁
        ((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒
          ∘ (f ⊗₁ id) ∘ rotate ∘ α⇒)
  merge-route {f = f} {g = g} = begin
    (id ⊗₁ ((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒))
      ∘ (id ⊗₁ ((f ⊗₁ id) ∘ rotate ∘ α⇒))
      ≈⟨ merge₂ˡ ⟩
    id ⊗₁ (((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒)
      ∘ ((f ⊗₁ id) ∘ rotate ∘ α⇒))
      ≈⟨ refl⟩⊗⟨ assoc ⟩
    id ⊗₁ ((id ⊗₁ g) ∘ ((id ⊗₁ σ⇒) ∘ α⇒)
      ∘ ((f ⊗₁ id) ∘ rotate ∘ α⇒))
      ≈⟨ refl⟩⊗⟨ (refl⟩∘⟨ assoc) ⟩
    id ⊗₁
      ((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ∘ (f ⊗₁ id) ∘ rotate ∘ α⇒)  ∎

  route-core :
    {u : unit ⇒ Y ⊗₀ Q} {f : P ⊗₀ Y ⇒ B ⊗₀ X} {g : F ⊗₀ X ⇒ Z} →
      ((((id {Q} ⊗₁ g) ∘ α⇒) ⊗₁ id {B}) ∘ rotate)
        ∘ ((id {Q ⊗₀ F} ⊗₁ f) ∘ σ⇒)
        ∘ α⇐ ∘ (id {P} ⊗₁ cup-bendˡ u)
    ≈ (rotate ∘ (id ⊗₁
          ((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒
            ∘ (f ⊗₁ id) ∘ rotate ∘ α⇒)))
        ∘ σ⇒ ∘ cup-bendʳ u
  route-core {u = u} {f} {g} = begin
    ((((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ rotate)
      ∘ ((id ⊗₁ f) ∘ σ⇒) ∘ α⇐ ∘ (id ⊗₁ cup-bendˡ u)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    ((((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ rotate)
      ∘ (id ⊗₁ f) ∘ σ⇒ ∘ α⇐ ∘ (id ⊗₁ cup-bendˡ u)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cup-route ⟩
    ((((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ rotate)
      ∘ (id ⊗₁ f) ∘ rotate
      ∘ (id ⊗₁ (rotate ∘ α⇒)) ∘ σ⇒ ∘ cup-bendʳ u
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    ((((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ rotate)
      ∘ ((id ⊗₁ f) ∘ rotate)
      ∘ (id ⊗₁ (rotate ∘ α⇒)) ∘ σ⇒ ∘ cup-bendʳ u
      ≈˘⟨ refl⟩∘⟨ rotate-middle ⟩∘⟨refl ⟩
    ((((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ rotate)
      ∘ (rotate ∘ (id ⊗₁ (f ⊗₁ id)))
      ∘ (id ⊗₁ (rotate ∘ α⇒)) ∘ σ⇒ ∘ cup-bendʳ u
      ≈⟨ refl⟩∘⟨ assoc ⟩
    ((((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ rotate)
      ∘ rotate ∘ (id ⊗₁ (f ⊗₁ id))
      ∘ (id ⊗₁ (rotate ∘ α⇒)) ∘ σ⇒ ∘ cup-bendʳ u
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    ((((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ rotate)
      ∘ rotate ∘ (id ⊗₁ ((f ⊗₁ id) ∘ rotate ∘ α⇒))
      ∘ σ⇒ ∘ cup-bendʳ u
      ≈⟨ sym-assoc ⟩
    (((((id ⊗₁ g) ∘ α⇒) ⊗₁ id) ∘ rotate) ∘ rotate)
      ∘ (id ⊗₁ ((f ⊗₁ id) ∘ rotate ∘ α⇒))
      ∘ σ⇒ ∘ cup-bendʳ u
      ≈⟨ (assoc ○ rotate-read) ⟩∘⟨refl ⟩
    (rotate ∘ (id ⊗₁ ((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒)))
      ∘ (id ⊗₁ ((f ⊗₁ id) ∘ rotate ∘ α⇒))
      ∘ σ⇒ ∘ cup-bendʳ u
      ≈⟨ sym-assoc ⟩
      ((rotate ∘ (id ⊗₁ ((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒)))
        ∘ (id ⊗₁ ((f ⊗₁ id) ∘ rotate ∘ α⇒)))
        ∘ σ⇒ ∘ cup-bendʳ u
        ≈⟨ pullʳ merge-route ⟩∘⟨refl ⟩
    (rotate ∘ (id ⊗₁
        ((id ⊗₁ g) ∘ (id ⊗₁ σ⇒) ∘ α⇒
          ∘ (f ⊗₁ id) ∘ rotate ∘ α⇒)))
      ∘ σ⇒ ∘ cup-bendʳ u  ∎

  evaluation-route-expand :
      (id ⊗₁ eval {X} {Y}) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ∘ (eval {Y} {B ⊗₀ X} ⊗₁ id) ∘ rotate ∘ α⇒
    ≈ (id ⊗₁ eval {X} {Y}) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ∘ (eval {Y} {B ⊗₀ X} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒
  evaluation-route-expand =
    refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ assoc)

  route-read : ∀ {X Y} →
      ((ρ⇒ ∘ σ⇒) ∘ (eval {Y} {unit} ⊗₁ id)
        ∘ (((id ⊗₁ eval {X} {Y}) ∘ α⇒) ⊗₁ id)
        ∘ rotate)
        ∘ ((id ⊗₁ eval {Y} {⊥ ⊗₀ X}) ∘ σ⇒)
        ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t {Y} ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
    ≈ (((ρ⇒ ∘ σ⇒) ∘ (eval {Y} {unit} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
        ∘ (id ⊗₁
          ((id ⊗₁ eval {X} {Y}) ∘ (id ⊗₁ σ⇒) ∘ α⇒
            ∘ (eval {Y} {⊥ ⊗₀ X} ⊗₁ id) ∘ rotate ∘ α⇒))
        ∘ σ⇒)
        ∘ α⇐ {[ Y , ⊥ ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀} {Y} {[ Y , unit ]₀}
        ∘ (id ⊗₁ t {Y}) ∘ ρ⇐
  route-read {X} {Y} = begin
    ((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (((id ⊗₁ eval) ∘ α⇒) ⊗₁ id) ∘ rotate)
      ∘ ((id ⊗₁ eval) ∘ σ⇒) ∘ α⇐
      ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ middle-cup ⟩
    ((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (((id ⊗₁ eval) ∘ α⇒) ⊗₁ id) ∘ rotate)
      ∘ ((id ⊗₁ eval) ∘ σ⇒) ∘ α⇐ ∘ (id ⊗₁ cup-bendˡ t)
      ≈⟨ sym-assoc ⟩∘⟨refl ⟩
    (((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id))
      ∘ ((((id ⊗₁ eval) ∘ α⇒) ⊗₁ id) ∘ rotate))
      ∘ ((id ⊗₁ eval) ∘ σ⇒) ∘ α⇐ ∘ (id ⊗₁ cup-bendˡ t)
      ≈⟨ pullʳ (route-core {u = t} {f = eval} {g = eval}) ⟩
    ((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id))
      ∘ (rotate ∘ (id ⊗₁
        ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
          ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒)))
      ∘ σ⇒ ∘ cup-bendʳ t
      ≈⟨ Equiv.refl ⟩
    ((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id))
      ∘ ((α⇐ ∘ (id ⊗₁ σ⇒)) ∘ (id ⊗₁
        ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
          ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒)))
      ∘ σ⇒ ∘ cup-bendʳ t
      ≈⟨ sym-assoc ⟩
    (((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id))
      ∘ ((α⇐ ∘ (id ⊗₁ σ⇒)) ∘ (id ⊗₁
        ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
          ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒))))
      ∘ σ⇒ ∘ cup-bendʳ t
      ≈⟨ sym-assoc ⟩∘⟨refl ⟩
    ((((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id)) ∘ (α⇐ ∘ (id ⊗₁ σ⇒)))
      ∘ (id ⊗₁
        ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
          ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒)))
      ∘ σ⇒ ∘ cup-bendʳ t
      ≈⟨ (assoc ⟩∘⟨refl) ⟩∘⟨refl ⟩
    (((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
      ∘ (id ⊗₁
        ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
          ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒)))
      ∘ σ⇒ ∘ cup-bendʳ t
      ≈⟨ assoc²γβ ⟩
    (((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
      ∘ (id ⊗₁
        ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
          ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒))
      ∘ σ⇒)
      ∘ cup-bendʳ {A = [ Y , ⊥ ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀} t
      ≈⟨ refl⟩∘⟨ cup-bendʳ-expand
        {P = [ Y , ⊥ ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀} {u = t {Y}} ⟩
    (((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
      ∘ (id ⊗₁
        ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
          ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒))
      ∘ σ⇒)
      ∘ α⇐ {[ Y , ⊥ ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀} {Y} {[ Y , unit ]₀}
      ∘ (id ⊗₁ t) ∘ ρ⇐  ∎
