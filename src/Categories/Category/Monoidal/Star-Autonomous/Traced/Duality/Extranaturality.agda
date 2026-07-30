{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Traced using (Traced)

-- The enriched extranaturality hexagon for the compact-closed unit constructed
-- from a trace and a dualizing object (Hajgató & Hasegawa, TAC 28(7), 2013,
-- Lemma 3.3 and Corollary 3.4).

module Categories.Category.Monoidal.Star-Autonomous.Traced.Duality.Extranaturality
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (Cl : Closed M) (T : Traced M) where

open import Data.Product using (_,_)
open import Relation.Unary using (Pred)

open import Categories.Category.Monoidal.Symmetric M using (Symmetric)
import Categories.Category.Monoidal.Symmetric.Properties as SymProps

open Category 𝒞
open Monoidal M
open Traced T using (trace; trace⟨_⟩; slide; tightenₗ; tightenᵣ; vanishing₁; superposing; symmetric)
open Symmetric symmetric using (braiding; commutative)
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
open SymProps symmetric using (braiding-selfInverse)

open import Categories.Category.Monoidal.Star-Autonomous.Traced.Base Cl T public

private
  variable
    A B C X Y Z : Obj

import Categories.Category.Monoidal.Star-Autonomous.Traced.Duality.Construction as Construction
import Categories.Category.Monoidal.Star-Autonomous.Traced.Duality.Evaluation as Evaluation

module Dualized (⊥ : Obj) (dualizing : IsDualizing ⊥) where

  open Construction.Dualized Cl T ⊥ dualizing
  open Evaluation.Dualized Cl T ⊥ dualizing

  ----------------------------------------------------------------------
  -- The extraordinary-ℂ-natural wedge (the hexagon `Closed/CompactClosed.agda` consumes) for a
  -- unit family `s : ∀ {X} → unit ⇒ X ⊗₀ X *`.  Its two legs read a function `[ X , Y ]₀`:
  -- apply it to the `X` produced by `s {X}`, or dualize and internally compose it into the `Y *`
  -- produced by `s {Y}`.  By Corollary 3.4 `t` satisfies this wedge; that is `t-extranatural`.
  Extra-H : (∀ {X} → unit ⇒ X ⊗₀ [ X , unit ]₀) → Set _
  Extra-H s = ∀ {X Y} →
      (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ s {X}) ∘ ρ⇐
    ≈ (id ⊗₁ internal-∘) ∘ α⇒ ∘ (s {Y} ⊗₁ id) ∘ λ⇐

  private
    -- `φ⁻¹`'s inner map at general `Y`, merged: the double dual `δ⇒` reindexed by `sᵍ`.
    φ-input : ⊥ ⊗₀ Y ⇒ [ [ Y , unit ]₀ , ⊥ ]₀
    φ-input = [ sᵍ _ , id ]₁ ∘ δ⇒

    -- `v₃⁻¹ ∘ v₂⁻¹` at general `Y` is the single hom action `[ sᵍ Y , id ]₁`.
    φ-input-fold : v₃⁻¹ {Y} ∘ v₂⁻¹ {Y} ∘ δ⇒ ≈ φ-input
    φ-input-fold = sym-assoc ○ (hom-∘ᵣ ⟩∘⟨refl)

    -- `Ψ`'s three covariant layers merge to `[ id , φ-input Y ]₁` (as in `Ψ-fold`, at general `X , Y`).
    Ψ-factor : Ψ′ X Y ≈ uncurry₂ ∘ [ id , φ-input {Y = Y} ]₁
    Ψ-factor = begin
      Ψ′ _ _                                                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ homˡ-∘ ⟩
      uncurry₂ ∘ [ id , v₃⁻¹ ]₁ ∘ [ id , v₂⁻¹ ∘ δ⇒ ]₁               ≈⟨ refl⟩∘⟨ homˡ-∘ ⟩
      uncurry₂ ∘ [ id , v₃⁻¹ ∘ v₂⁻¹ ∘ δ⇒ ]₁                         ≈⟨ refl⟩∘⟨ [-,-].F-resp-≈ (Equiv.refl , φ-input-fold) ⟩
      uncurry₂ ∘ [ id , φ-input ]₁                                  ∎

    -- Uncurrying `Ψ′ X Y` (as in `uncurryΨ`, at general `X , Y`): `uncurry₂`'s double `eval`, with
    -- `φ-input Y` folded onto the inner one (`inner`, via `eval-comm-cod`).
    evaluate-reindexed :
      uncurry (eval {X} {[ [ Y , unit ]₀ , ⊥ ]₀})
        ∘ (([ id , φ-input {Y = Y} ]₁ ⊗₁ id) ⊗₁ id)
      ≈ eval ∘ ((φ-input ∘ eval) ⊗₁ id)
    evaluate-reindexed = begin
      (eval ∘ (eval ⊗₁ id)) ∘ (([ id , φ-input ]₁ ⊗₁ id) ⊗₁ id)
        ≈⟨ assoc ⟩
      eval ∘ (eval ⊗₁ id) ∘ (([ id , φ-input ]₁ ⊗₁ id) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
      eval ∘ ((eval ∘ ([ id , φ-input ]₁ ⊗₁ id)) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ (eval-comm-cod ⟩⊗⟨refl) ⟩
      eval ∘ ((φ-input ∘ eval) ⊗₁ id)  ∎

    uncurry-Ψ : uncurry (Ψ′ X Y) ≈ eval ∘ ((φ-input {Y = Y} ∘ eval) ⊗₁ id) ∘ α⇐
    uncurry-Ψ = begin
      eval ∘ (Ψ′ _ _ ⊗₁ id)                                  ≈⟨ refl⟩∘⟨ (Ψ-factor ⟩⊗⟨refl) ⟩
      eval ∘ ((uncurry₂ ∘ [ id , φ-input ]₁) ⊗₁ id)           ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
      eval ∘ (uncurry₂ ⊗₁ id) ∘ ([ id , φ-input ]₁ ⊗₁ id)     ≈⟨ pullˡ eval-curry ⟩
      (uncurry eval ∘ α⇐) ∘ ([ id , φ-input ]₁ ⊗₁ id)         ≈⟨ assoc ⟩
      uncurry eval ∘ α⇐ ∘ ([ id , φ-input ]₁ ⊗₁ id)           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⟺ ⊗.identity) ⟩
      uncurry eval ∘ α⇐ ∘ ([ id , φ-input ]₁ ⊗₁ (id ⊗₁ id))   ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩
      uncurry eval ∘ (([ id , φ-input ]₁ ⊗₁ id) ⊗₁ id) ∘ α⇐   ≈⟨ pullˡ evaluate-reindexed ⟩
      (eval ∘ ((φ-input ∘ eval) ⊗₁ id)) ∘ α⇐                  ≈⟨ assoc ⟩
      eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐                    ∎

    -- After uncurrying, `eval` reads the `Ψ`-function on the `M`-argument: fuse the two whiskers
    -- into one tensor and push the braiding to the front so `Ψ` and `M` sit on their own strands.
    evaluate-swapped : {g : A ⇒ [ B , ⊥ ]₀} {f : C ⇒ B} →
        (eval ∘ σ⇒) ∘ (f ⊗₁ id) ∘ (id ⊗₁ g) ≈ eval ∘ (g ⊗₁ f) ∘ σ⇒
    evaluate-swapped {g = g} {f = f} = begin
      (eval ∘ σ⇒) ∘ (f ⊗₁ id) ∘ (id ⊗₁ g)  ≈⟨ refl⟩∘⟨ ⟺ serialize₁₂ ⟩
      (eval ∘ σ⇒) ∘ (f ⊗₁ g)                ≈⟨ assoc ⟩
      eval ∘ σ⇒ ∘ (f ⊗₁ g)                  ≈⟨ refl⟩∘⟨ σ⇒-comm ⟩
      eval ∘ (g ⊗₁ f) ∘ σ⇒                  ∎

    -- Feeding an argument `M` to the `Ψ`-function: `eval ∘ (Ψ ⊗₁ M) = uncurry Ψ ∘ (id ⊗₁ M)`, then
    -- unfold `uncurry Ψ` by `uncurry-Ψ`.  This exposes `φ-input X`'s own `δ⇒`, ready to meet `t`'s `δ⇐`.
    evaluate-Ψ : (N : [ X , Y ]₀ ⇒ Y ⊗₀ [ X , unit ]₀) →
        eval ∘ (Ψ′ Y X ⊗₁ N) ∘ σ⇒
      ≈ (eval ∘ ((φ-input {Y = X} ∘ eval) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ N) ∘ σ⇒
    evaluate-Ψ N = begin
      eval ∘ (Ψ′ _ _ ⊗₁ N) ∘ σ⇒                         ≈⟨ refl⟩∘⟨ (serialize₁₂ ⟩∘⟨refl) ⟩
      eval ∘ ((Ψ′ _ _ ⊗₁ id) ∘ (id ⊗₁ N)) ∘ σ⇒          ≈⟨ refl⟩∘⟨ assoc ⟩
      eval ∘ (Ψ′ _ _ ⊗₁ id) ∘ (id ⊗₁ N) ∘ σ⇒            ≈⟨ pullˡ uncurry-Ψ ⟩
      (eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ N) ∘ σ⇒  ∎

    -- The core of the hexagon: the enriched dinaturality of `τ̂`, fed through `φ⁻¹`'s inner map (as
    -- `φ-input X ∘ eval`).  Both legs feed the same `Wrap = eval ∘ ((φ-input X ∘ eval) ⊗₁ id) ∘ α⇐`; they agree
    -- because `φ-input` collapses the `φ` in `t` and `τ`'s dinaturality bridges the `X`- and `Y`-legs.
    hexagon-under-φ⇐ :
        (eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐)) ∘ σ⇒
      ≈ (eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐)) ∘ σ⇒

    φ-input-eval :
        φ-input ∘ eval {Y} {⊥ ⊗₀ X}
      ≈ curry ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ X))
    φ-input-eval = begin
      ([ sᵍ _ , id ]₁ ∘ δ⇒) ∘ eval                         ≈⟨ assoc ⟩
      [ sᵍ _ , id ]₁ ∘ δ⇒ ∘ eval                           ≈⟨ refl⟩∘⟨ ⟺ curry-∘ ⟩
      [ sᵍ _ , id ]₁ ∘ curry ((eval ∘ σ⇒) ∘ (eval ⊗₁ id)) ≈⟨ hom-curryᵣ ⟩
      curry (((eval ∘ σ⇒) ∘ (eval ⊗₁ id)) ∘ (id ⊗₁ sᵍ _)) ≈⟨ curry-resp-≈ assoc ⟩
      curry ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _))   ∎

    -- The shared outer read `Wrap = eval ∘ ((φ-input X ∘ eval) ⊗₁ id) ∘ α⇐` unfolds: `φ-input X ∘ eval` is a
    -- `curry` (fold `δ⇒ = curry (eval ∘ σ⇒)` and the reindex `sᵍ X`), so the outer `eval` un-currys it.
    evaluate-φ-input :
        eval ∘ ((φ-input ∘ eval {Y} {⊥ ⊗₀ X}) ⊗₁ id) ∘ α⇐ {[ Y , ⊥ ⊗₀ X ]₀} {Y} {[ X , unit ]₀}
      ≈ ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ X)) ∘ α⇐
    evaluate-φ-input = begin
      eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐                              ≈⟨ refl⟩∘⟨ (φ-input-eval ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      eval ∘ (curry ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ⊗₁ id) ∘ α⇐
        ≈⟨ pullˡ eval-curry ⟩
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ α⇐                 ∎

    -- The common `τ`-form both legs reduce to: apply `sᵍ X` (naming `⌜τ{X}⌝` back) after the trace's
    -- self-application, bridged by `τ`'s dinaturality.
    τ-composite : [ X , Y ]₀ ⊗₀ [ Y , ⊥ ⊗₀ X ]₀ ⇒ ⊥
    τ-composite = τ ∘ internal-∘ ∘ σ⇒

    -- The two evals plus the associator collapse into internal composition (`eval-internal-∘`),
    -- carrying `sᵍ X` along on the second tensor factor.
    evaluate-internal-∘ :
        (eval {Y} {⊥ ⊗₀ X} ⊗₁ id) ∘ (id ⊗₁ sᵍ X) ∘ ((id ⊗₁ eval {X} {Y}) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈ (eval ∘ (internal-∘ {Y} {⊥ ⊗₀ X} {X} ⊗₁ id)) ⊗₁ sᵍ X
    evaluate-internal-∘ = begin
      (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _) ∘ ((id ⊗₁ eval) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
        ≈⟨ sym-assoc ○ ((⟺ serialize₁₂) ⟩∘⟨refl) ⟩
      (eval ⊗₁ sᵍ _) ∘ ((id ⊗₁ eval) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
        ≈⟨ sym-assoc ○ ((⟺ ⊗.homomorphism ○ (Equiv.refl ⟩⊗⟨ identityʳ)) ⟩∘⟨refl) ⟩
      ((eval ∘ (id ⊗₁ eval)) ⊗₁ sᵍ _) ∘ (α⇒ ⊗₁ id)
        ≈⟨ ⟺ ⊗.homomorphism ○ (assoc ⟩⊗⟨ identityʳ) ⟩
      (eval ∘ (id ⊗₁ eval) ∘ α⇒) ⊗₁ sᵍ _
        ≈⟨ (⟺ eval-internal-∘) ⟩⊗⟨refl ⟩
      (eval ∘ (internal-∘ ⊗₁ id)) ⊗₁ sᵍ _ ∎

    -- The fundamental collapse: `φ⁻¹` at the diagonal names `τ`.  `t {X} = φ ∘ ⌜τ⌝`, so composing
    -- the concrete inverse `φ⁻¹` (`φ⇐′ X X`) cancels `φ` and leaves the name `⌜ τ {X} {⊥} ⌝`.
    φ⇐-t : φ⇐′ X X ∘ t {X} ≈ ⌜ τ {X} {⊥} ⌝
    φ⇐-t = cancelˡ (_≅_.isoˡ φ-≅)

    -- Braiding-unitor coherence (symmetric): `σ⇒ ∘ λ⇐ = ρ⇐`.
    braid-unit : σ⇒ {unit} {A} ∘ λ⇐ ≈ ρ⇐ {A}
    braid-unit = (⟺ braiding-selfInverse ⟩∘⟨refl) ○ braiding-coherence-inv

    -- Associator-unitor (right) triangle: `α⇐ ∘ (id ⊗ ρ⇐) = ρ⇐`.
    assoc-unitorʳ : α⇐ {A} {B} {unit} ∘ (id ⊗₁ ρ⇐ {B}) ≈ ρ⇐ {A ⊗₀ B}
    assoc-unitorʳ = (refl⟩∘⟨ ρ⇐-assoc) ○ cancelˡ associator.isoˡ

    -- Fold `φ⁻¹`'s read at the diagonal to the concrete `sᵍ X`-read: `uncurry (Ψ′ X X)`.
    uncurry-Ψ-diagonal :
      uncurry (Ψ′ X X) ≈ (eval ∘ σ⇒) ∘ (eval {X} {⊥ ⊗₀ X} ⊗₁ sᵍ X) ∘ α⇐
    uncurry-Ψ-diagonal = begin
      uncurry (Ψ′ _ _)                                    ≈⟨ uncurry-Ψ ⟩
      eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐                ≈⟨ evaluate-φ-input ⟩
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ α⇐   ≈⟨ (refl⟩∘⟨ (⟺ serialize₁₂)) ⟩∘⟨refl ⟩
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _)) ∘ α⇐                 ≈⟨ assoc ⟩
      (eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _) ∘ α⇐                   ∎

    -- Off-diagonal fold of `φ⁻¹`'s read (`uncurry-Ψ` then `evaluate-φ-input`, at `Ψ′ Y X`).
    uncurry-Ψ-off-diagonal :
      uncurry (Ψ′ Y X) ≈ ((eval ∘ σ⇒) ∘ (eval {Y} {⊥ ⊗₀ X} ⊗₁ id) ∘ (id ⊗₁ sᵍ X)) ∘ α⇐
    uncurry-Ψ-off-diagonal = uncurry-Ψ ○ evaluate-φ-input

    Ψ-t-split :
      Ψ′ X X ⊗₁ t {X} ≈ (Ψ′ X X ⊗₁ id) ∘ (id ⊗₁ t {X})
    Ψ-t-split = serialize₁₂

    evaluate-diagonal :
        (eval ∘ σ⇒) ∘ (eval {X} {⊥ ⊗₀ X} ⊗₁ sᵍ X)
          ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐
      ≈ eval ∘ (Ψ′ X X ⊗₁ t {X}) ∘ ρ⇐
    evaluate-diagonal {X} = begin
      (eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐
        ≈⟨ assoc²εβ ⟩
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _) ∘ α⇐) ∘ (id ⊗₁ t {X}) ∘ ρ⇐
        ≈˘⟨ uncurry-Ψ-diagonal ⟩∘⟨refl ⟩
      uncurry (Ψ′ _ _) ∘ (id ⊗₁ t {X}) ∘ ρ⇐
        ≈⟨ assoc ⟩
      eval ∘ (Ψ′ _ _ ⊗₁ id) ∘ (id ⊗₁ t {X}) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ pullˡ (⟺ Ψ-t-split) ⟩
      eval ∘ (Ψ′ _ _ ⊗₁ t {X}) ∘ ρ⇐  ∎

    uncurry-φ⇐-t :
      uncurry (φ⇐′ X X ∘ t {X}) ≈ eval ∘ (Ψ′ X X ⊗₁ t {X}) ∘ σ⇒
    uncurry-φ⇐-t = uncurry-φ⇐ ○ evaluate-swapped

    -- The diagonal collapse (Corollary 3.4's core).  Feeding the trace-witness `t {X}` to `φ⁻¹`'s
    -- read `sᵍ X` names `τ {X}` back (`φ⇐-t`: `φ⇐′ X X ∘ t {X} = ⌜ τ ⌝`); evaluating the name applies
    -- it (`uncurry ⌜ τ ⌝ = τ ∘ λ⇒`), and the unitors cancel.
    evaluate-t :
      (eval ∘ σ⇒) ∘ (eval {X} {⊥ ⊗₀ X} ⊗₁ sᵍ X) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐
      ≈ τ {X} {⊥}
    evaluate-t = begin
      (eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐
        ≈⟨ evaluate-diagonal ⟩
      eval ∘ (Ψ′ _ _ ⊗₁ t) ∘ ρ⇐
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ braid-unit ⟩
      eval ∘ (Ψ′ _ _ ⊗₁ t) ∘ σ⇒ ∘ λ⇐
        ≈⟨ assoc²εβ ⟩
      (eval ∘ (Ψ′ _ _ ⊗₁ t) ∘ σ⇒) ∘ λ⇐
        ≈˘⟨ uncurry-φ⇐-t ⟩∘⟨refl ⟩
      uncurry (φ⇐′ _ _ ∘ t) ∘ λ⇐
        ≈⟨ (refl⟩∘⟨ (φ⇐-t ⟩⊗⟨refl)) ⟩∘⟨refl ⟩
      uncurry ⌜ τ ⌝ ∘ λ⇐
        ≈⟨ eval-⌜⌝ ⟩∘⟨refl ⟩
      (τ ∘ λ⇒) ∘ λ⇐
        ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
      τ ∎

    t-open-natural : {f : A ⇒ B} →
        (α⇐ ∘ (id ⊗₁ t {Y}) ∘ ρ⇐) ∘ f
      ≈ ((f ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {Y}) ∘ ρ⇐
    t-open-natural {f = f} = begin
      (α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐) ∘ f            ≈⟨ assoc²βε ⟩
      α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐ ∘ f              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ-commute-to ⟩
      α⇐ ∘ (id ⊗₁ t) ∘ (f ⊗₁ id) ∘ ρ⇐      ≈⟨ refl⟩∘⟨ extendʳ (⟺ whisker-comm) ⟩
      α⇐ ∘ (f ⊗₁ id) ∘ (id ⊗₁ t) ∘ ρ⇐      ≈⟨ extendʳ α⇐-⊗id-commute ⟩
      ((f ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐  ∎

    evaluate-t-natural : {f : A ⇒ [ Y , ⊥ ⊗₀ Y ]₀} →
        ((eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ Y) ∘ α⇐ ∘ (id ⊗₁ t {Y}) ∘ ρ⇐) ∘ f
      ≈ (eval ∘ σ⇒) ∘ (uncurry f ⊗₁ sᵍ Y) ∘ α⇐ ∘ (id ⊗₁ t {Y}) ∘ ρ⇐
    evaluate-t-natural {f = f} = begin
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _) ∘ (α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐)) ∘ f
        ≈⟨ assoc²βε ⟩
      (eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _) ∘ (α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐) ∘ f
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ t-open-natural ⟩
      (eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _) ∘ ((f ⊗₁ id) ⊗₁ id)
        ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ pullˡ (⟺ ⊗.homomorphism ○ (Equiv.refl ⟩⊗⟨ identityʳ)) ⟩
      (eval ∘ σ⇒) ∘ ((eval ∘ (f ⊗₁ id)) ⊗₁ sᵍ _)
        ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐  ≡⟨⟩
      (eval ∘ σ⇒) ∘ (uncurry f ⊗₁ sᵍ _)
        ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐  ∎

    evaluate-t-curry : {g : A ⊗₀ Y ⇒ ⊥ ⊗₀ Y} →
        ((eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ Y) ∘ α⇐ ∘ (id ⊗₁ t {Y}) ∘ ρ⇐) ∘ curry g
      ≈ (eval ∘ σ⇒) ∘ (g ⊗₁ sᵍ Y) ∘ α⇐ ∘ (id ⊗₁ t {Y}) ∘ ρ⇐
    evaluate-t-curry {g = g} = begin
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐) ∘ curry g
        ≈⟨ evaluate-t-natural ⟩
      (eval ∘ σ⇒) ∘ (uncurry (curry g) ⊗₁ sᵍ _) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ (eval-curry ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      (eval ∘ σ⇒) ∘ (g ⊗₁ sᵍ _) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐  ∎

    t-open-unitor :
        α⇐ {A} {B} {X ⊗₀ [ X , unit ]₀} ∘ (id ⊗₁ (id ⊗₁ t {X})) ∘ (id ⊗₁ ρ⇐)
      ≈ (id ⊗₁ t {X}) ∘ ρ⇐
    t-open-unitor = begin
      α⇐ ∘ (id ⊗₁ (id ⊗₁ t)) ∘ (id ⊗₁ ρ⇐)       ≈⟨ sym-assoc ⟩
      (α⇐ ∘ (id ⊗₁ (id ⊗₁ t))) ∘ (id ⊗₁ ρ⇐)     ≈⟨ assoc-commute-to ⟩∘⟨refl ⟩
      (((id ⊗₁ id) ⊗₁ t) ∘ α⇐) ∘ (id ⊗₁ ρ⇐)     ≈⟨ assoc ⟩
      ((id ⊗₁ id) ⊗₁ t) ∘ α⇐ ∘ (id ⊗₁ ρ⇐)       ≈⟨ refl⟩∘⟨ assoc-unitorʳ ⟩
      ((id ⊗₁ id) ⊗₁ t) ∘ ρ⇐                     ≈⟨ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      (id ⊗₁ t) ∘ ρ⇐                             ∎

    -- The left leg's core (drop the outer braiding): feeding `t {X}` to `φ⁻¹`'s read reconstructs
    -- `φ⇐′ X X ∘ t {X} = ⌜ τ {X} ⌝` (`φ⇐-t`), and the doubled `eval` becomes internal composition.
    evaluate-t-composite :
        ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ X)) ∘ α⇐ ∘ (id ⊗₁ ((eval {X} {Y} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐))
      ≈ τ {X} {⊥} ∘ internal-∘ {Y} {⊥ ⊗₀ X} {X}
    evaluate-t-composite = begin
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ α⇐ ∘ (id ⊗₁ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ((split₂ˡ ○ (refl⟩∘⟨ split₂ˡ) ○ (refl⟩∘⟨ refl⟩∘⟨ split₂ˡ)))) ⟩
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ α⇐ ∘ (id ⊗₁ (eval ⊗₁ id)) ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ t)) ∘ (id ⊗₁ ρ⇐)
        ≈⟨ refl⟩∘⟨ extendʳ assoc-commute-to ⟩
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ ((id ⊗₁ eval) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ t)) ∘ (id ⊗₁ ρ⇐)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ ((⟺ pentagon-collapse-inv) ⟩∘⟨refl)) ⟩
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ ((id ⊗₁ eval) ⊗₁ id) ∘ ((α⇒ ⊗₁ id) ∘ α⇐ ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ t)) ∘ (id ⊗₁ ρ⇐)
        ≈⟨ assoc ○ (refl⟩∘⟨ ((refl⟩∘⟨ (refl⟩∘⟨ assoc)) ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc ○ (assoc ⟩∘⟨refl) ○ (refl⟩∘⟨ assoc))) ⟩
      (eval ∘ σ⇒) ∘ ((eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _) ∘ ((id ⊗₁ eval) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ α⇐ ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ t)) ∘ (id ⊗₁ ρ⇐)
        ≈⟨ refl⟩∘⟨ (evaluate-internal-∘ ⟩∘⟨refl) ⟩
      (eval ∘ σ⇒) ∘ ((eval ∘ (internal-∘ ⊗₁ id)) ⊗₁ sᵍ _) ∘ α⇐ ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ t)) ∘ (id ⊗₁ ρ⇐)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ t-open-unitor ⟩
      (eval ∘ σ⇒) ∘ (uncurry internal-∘ ⊗₁ sᵍ _) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐
        ≈˘⟨ evaluate-t-natural ⟩
      ((eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐) ∘ internal-∘
        ≈⟨ evaluate-t ⟩∘⟨refl ⟩
      τ ∘ internal-∘ ∎

    hexagon-left :
        (((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ X)) ∘ α⇐) ∘ (id ⊗₁ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐)) ∘ σ⇒
      ≈ τ-composite {X} {Y}
    hexagon-left = begin
      (((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ α⇐) ∘ (id ⊗₁ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐)) ∘ σ⇒
        ≈⟨ sym-assoc ⟩
      ((((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ α⇐) ∘ (id ⊗₁ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐))) ∘ σ⇒
        ≈⟨ (assoc ○ evaluate-t-composite) ⟩∘⟨refl ⟩
      (τ ∘ internal-∘) ∘ σ⇒
        ≈⟨ assoc ⟩
      τ ∘ internal-∘ ∘ σ⇒ ∎

    -- Reading the internally reindexed `t {Y}` through `φ⁻¹` is exactly the enriched
    -- dinaturality equation for `τ`.
    evaluate-φ⇐-hexagon :
      eval ∘ (Ψ′ Y X ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐))
      ≈ τ {X} {⊥} ∘ internal-∘
    evaluate-φ⇐-hexagon = begin
          eval ∘ (Ψ′ _ _ ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐))
            ≈⟨ (refl⟩∘⟨ serialize₁₂) ○ sym-assoc ⟩
          uncurry (Ψ′ _ _) ∘ (id ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐))
            ≈⟨ uncurry-Ψ-off-diagonal ⟩∘⟨refl ⟩
          (((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ α⇐) ∘ (id ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐))
            ≈⟨ assoc ⟩
          ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ α⇐ ∘ (id ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐))
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (split₂ˡ ○ (refl⟩∘⟨ split₂ˡ) ○ (refl⟩∘⟨ refl⟩∘⟨ split₂ˡ)) ⟩
          ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ internal-∘)) ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
            ≈⟨ refl⟩∘⟨ extendʳ assoc-commute-to ⟩
          ((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ ((id ⊗₁ id) ⊗₁ internal-∘) ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
            ≈⟨ (refl⟩∘⟨ (⟺ serialize₁₂)) ⟩∘⟨refl ⟩
          ((eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _)) ∘ ((id ⊗₁ id) ⊗₁ internal-∘) ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
            ≈⟨ sym-assoc ⟩
          (((eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _)) ∘ ((id ⊗₁ id) ⊗₁ internal-∘)) ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
            ≈⟨ (assoc ○ (refl⟩∘⟨ (⟺ ⊗.homomorphism ○ (elimʳ ⊗.identity ⟩⊗⟨ Equiv.refl)))) ⟩∘⟨refl ⟩
          ((eval ∘ σ⇒) ∘ (eval ⊗₁ (sᵍ _ ∘ internal-∘))) ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
            ≈⟨ swap-evaluate ⟩∘⟨refl ⟩
          (uncurry (sᵍ _ ∘ internal-∘)
            ∘ (id ⊗₁ eval) ∘ σ⇒)
            ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
            ≈⟨ assoc ⟩
          uncurry (sᵍ _ ∘ internal-∘)
            ∘ ((id ⊗₁ eval) ∘ σ⇒)
            ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
            ≈⟨ sᵍ-internal-∘ ⟩∘⟨refl ⟩
          (((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
            ∘ (internal-∘ ⊗₁ id))
            ∘ ((id ⊗₁ eval) ∘ σ⇒)
            ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
            ≈⟨ compose-read-closed ⟩∘⟨refl ⟩
          ((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id)
            ∘ (((id ⊗₁ eval) ∘ α⇒) ⊗₁ id)
            ∘ rotate)
            ∘ ((id ⊗₁ eval) ∘ σ⇒)
            ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (t ⊗₁ id)) ∘ (id ⊗₁ λ⇐)
            ≈⟨ route-read ⟩
          (((ρ⇒ ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒))
            ∘ (id ⊗₁
              ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
                ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒))
            ∘ σ⇒)
            ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐
            ≈˘⟨ sᵍ-read ⟩∘⟨refl ⟩
          ((eval ∘ σ⇒) ∘
            (((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
              ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒) ⊗₁ sᵍ _))
            ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐
            ≈⟨ assoc ⟩
          (eval ∘ σ⇒) ∘
            (((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
              ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒) ⊗₁ sᵍ _)
            ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐
            ≈˘⟨ evaluate-t-curry ⟩
          ((eval ∘ σ⇒) ∘ (eval ⊗₁ sᵍ _) ∘ α⇐
            ∘ (id ⊗₁ t) ∘ ρ⇐) ∘ curry
              ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
                ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒)
            ≈⟨ evaluate-t ⟩∘⟨refl ⟩
          τ ∘ curry
            ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
              ∘ (eval ⊗₁ id) ∘ rotate ∘ α⇒)
            ≈⟨ refl⟩∘⟨ curry-resp-≈ evaluation-route-expand ⟩
          τ ∘ curry
            ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
              ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒)
            ≈˘⟨ τ-extra ⟩
          τ ∘ internal-∘ ∎

    -- The right leg's enriched dinaturality, transposed through `φ⁻¹`.
    φ⇐-hexagon :
        φ⇐′ Y X ∘ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐)
      ≈ curry (τ-composite {X} {Y})
    φ⇐-hexagon = uncurry-injective (begin
      uncurry (φ⇐′ _ _ ∘ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐))
        ≈⟨ uncurry-φ⇐ ○ evaluate-swapped ⟩
      eval ∘ (Ψ′ _ _ ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐)) ∘ σ⇒
        ≈⟨ sym-assoc ⟩
      (eval ∘ (Ψ′ _ _ ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐))) ∘ σ⇒
        ≈⟨ evaluate-φ⇐-hexagon ⟩∘⟨refl ⟩
      (τ ∘ internal-∘) ∘ σ⇒                                   ≈⟨ assoc ⟩
      τ ∘ internal-∘ ∘ σ⇒                                     ≈˘⟨ eval-curry ⟩
      uncurry (curry τ-composite)                             ∎)

    hexagon-right :
        (((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ X)) ∘ α⇐) ∘ (id ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐)) ∘ σ⇒
      ≈ τ-composite {X} {Y}
    hexagon-right = begin
      (((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ _)) ∘ α⇐) ∘ (id ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐)) ∘ σ⇒
        ≈˘⟨ evaluate-φ-input ⟩∘⟨refl ⟩
      (eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐)) ∘ σ⇒
        ≈˘⟨ evaluate-Ψ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐) ⟩
      eval ∘ (Ψ′ _ _ ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐)) ∘ σ⇒
        ≈˘⟨ evaluate-swapped ⟩
      (eval ∘ σ⇒) ∘ (((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐) ⊗₁ id) ∘ (id ⊗₁ Ψ′ _ _)
        ≈˘⟨ uncurry-φ⇐ ⟩
      uncurry (φ⇐′ _ _ ∘ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐))
        ≈⟨ uncurry-resp-≈ φ⇐-hexagon ⟩
      uncurry (curry τ-composite)
        ≈⟨ eval-curry ⟩
      τ-composite ∎

    hexagon-under-φ⇐ {X} {Y} = begin
      (eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐)) ∘ σ⇒
        ≈⟨ evaluate-φ-input ⟩∘⟨refl ⟩
      (((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ X)) ∘ α⇐) ∘ (id ⊗₁ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐)) ∘ σ⇒
        ≈⟨ hexagon-left ⟩
      τ-composite
        ≈˘⟨ hexagon-right ⟩
      (((eval ∘ σ⇒) ∘ (eval ⊗₁ id) ∘ (id ⊗₁ sᵍ X)) ∘ α⇐) ∘ (id ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐)) ∘ σ⇒
        ≈˘⟨ evaluate-φ-input ⟩∘⟨refl ⟩
      (eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐)) ∘ σ⇒ ∎


    -- The hexagon, transposed by the iso `φ⁻¹` (mono) into the hom object `[ Y , ⊥ ⊗₀ X ]₀ *`, then
    -- uncurried to `⊥`: it becomes `eval ∘ (Ψ ⊗₁ Lhex) ∘ σ⇒ ≈ eval ∘ (Ψ ⊗₁ Rhex) ∘ σ⇒`, the enriched
    -- dinaturality of `τ̂` fed through the inner map `Ψ` of `φ⁻¹`.
    hexagon-transposed :
        φ⇐′ Y X ∘ (eval {X} {Y} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐
      ≈ φ⇐′ Y X ∘ (id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐
    hexagon-transposed = uncurry-injective (begin
      uncurry (φ⇐′ _ _ ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐)
        ≈⟨ uncurry-φ⇐ ⟩
      (eval ∘ σ⇒) ∘ (((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐) ⊗₁ id) ∘ (id ⊗₁ Ψ′ _ _)
        ≈⟨ evaluate-swapped ⟩
      eval ∘ (Ψ′ _ _ ⊗₁ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐)) ∘ σ⇒
        ≈⟨ evaluate-Ψ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐) ⟩
      (eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐)) ∘ σ⇒
        ≈⟨ hexagon-under-φ⇐ ⟩
      (eval ∘ ((φ-input ∘ eval) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐)) ∘ σ⇒
        ≈˘⟨ evaluate-Ψ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐) ⟩
      eval ∘ (Ψ′ _ _ ⊗₁ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐)) ∘ σ⇒
        ≈˘⟨ evaluate-swapped ⟩
      (eval ∘ σ⇒) ∘ (((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐) ⊗₁ id) ∘ (id ⊗₁ Ψ′ _ _)
        ≈˘⟨ uncurry-φ⇐ ⟩
      uncurry (φ⇐′ _ _ ∘ (id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐)  ∎)

  t-extranatural : Extra-H t
  t-extranatural {X} {Y} = begin
    (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐
      ≈⟨ introˡ (_≅_.isoʳ (φ-≅ {Y} {X})) ⟩
    (φ⇒ Y X ∘ φ⇐′ Y X) ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐
      ≈⟨ assoc ⟩
    φ⇒ Y X ∘ φ⇐′ Y X ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ hexagon-transposed ⟩
    φ⇒ Y X ∘ φ⇐′ Y X ∘ (id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐
      ≈˘⟨ assoc ⟩
    (φ⇒ Y X ∘ φ⇐′ Y X) ∘ (id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐
      ≈⟨ elimˡ (_≅_.isoʳ (φ-≅ {Y} {X})) ⟩
    (id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐              ∎
