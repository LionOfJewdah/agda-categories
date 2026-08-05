{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.CompactClosed using (CompactClosed)
open import Categories.Category.Monoidal.Traced using (Traced)

-- The construction follows Hajgató--Hasegawa 2013, Lemmas 3.2, 3.3, and 3.5,
-- Corollary 3.4, and Theorem 3.6.

module Categories.Category.Monoidal.Star-Autonomous.Traced
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (Cl : Closed M) (T : Traced M) where

open import Data.Product using (_,_)

import Categories.Category.Construction.Core 𝒞 as Core
import Categories.Enriched.Category as EnrichedCategory
import Categories.Enriched.Extraordinary as Extraordinary
import Categories.Category.Monoidal.Closed.CompactClosed as ClosedCompactClosed
import Categories.Category.Monoidal.Star-Autonomous.Duality as StarDuality
import Categories.Category.Monoidal.Star-Autonomous.Duality.Enriched as EnrichedDuality

open Category 𝒞
open Traced T
open Closed Cl using ([_,_]₀; [_,_]₁; [-,_]; [_,-]; [-,-])

open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Closed.Currying Cl
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment symmetric Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Tensor symmetric Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Currying symmetric Cl
  using (_⊗₁ˡ_; _⊗₁ʳ_; ev⊗ˡ; ev⊗ʳ; tensorˡ-action; tensorʳ-action)
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.Symmetric.Properties symmetric
  using (braiding-selfInverse; cup-swap; middle-braid)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Bifunctor symmetric
  using ( appʳ; op₂F; reduce-⊠; reduce-flipped-helper
        ; module FromHelper; module Helper; module Postcomposition )
open import Categories.Enriched.Category.Opposite symmetric renaming (op to opE)
open import Categories.Enriched.Functor M using (Functor; _∘F_) renaming (id to idF)
open import Categories.Enriched.Functor.Opposite symmetric using (op²F)
open import Categories.Enriched.Functor.TensorProduct.Symmetric symmetric using (swapF)
open import Categories.Enriched.Extraordinary symmetric
  using (Extraordinary; extraordinary-resp-≈; map-extraordinary)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism)
open import Categories.Enriched.NaturalTransformation M using (NaturalTransformation)
open import Categories.Morphism 𝒞 using (_≅_; Iso; IsIso; module ≅)
open import Categories.Morphism.Duality 𝒞 using (≅⇒op-≅)
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.Category.Monoidal.Interchange.Braided braided
  using () renaming (hasInterchange to interchange)
open import Categories.Enriched.Category.TensorProduct interchange using (_⊠_)
open Shorthands
open BraidShorthands
open Core.Shorthands using (_∘ᵢ_)
open SelfEnriched using (homʳ₁)

import Categories.Category.Monoidal.Star-Autonomous.Traced.TraceExtraordinary as TraceExtraordinary

module Base = StarDuality symmetric Cl
module Enriched = EnrichedDuality symmetric Cl
open Base public
  using (swap-curry-≅; δ; δ-name; uncurry-δ; uncurry-δ-at; IsDualizing)

private
  variable
    A B : Obj -- closed arguments
    X Y : Obj -- feedback and comparison roles

module Dualized (⊥ : Obj) (dualizing : IsDualizing ⊥) where
  open TraceExtraordinary using (τ̂; τ; τ-unit; traceFunctor)
  open Base.Dualized ⊥ dualizing public
  module EnrichedDualized = Enriched.Dualized ⊥ dualizing
  open EnrichedDualized using (⌜φ⌝)

  private
    dualᵒ : A ≅ B → (A *) ≅ (B *)
    dualᵒ iso = [ [-, ⊥ ] ]-resp-≅ (≅⇒op-≅ iso)

    homˡ : (D : Obj) → A ≅ B → [ D , A ]₀ ≅ [ D , B ]₀
    homˡ D = [ [ D ,-] ]-resp-≅

    swap-curry-layer-≅ : ((⊥ ⊗₀ X) *) * ≅ ([ X , ⊥ * ]₀ *)
    swap-curry-layer-≅ = dualᵒ swap-curry-≅
    module swap-curry-layer-≅ {X} = _≅_ (swap-curry-layer-≅ {X = X})

    replace-dual-unit-≅ : ([ X , ⊥ * ]₀ *) ≅ ([ X , unit ]₀ *)
    replace-dual-unit-≅ = dualᵒ (homˡ _ ⊥*-≅)
    module replace-dual-unit-≅ {X} = _≅_ (replace-dual-unit-≅ {X = X})

    uncurry-tensor-≅ : [ Y , ([ X , unit ]₀ *) ]₀ ≅ (Y ⊗₀ [ X , unit ]₀) *
    uncurry-tensor-≅ = ≅.sym curry₂-iso

    remove-double-dual-≅ : ((Y ⊗₀ [ X , unit ]₀) *) * ≅ Y ⊗₀ [ X , unit ]₀
    remove-double-dual-≅ = ≅.sym **-≅

    module insert-double-dual-≅ {X} = **-≅ {⊥ ⊗₀ X}

    feedback⁻ : ⊥ ⊗₀ X ≅ ([ X , unit ]₀ *)
    feedback⁻ = replace-dual-unit-≅ ∘ᵢ (swap-curry-layer-≅ ∘ᵢ **-≅)
    module feedback⁻ {X} = _≅_ (feedback⁻ {X = X})

    φᵀ-≅ : [ Y , ⊥ ⊗₀ X ]₀ ≅ (Y ⊗₀ [ X , unit ]₀) *
    φᵀ-≅ = uncurry-tensor-≅ ∘ᵢ homˡ _ feedback⁻
    module φᵀ-≅ {X Y} = _≅_ (φᵀ-≅ {Y = Y} {X = X})

  -- Hajgató--Hasegawa 2013, Lemma 3.2.
  φ-≅ : ([ Y , ⊥ ⊗₀ X ]₀ *) ≅ Y ⊗₀ [ X , unit ]₀
  φ-≅ = remove-double-dual-≅ ∘ᵢ dualᵒ φᵀ-≅
  module φ-≅ {X Y} = _≅_ (φ-≅ {Y = Y} {X = X})

  φ-source : SelfProfunctor
  φ-source = EnrichedDualized.φ-source

  φ-target : SelfProfunctor
  φ-target = reduce-⊠ -⊗F- idF (SelfEnriched.homʳFunctor unit) ∘F swapF

  -- Hajgató--Hasegawa 2013, Lemma 3.2.
  φ-NI : NaturalIsomorphism φ-source φ-target
  φ-NI = EnrichedDualized.φ-NI

  private
    module Extra = Extraordinary.Calculus symmetric selfEnrichment selfEnrichment
    module TargetExtra = Extra.Definition φ-target unit
    module TargetAction = Extra.Actions φ-target
    module Φ⇒ = NaturalTransformation (NaturalIsomorphism.from φ-NI)
    module Target = Functor φ-target
    module UnitHom = Functor (Representable.functor (opE selfEnrichment) {X = unit})
    module Self = EnrichedCategory.Category selfEnrichment
    module Selfᵒ = EnrichedCategory.Category (opE selfEnrichment)

    module K = FromHelper
      (reduce-flipped-helper SelfEnriched.homᵒᵖHelper (⊥ ⊗Fᵒᵖ-) op²F)
    module Post = Postcomposition
      {H = reduce-flipped-helper SelfEnriched.homᵒᵖHelper (⊥ ⊗Fᵒᵖ-) op²F}
    module Homᵒ = Helper SelfEnriched.homᵒᵖHelper

    abstract
      trace-action : Functor.₁ (traceFunctor Cl T ⊥) {X = A , X} {Y = B , Y}
        ≈ Functor.₁ φ-source
      trace-action = begin
        Functor.₁ (traceFunctor Cl T ⊥)
          ≈⟨ Post.diagonal (SelfEnriched.homʳFunctor ⊥) ⟩
        Functor.₁ (SelfEnriched.homʳFunctor ⊥) ∘ K.diagonal
          ≈⟨ refl⟩∘⟨ Homᵒ.reduce-flipped-diagonal (⊥ ⊗Fᵒᵖ-) op²F ⟩
        Functor.₁ φ-source ∎

    φ⇒ : NaturalTransformation (traceFunctor Cl T ⊥) φ-target
    φ⇒ = record
      { comp = Φ⇒.comp
      ; commute = (refl⟩∘⟨ (refl⟩⊗⟨ trace-action) ⟩∘⟨refl) ○ Φ⇒.commute
      }
    module φ⇒ = NaturalTransformation φ⇒

    target-tailʳ : (⊗-map₁ ∘ ((id ⊗₁ UnitHom.₁ {X = X} {Y = X}) ∘ σ⇒)) ∘
                      ((Selfᵒ.id {A = X} ⊗₁ id) ∘ λ⇐)
                    ≈ (X ⊗₁ˡ Y) [ X , unit ]₀
    target-tailʳ {X} {Y} = begin
      (⊗-map₁ ∘ ((id ⊗₁ UnitHom.₁) ∘ σ⇒)) ∘ ((Selfᵒ.id ⊗₁ id) ∘ λ⇐)
        ≈⟨ assoc²βε ⟩
      ⊗-map₁ ∘ (id ⊗₁ UnitHom.₁) ∘ σ⇒ ∘ (Selfᵒ.id ⊗₁ id) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ σ⇒-comm ⟩
      ⊗-map₁ ∘ (id ⊗₁ UnitHom.₁) ∘ (id ⊗₁ Selfᵒ.id) ∘ σ⇒ ∘ λ⇐
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      ⊗-map₁ ∘ (id ⊗₁ (UnitHom.₁ ∘ Selfᵒ.id)) ∘ σ⇒ ∘ λ⇐
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ UnitHom.identity ⟩∘⟨refl) ⟩
      ⊗-map₁ ∘ (id ⊗₁ ⌜id⌝) ∘ σ⇒ ∘ λ⇐
        ≈⟨ refl⟩∘⟨ extendʳ (⟺ σ⇒-comm) ⟩
      ⊗-map₁ ∘ σ⇒ ∘ (⌜id⌝ ⊗₁ id) ∘ λ⇐
        ≈⟨ tensorˡ-action X Y [ X , unit ]₀ ⟩
      (X ⊗₁ˡ Y) [ X , unit ]₀ ∎

    target-actionʳ : TargetAction.F₁ʳ {X = X} {Y} ≈ (X ⊗₁ˡ Y) [ X , unit ]₀
    target-actionʳ = (assoc ⟩∘⟨refl) ○ target-tailʳ

    target-actionʳ-eval : uncurry (TargetAction.F₁ʳ {X = X} {Y})
                          ≈ ev⊗ˡ X Y [ X , unit ]₀
    target-actionʳ-eval {X = X} {Y = Y} = begin
      uncurry TargetAction.F₁ʳ            ≈⟨ uncurry-resp-≈ target-actionʳ ⟩
      uncurry ((X ⊗₁ˡ Y) [ X , unit ]₀)   ≈⟨ eval-curry ⟩
      ev⊗ˡ X Y [ X , unit ]₀ ∎

    merge-tensor-unit : (f : A ⇒ B) → (id ⊗₁ f) ∘ (Self.id {A = Y} ⊗₁ id) ≈ Self.id ⊗₁ f
    merge-tensor-unit f = merge₂ˡ ○ (refl⟩⊗⟨ identityʳ)

    tensor-map-precompose : ⊗-map₁ {Y} {Y} {[ Y , unit ]₀} {[ X , unit ]₀} ∘
                              (Self.id ⊗₁ homʳ₁ X Y unit) ∘ λ⇐
                            ≈ ((Y ⊗₁ʳ [ Y , unit ]₀) [ X , unit ]₀) ∘ homʳ₁ X Y unit
    tensor-map-precompose {Y = Y} {X = X} = begin
      ⊗-map₁ ∘ (Self.id ⊗₁ homʳ₁ X Y unit) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
      ⊗-map₁ ∘ (Self.id ⊗₁ id) ∘ (id ⊗₁ homʳ₁ X Y unit) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ unitorˡ-commute-to ⟩
      ⊗-map₁ ∘ (Self.id ⊗₁ id) ∘ λ⇐ ∘ homʳ₁ X Y unit
        ≈⟨ assoc²εβ ⟩
      (⊗-map₁ ∘ (Self.id ⊗₁ id) ∘ λ⇐) ∘ homʳ₁ X Y unit
        ≈⟨ tensorʳ-action Y [ Y , unit ]₀ [ X , unit ]₀ ⟩∘⟨refl ⟩
      ((Y ⊗₁ʳ [ Y , unit ]₀) [ X , unit ]₀) ∘ homʳ₁ X Y unit ∎

    target-actionˡ : TargetAction.F₁ˡ {X = X} {Y}
      ≈ ((Y ⊗₁ʳ [ Y , unit ]₀) [ X , unit ]₀) ∘ homʳ₁ X Y unit
    target-actionˡ {X} {Y} = begin
      TargetAction.F₁ˡ
        ≈⟨ assoc ⟩∘⟨refl ⟩
      (⊗-map₁ ∘ ((id ⊗₁ homʳ₁ X Y unit) ∘ σ⇒)) ∘ ((id ⊗₁ Self.id) ∘ ρ⇐)
        ≈⟨ assoc²βε ⟩
      ⊗-map₁ ∘ (id ⊗₁ homʳ₁ X Y unit) ∘ σ⇒ ∘ (id ⊗₁ Self.id) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ σ⇒-comm ⟩
      ⊗-map₁ ∘ (id ⊗₁ homʳ₁ X Y unit) ∘ (Self.id ⊗₁ id) ∘ σ⇒ ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ pullˡ (merge-tensor-unit (homʳ₁ X Y unit)) ⟩
      ⊗-map₁ ∘ (Self.id ⊗₁ homʳ₁ X Y unit) ∘ σ⇒ ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding-coherence-σ ⟩∘⟨refl ⟩
      ⊗-map₁ ∘ (Self.id ⊗₁ homʳ₁ X Y unit) ∘ (λ⇐ ∘ ρ⇒) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelʳ unitorʳ.isoʳ ⟩
      ⊗-map₁ ∘ (Self.id ⊗₁ homʳ₁ X Y unit) ∘ λ⇐
        ≈⟨ tensor-map-precompose ⟩
      ((Y ⊗₁ʳ [ Y , unit ]₀) [ X , unit ]₀) ∘ homʳ₁ X Y unit ∎

    target-actionˡ-eval : uncurry (TargetAction.F₁ˡ {X = X} {Y})
      ≈ ev⊗ʳ Y (Self.hom Y unit) (Self.hom X unit) ∘ (homʳ₁ X Y unit ⊗₁ id)
    target-actionˡ-eval {X = X} {Y = Y} = begin
      uncurry TargetAction.F₁ˡ
        ≈⟨ uncurry-resp-≈ target-actionˡ ⟩
      uncurry (((Y ⊗₁ʳ [ Y , unit ]₀) [ X , unit ]₀) ∘ homʳ₁ X Y unit)
        ≈⟨ uncurry-∘ ⟩
      uncurry ((Y ⊗₁ʳ [ Y , unit ]₀) [ X , unit ]₀) ∘ (homʳ₁ X Y unit ⊗₁ id)
        ≈⟨ eval-curry ⟩∘⟨refl ⟩
      ev⊗ʳ Y (Self.hom Y unit) (Self.hom X unit) ∘ (homʳ₁ X Y unit ⊗₁ id) ∎

    tᵉ : unit ⇒ [ unit , X ⊗₀ [ X , unit ]₀ ]₀
    tᵉ {X} = internal-∘ ∘ (φ⇒.comp (X , X) ⊗₁ ⌜ τ̂ Cl T {B = ⊥} ⌝) ∘ λ⇐

  -- Hajgató--Hasegawa 2013, Corollary 3.4.
  t : unit ⇒ X ⊗₀ [ X , unit ]₀
  t = ⌞ tᵉ ⌟ᶜ

  abstract
    t-extraordinary : Extraordinary selfEnrichment selfEnrichment φ-target unit
      (λ X → ⌜ t {X} ⌝)
    t-extraordinary =
      extraordinary-resp-≈ selfEnrichment selfEnrichment φ-target unit (λ X → ⟺ ⌜⌞⌟⌝ᶜ)
        (map-extraordinary selfEnrichment selfEnrichment
          φ⇒ (TraceExtraordinary.τ-extraordinary Cl T))

  -- The extraordinary equation in the cap/cup form used by Proposition 2.1.
  Extra-H : (∀ {X} → unit ⇒ X ⊗₀ [ X , unit ]₀) → Set _
  Extra-H s = ∀ {X Y} →
      (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ s {X}) ∘ ρ⇐
    ≈ (id ⊗₁ internal-∘) ∘ α⇒ ∘ (s {Y} ⊗₁ id) ∘ λ⇐

  private abstract
    extraordinaryʳ : (s : unit ⇒ X ⊗₀ [ X , unit ]₀) →
      uncurry (internal-∘ ∘ (TargetAction.F₁ʳ {X = X} {Y} ⊗₁ ⌜ s ⌝) ∘ ρ⇐) ∘ ρ⇐
      ≈ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ s) ∘ ρ⇐
    extraordinaryʳ s = pushˡ uncurry-∘-⌜⌝ʳ ○ pushˡ target-actionʳ-eval

    ∘-eval : ev⊗ʳ Y (Self.hom Y unit) (Self.hom X unit) ∘ (homʳ₁ X Y unit ⊗₁ id)
      ≈ (id ⊗₁ internal-∘) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐
    ∘-eval {X = X} = begin
      ev⊗ʳ _ (Self.hom _ unit) (Self.hom X unit) ∘ (homʳ₁ X _ unit ⊗₁ id)
        ≈˘⟨ reassoc-tail₅ ⟩
      (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∘ (homʳ₁ X _ unit ⊗₁ id)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ α⇐-⊗id-commute ⟩
      (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ ((homʳ₁ X _ unit ⊗₁ id) ⊗₁ id) ∘ α⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (parallel σ⇒-comm id-comm-sym) ⟩
      (id ⊗₁ eval) ∘ α⇒ ∘ ((id ⊗₁ homʳ₁ X _ unit) ⊗₁ id) ∘ (σ⇒ ⊗₁ id) ∘ α⇐
        ≈⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
      (id ⊗₁ eval) ∘ (id ⊗₁ (homʳ₁ X _ unit ⊗₁ id)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐
        ≈⟨ pullˡ merge₂ˡ ⟩
      (id ⊗₁ (eval ∘ (homʳ₁ X _ unit ⊗₁ id))) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐
        ≈⟨ refl⟩⊗⟨ eval-curry ⟩∘⟨refl ⟩
      (id ⊗₁ (internal-∘ ∘ σ⇒)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐
        ≈⟨ pushˡ split₂ʳ ⟩
      (id ⊗₁ internal-∘) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∎

    uncross-middle : (id ⊗₁ σ⇒ {[ X , Y ]₀} {[ Y , unit ]₀}) ∘ α⇒ ∘
                        (σ⇒ {[ X , Y ]₀} {Y} ⊗₁ id) ∘ α⇐ ∘ σ⇐ {[ X , Y ]₀} {Y ⊗₀ [ Y , unit ]₀}
                     ≈ α⇒
    uncross-middle = begin
      (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∘ σ⇐      ≈⟨ refl⟩∘⟨ assoc²εβ ⟩
      (id ⊗₁ σ⇒) ∘ ((α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ σ⇐)  ≈⟨ refl⟩∘⟨ middle-braid ⟩
      (id ⊗₁ σ⇒) ∘ (id ⊗₁ σ⇒) ∘ α⇒                ≈⟨ cancelˡ (⊗-cancel identity² commutative) ⟩
      α⇒                                          ∎

    rotate-parameter : (s : unit ⇒ Y ⊗₀ [ Y , unit ]₀) →
      (id {Y} ⊗₁ σ⇒ {[ X , Y ]₀} {[ Y , unit ]₀}) ∘ α⇒ ∘
        (σ⇒ {[ X , Y ]₀} {Y} ⊗₁ id) ∘ α⇐ ∘
        (id {[ X , Y ]₀} ⊗₁ s) ∘ ρ⇐
      ≈ α⇒ ∘ (s ⊗₁ id {[ X , Y ]₀}) ∘ λ⇐
    rotate-parameter s = begin
      (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ s) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cup-swap ⟩
      (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∘ σ⇐ ∘ (s ⊗₁ id) ∘ λ⇐
        ≈⟨ reassoc-tail₆ ⟩
      ((id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∘ σ⇐) ∘ (s ⊗₁ id) ∘ λ⇐
        ≈⟨ uncross-middle ⟩∘⟨refl ⟩
      α⇒ ∘ (s ⊗₁ id) ∘ λ⇐ ∎

    extraordinaryˡ : (s : unit ⇒ Y ⊗₀ [ Y , unit ]₀) →
      uncurry (internal-∘ ∘ (TargetAction.F₁ˡ {X = X} {Y} ⊗₁ ⌜ s ⌝) ∘ ρ⇐) ∘ ρ⇐
      ≈ (id ⊗₁ internal-∘) ∘ α⇒ ∘ (s ⊗₁ id) ∘ λ⇐
    extraordinaryˡ s = begin
      uncurry (internal-∘ ∘ (TargetAction.F₁ˡ ⊗₁ ⌜ s ⌝) ∘ ρ⇐) ∘ ρ⇐
        ≈⟨ pushˡ uncurry-∘-⌜⌝ʳ ⟩
      uncurry TargetAction.F₁ˡ ∘ ((id ⊗₁ s) ∘ ρ⇐)
        ≈⟨ target-actionˡ-eval ⟩∘⟨refl ⟩
      (ev⊗ʳ _ (Self.hom _ unit) (Self.hom _ unit) ∘ (homʳ₁ _ _ unit ⊗₁ id)) ∘
        ((id ⊗₁ s) ∘ ρ⇐)
        ≈⟨ ∘-eval ⟩∘⟨refl ⟩
      ((id ⊗₁ internal-∘) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘
        ((id ⊗₁ s) ∘ ρ⇐)
        ≈˘⟨ reassoc-tail₆ ⟩
      (id ⊗₁ internal-∘) ∘
        ((id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ s) ∘ ρ⇐)
        ≈⟨ refl⟩∘⟨ rotate-parameter s ⟩
      (id ⊗₁ internal-∘) ∘ α⇒ ∘ (s ⊗₁ id) ∘ λ⇐ ∎

    extraordinary-actions :
      uncurry (internal-∘ ∘ (TargetAction.F₁ʳ {X = X} {Y} ⊗₁ ⌜ t ⌝) ∘ ρ⇐) ∘ ρ⇐
      ≈ uncurry (internal-∘ ∘ (TargetAction.F₁ˡ {X = X} {Y} ⊗₁ ⌜ t ⌝) ∘ ρ⇐) ∘ ρ⇐
    extraordinary-actions {X = X} {Y = Y} =
      uncurry-resp-≈ (TargetExtra.extraordinary-equation t-extraordinary) ⟩∘⟨refl

  abstract
    t-extranatural : Extra-H t
    t-extranatural {X} {Y} = begin
      (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐
        ≈˘⟨ extraordinaryʳ t ⟩
      uncurry (internal-∘ ∘ (TargetAction.F₁ʳ ⊗₁ ⌜ t ⌝) ∘ ρ⇐) ∘ ρ⇐
        ≈⟨ extraordinary-actions ⟩
      uncurry (internal-∘ ∘ (TargetAction.F₁ˡ ⊗₁ ⌜ t ⌝) ∘ ρ⇐) ∘ ρ⇐
        ≈⟨ extraordinaryˡ t ⟩
      (id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐ ∎

  private
    unit-coeval : unit ⇒ unit ⊗₀ [ unit , unit ]₀
    unit-coeval = (id ⊗₁ ⌜id⌝) ∘ ρ⇐

    module unit-swap-curry = _≅_ (swap-curry-≅ {A = ⊥} {B = unit} {C = ⊥})

    unit-dual : [ unit , unit ]₀ ⇒ [ ⊥ ⊗₀ unit , ⊥ ]₀
    unit-dual = unit-swap-curry.to ∘ [ id , ⊥*-≅.to ]₁

  private abstract
    feedback⁻-from : feedback⁻.from ≈ [ unit-dual , id ]₁ ∘ δ ⊥
    feedback⁻-from = pullˡ hom-∘ᵣ

    dualizing-unit-eval : ρ⇒ {⊥} ∘ σ⇒ ≈ (eval {unit} {⊥} ∘ σ⇒) ∘ (id ⊗₁ unit-hom⇒)
    dualizing-unit-eval = begin
      ρ⇒ ∘ σ⇒                          ≈⟨ pushˡ (⟺ eval-unit-hom⇒) ⟩
      eval ∘ (unit-hom⇒ ⊗₁ id) ∘ σ⇒    ≈⟨ pushʳ (⟺ σ⇒-comm) ⟩
      (eval ∘ σ⇒) ∘ (id ⊗₁ unit-hom⇒)  ∎

    ⌜dualizing-unit⌝ : ⊥*-≅.to ≈ curry (ρ⇒ {⊥} ∘ σ⇒)
    ⌜dualizing-unit⌝ = begin
      [ unit-hom⇒ , id ]₁ ∘ δ ⊥                 ≈⟨ hom-curryᵣ ⟩
      curry ((eval ∘ σ⇒) ∘ (id ⊗₁ unit-hom⇒))   ≈˘⟨ curry-resp-≈ dualizing-unit-eval ⟩
      curry (ρ⇒ ∘ σ⇒)                           ∎

    ⌜unit-swap⌝ : [ σ⇐ {⊥} {unit} , id {⊥} ]₁ ∘ ⌜ ρ⇒ {⊥} ⌝ ≈ ⌜ ρ⇒ ∘ σ⇒ ⌝
    ⌜unit-swap⌝ = ⌜hom⌝ʳ ○ ⌜⌝-resp-≈ (refl⟩∘⟨ braiding-selfInverse)

    ⌜swap-curry⌝ : unit-swap-curry.from ∘ ⌜ ρ⇒ {⊥} ⌝ ≈ ⌜ ⊥*-≅.to ⌝
    ⌜swap-curry⌝ = begin
      unit-swap-curry.from ∘ ⌜ ρ⇒ ⌝   ≈⟨ pullʳ ⌜unit-swap⌝ ⟩
      curry₂ ∘ ⌜ ρ⇒ ∘ σ⇒ ⌝            ≈⟨ curry₂-⌜⌝ ⟩
      ⌜ curry (ρ⇒ ∘ σ⇒) ⌝             ≈˘⟨ ⌜⌝-resp-≈ ⌜dualizing-unit⌝ ⟩
      ⌜ ⊥*-≅.to ⌝                     ∎

    ⌜dualizing-unit-map⌝ : [ id {unit} , ⊥*-≅.to ]₁ ∘ ⌜id⌝ ≈ ⌜ ⊥*-≅.to ⌝
    ⌜dualizing-unit-map⌝ = ⌜hom⌝ˡ ○ ⌜⌝-resp-≈ identityʳ

    ⌜unit-dual⌝ : unit-dual ∘ ⌜id⌝ ≈ ⌜ ρ⇒ {⊥} ⌝
    ⌜unit-dual⌝ = begin
      unit-dual ∘ ⌜id⌝                                    ≈⟨ pullʳ ⌜dualizing-unit-map⌝ ⟩
      unit-swap-curry.to ∘ ⌜ ⊥*-≅.to ⌝                    ≈˘⟨ refl⟩∘⟨ ⌜swap-curry⌝ ⟩
      unit-swap-curry.to ∘ unit-swap-curry.from ∘ ⌜ ρ⇒ ⌝  ≈⟨ cancelˡ unit-swap-curry.isoˡ ⟩
      ⌜ ρ⇒ ⌝                                              ∎

    feedback⁻-unit : [ unit-dual , id ]₁ ∘ δ ⊥ ∘ feedback⁻.to
                      ∘ [ λ⇐ , id ]₁ ≈ [ λ⇐ , id ]₁
    feedback⁻-unit = begin
      [ unit-dual , id ]₁ ∘ δ ⊥ ∘ feedback⁻.to ∘ [ λ⇐ , id ]₁   ≈⟨ pullˡ (⟺ feedback⁻-from) ⟩
      feedback⁻.from ∘ feedback⁻.to ∘ [ λ⇐ , id ]₁              ≈⟨ cancelˡ feedback⁻.isoʳ ⟩
      [ λ⇐ , id ]₁                                              ∎

    ⌜id⌝-coeval : λ⇐ ∘ ⌜id⌝ ≈ unit-coeval
    ⌜id⌝-coeval = begin
      λ⇐ ∘ ⌜id⌝           ≈⟨ unitorˡ-commute-to ⟩
      (id ⊗₁ ⌜id⌝) ∘ λ⇐   ≈⟨ refl⟩∘⟨ coherence-inv₃ ⟩
      unit-coeval         ∎

    feedback⁻-eval : ρ⇒ ∘ feedback⁻.to ∘ [ λ⇐ , id ]₁
                      ≈ eval ∘ (id ⊗₁ unit-coeval) ∘ ρ⇐
    feedback⁻-eval = begin
      ρ⇒ ∘ feedback⁻.to ∘ [ λ⇐ , id ]₁
        ≈˘⟨ eval-⌜⌝-unit ⟩
      (eval ∘ (⌜ ρ⇒ ⌝ ⊗₁ (feedback⁻.to ∘ [ λ⇐ , id ]₁))) ∘ λ⇐
        ≈˘⟨ (refl⟩∘⟨ ⌜unit-dual⌝ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      (eval ∘ ((unit-dual ∘ ⌜id⌝) ⊗₁ (feedback⁻.to ∘ [ λ⇐ , id ]₁))) ∘ λ⇐
        ≈˘⟨ uncurry-δ-at ⟩
      uncurry ([ unit-dual , id ]₁ ∘ δ ⊥ ∘ feedback⁻.to ∘ [ λ⇐ , id ]₁)
        ∘ (id ⊗₁ ⌜id⌝) ∘ ρ⇐
        ≈⟨ uncurry-resp-≈ feedback⁻-unit ⟩∘⟨refl ⟩
      uncurry [ λ⇐ , id ]₁ ∘ (id ⊗₁ ⌜id⌝) ∘ ρ⇐
        ≈⟨ eval-comm-dom ⟩∘⟨refl ⟩
      (eval ∘ (id ⊗₁ λ⇐)) ∘ (id ⊗₁ ⌜id⌝) ∘ ρ⇐
        ≈⟨ center merge₂ˡ ⟩
      eval ∘ (id ⊗₁ (λ⇐ ∘ ⌜id⌝)) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ ⌜id⌝-coeval ⟩∘⟨refl ⟩
      eval ∘ (id ⊗₁ unit-coeval) ∘ ρ⇐ ∎

    τ-unit-transpose : τ Cl T {unit} {⊥} ∘ φᵀ-≅.to
                        ≈ ρ⇒ ∘ feedback⁻.to ∘ [ λ⇐ , id ]₁
    τ-unit-transpose = begin
      τ Cl T ∘ φᵀ-≅.to                                      ≈⟨ τ-unit Cl T ⟩∘⟨refl ⟩
      (ρ⇒ ∘ unit-hom⇐) ∘ ([ id , feedback⁻.to ]₁ ∘ curry₂)  ≈⟨ assoc²γδ ⟩
      ρ⇒ ∘ ((unit-hom⇐ ∘ [ id , feedback⁻.to ]₁) ∘ curry₂)  ≈⟨ refl⟩∘⟨ unit-hom⇐-natural ⟩∘⟨refl ⟩
      ρ⇒ ∘ ((feedback⁻.to ∘ unit-hom⇐) ∘ curry₂)            ≈⟨ refl⟩∘⟨ pullʳ unit-hom⇐-curry₂ ⟩
      ρ⇒ ∘ feedback⁻.to ∘ [ λ⇐ , id ]₁                      ∎

  private abstract
    canonical-t-unit : φ-≅.from ∘ τ̂ Cl T {X = unit} {B = ⊥} ≈ unit-coeval
    canonical-t-unit = begin
      φ-≅.from ∘ τ̂ Cl T                               ≈⟨ pullʳ ⌜hom⌝ʳ ⟩
      **-≅.to ∘ ⌜ τ Cl T ∘ φᵀ-≅.to ⌝                  ≈⟨ refl⟩∘⟨ ⌜⌝-resp-≈ τ-unit-transpose ⟩
      **-≅.to ∘ ⌜ ρ⇒ ∘ feedback⁻.to ∘ [ λ⇐ , id ]₁ ⌝  ≈⟨ refl⟩∘⟨ ⌜⌝-resp-≈ feedback⁻-eval ⟩
      **-≅.to ∘ ⌜ eval ∘ (id ⊗₁ unit-coeval) ∘ ρ⇐ ⌝   ≈˘⟨ refl⟩∘⟨ δ-name ⟩
      **-≅.to ∘ δ ⊥ ∘ unit-coeval                     ≈⟨ cancelˡ **-≅.isoˡ ⟩
      unit-coeval                                     ∎

    tᵉ-unit : tᵉ {unit} ≈ ⌜ φ-≅.from ∘ τ̂ Cl T {X = unit} {B = ⊥} ⌝
    tᵉ-unit = begin
      tᵉ  ≈⟨ refl⟩∘⟨ (⌜φ⌝ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      internal-∘ ∘ (⌜ φ-≅.from ⌝ ⊗₁ ⌜ τ̂ Cl T ⌝) ∘ λ⇐  ≈⟨ ⌜∘⌝ ⟩
      ⌜ φ-≅.from ∘ τ̂ Cl T ⌝ ∎

  -- Hajgató--Hasegawa 2013, Lemma 3.5.
  abstract
    t-unit : t {unit} ≈ unit-coeval
    t-unit = begin
      t                           ≈⟨ uncurry-resp-≈ tᵉ-unit ⟩∘⟨refl ⟩
      ⌞ ⌜ φ-≅.from ∘ τ̂ Cl T ⌝ ⌟ᶜ  ≈⟨ ⌞⌜⌝⌟ᶜ ⟩
      φ-≅.from ∘ τ̂ Cl T           ≈⟨ canonical-t-unit ⟩
      unit-coeval                 ∎

  -- Hajgató--Hasegawa 2013, Theorem 3.6.
  compactClosed : CompactClosed M
  compactClosed = ClosedCompactClosed.compactClosed Cl t t-extranatural t-unit symmetric
