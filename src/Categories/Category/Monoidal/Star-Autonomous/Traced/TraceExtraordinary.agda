{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Traced using (Traced)

import Categories.Enriched.Category as Enriched

-- Joyal--Street--Verity's trace axioms imply Hajgató--Hasegawa 2013,
-- Lemma 3.1: the name of traced evaluation is extraordinary.

module Categories.Category.Monoidal.Star-Autonomous.Traced.TraceExtraordinary
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (Cl : Closed M) (T : Traced M) where

open Category 𝒞
open Traced T
open Closed Cl using ([_,_]₀)

open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Closed.Currying Cl
  using (uncurry²-injective; uncurry²-∘)
open import Categories.Category.Monoidal.Closed.SelfEnrichment symmetric Cl
  renaming (evaluate-precomposition to eval-pre-∘)
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Tensor symmetric Cl
open import Categories.Category.Monoidal.Properties M using (coherence₁)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Symmetric.Properties symmetric using (middle-braid)
open import Categories.Category.Monoidal.Traced.Dinaturality T using (parameter-slide)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Bifunctor symmetric
  using ( BifunctorHelper; bifunctorHelper; postcompose-helper
        ; reduce-flipped-helper; module FromHelper )
open import Categories.Enriched.Category.Opposite symmetric renaming (op to opE)
open import Categories.Enriched.Functor M using (Functor)
open import Categories.Enriched.Functor.Opposite symmetric using (op²F)
open import Categories.Enriched.Extraordinary symmetric
  using (Extraordinary; module Actions)
open import Categories.Category.Monoidal.Braided.Properties braided
  using (braiding-coherence) renaming (module Shorthands to BraidShorthands)
open import Categories.Morphism.Reasoning 𝒞
open Shorthands
open BraidShorthands
open SelfEnriched using (homᵒᵖHelper; homˡ₁; homʳ₁) renaming (homʳFunctor to homʳ)

private
  S₀ S₁ : Enriched.Category M o
  S₀ = selfEnrichment
  S₁ = opE selfEnrichment

  variable
    A B C : Obj -- continuation source, parameter, and target roles
    X Y Z : Obj -- feedback and comparison roles

  traceHelper : Obj → BifunctorHelper S₁ S₀ S₀
  traceHelper B = postcompose-helper (homʳ B)
    (reduce-flipped-helper homᵒᵖHelper (B ⊗Fᵒᵖ-) op²F)

-- The enriched functor (X,Y) ↦ [[Y,B⊗X],B] from Lemma 3.1.
traceFunctor : Obj → SelfProfunctor
traceFunctor B = bifunctorHelper (traceHelper B)

-- Trace evaluation over its argument.
τ : [ X , B ⊗₀ X ]₀ ⇒ B
τ = trace eval

-- The closed name of `τ`.
τ̂ : unit ⇒ [ [ X , B ⊗₀ X ]₀ , B ]₀
τ̂ = ⌜ τ ⌝

module Lemma₃₁ {B : Obj} where
  private
    module H = BifunctorHelper (traceHelper B)
    module Δ = FromHelper (traceHelper B)
    module Act = Actions selfEnrichment selfEnrichment (traceFunctor B)
    module B⊗ = Functor (B ⊗F-)

    ev² : ([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ X ⇒ B ⊗₀ X
    ev² = eval ∘ (id ⊗₁ eval) ∘ α⇒

    ev²ˡ : ([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ Y ⇒ B ⊗₀ Y
    ev²ˡ = (id ⊗₁ (eval ∘ σ⇒)) ∘ (α⇒ ∘ (eval ⊗₁ id)) ∘
      (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒)

  private abstract
    eval-pre-⌜⌝ : (q : A ⇒ [ Y , X ]₀) (k : X ⇒ B) →
      uncurry (uncurry (homʳ₁ Y X B ∘ q)) ∘ ((id ⊗₁ ⌜ k ⌝) ⊗₁ id)
      ≈ k ∘ uncurry q ∘ (ρ⇒ ⊗₁ id)
    eval-pre-⌜⌝ q k = begin
      uncurry (uncurry (homʳ₁ _ _ _ ∘ q)) ∘ ((id ⊗₁ ⌜ k ⌝) ⊗₁ id)
        ≈⟨ eval-pre-∘ ⟩
      uncurry ⌜ k ⌝ ∘ (id ⊗₁ uncurry q) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
        ≈⟨ eval-⌜⌝ ⟩∘⟨refl ⟩
      (k ∘ λ⇒) ∘ ((id ⊗₁ uncurry q) ∘ α⇒ ∘ (σ⇒ ⊗₁ id))
        ≈⟨ pullˡ (pullʳ unitorˡ-commute-from) ⟩
      (k ∘ (uncurry q ∘ λ⇒)) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))
        ≈⟨ assoc²βγ ⟩
      (k ∘ uncurry q) ∘ λ⇒ ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
        ≈⟨ pullʳ (refl⟩∘⟨ pullˡ coherence₁) ⟩
      k ∘ uncurry q ∘ (λ⇒ ⊗₁ id) ∘ (σ⇒ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ˡ ⟩
      k ∘ uncurry q ∘ ((λ⇒ ∘ σ⇒) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding-coherence ⟩⊗⟨refl ⟩
      k ∘ uncurry q ∘ (ρ⇒ ⊗₁ id) ∎

    ev²⊗ :
      (eval {B ⊗₀ X} {B ⊗₀ Y} ∘ (id ⊗₁ eval {Y} {B ⊗₀ X}) ∘ α⇒)
        ∘ ((B⊗.₁ ⊗₁ id) ⊗₁ id)
      ≈ ev²ˡ ∘ (σ⇒ ⊗₁ id)
    ev²⊗ = begin
      (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((B⊗.₁ ⊗₁ id) ⊗₁ id)
        ≈⟨ pull-last assoc-commute-from ⟩
      eval ∘ (id ⊗₁ eval) ∘ (B⊗.₁ ⊗₁ (id ⊗₁ id)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
      eval ∘ (id ⊗₁ eval) ∘ (B⊗.₁ ⊗₁ id) ∘ α⇒
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      eval ∘ (B⊗.₁ ⊗₁ (eval ∘ id)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ identityʳ) ⟩∘⟨refl ⟩
      eval ∘ (B⊗.₁ ⊗₁ eval) ∘ α⇒
        ≈⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
      eval ∘ (B⊗.₁ ⊗₁ id) ∘ (id ⊗₁ eval) ∘ α⇒
        ≈⟨ pullˡ ⊗F-eval ⟩
      ((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ eval) ∘ α⇒
        ≈⟨ pullʳ ((switch-tofromʳ σ middle-braid) ⟩∘⟨refl) ⟩
      (id ⊗₁ eval) ∘
        ((((id ⊗₁ σ⇒) ∘ α⇒) ∘ σ⇒) ∘ ((id ⊗₁ eval) ∘ α⇒))
        ≈⟨ refl⟩∘⟨ center σ⇒-comm ⟩
      (id ⊗₁ eval) ∘ ((id ⊗₁ σ⇒) ∘ α⇒) ∘ ((eval ⊗₁ id) ∘ σ⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullʳ (switch-fromtoˡ associator (⟺ hexagon₁)) ⟩
      (id ⊗₁ eval) ∘ ((id ⊗₁ σ⇒) ∘ α⇒) ∘ (eval ⊗₁ id)
        ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (eval ⊗₁ id)
        ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
        ≈⟨ pullˡ merge₂ˡ ⟩
      (id ⊗₁ (eval ∘ σ⇒)) ∘ α⇒ ∘ (eval ⊗₁ id)
        ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      (id ⊗₁ (eval ∘ σ⇒)) ∘ (α⇒ ∘ (eval ⊗₁ id))
        ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
        ≈⟨ reassoc-tail₆ ⟩
      ev²ˡ ∘ (σ⇒ ⊗₁ id) ∎

    Tr-homʳ :
      τ ∘ uncurry (homʳ₁ X Y (B ⊗₀ X)) ∘ (ρ⇒ ⊗₁ id)
      ≈ trace ev² ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
    Tr-homʳ = begin
      trace eval ∘ uncurry (homʳ₁ _ _ _) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ pullˡ (⟺ tightenᵣ) ⟩
      trace (eval ∘ (uncurry (homʳ₁ _ _ _) ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ trace⟨ uncurry²-homʳ ⟩ ⟩∘⟨refl ⟩
      trace (ev² ∘ (σ⇒ ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ pushˡ tightenᵣ ⟩
      trace ev² ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id) ∎

    Tr-homˡ :
      τ {Y} {B} ∘
        uncurry (homˡ₁ Y (B ⊗₀ X) (B ⊗₀ Y) ∘ B⊗.₁) ∘
        (ρ⇒ ⊗₁ id)
      ≈ trace ev²ˡ ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
    Tr-homˡ = begin
      trace eval ∘
        uncurry (homˡ₁ _ _ _ ∘ B⊗.₁) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ uncurry-∘ ⟩∘⟨refl ⟩
      trace eval ∘
        (uncurry (homˡ₁ _ _ _) ∘ (B⊗.₁ ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ (eval-curry ⟩∘⟨refl) ⟩∘⟨refl ⟩
      trace eval ∘ (internal-∘ ∘ (B⊗.₁ ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ assoc ⟩
      trace eval ∘ internal-∘ ∘ (B⊗.₁ ⊗₁ id) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ pullˡ (⟺ tightenᵣ) ⟩
      trace (eval ∘ (internal-∘ ⊗₁ id)) ∘ (B⊗.₁ ⊗₁ id) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ trace⟨ eval-curry ⟩ ⟩∘⟨refl ⟩
      trace (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (B⊗.₁ ⊗₁ id) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ pullˡ (⟺ tightenᵣ) ⟩
      trace ((eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((B⊗.₁ ⊗₁ id) ⊗₁ id))
        ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ trace⟨ ev²⊗ ⟩ ⟩∘⟨refl ⟩
      trace (ev²ˡ ∘ (σ⇒ ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ pushˡ tightenᵣ ⟩
      trace ev²ˡ ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id) ∎

  private abstract
    reduceʳ : Act.F₁ʳ {X = X} {Y} ≈ H.mapʳ X X Y
    reduceʳ = Δ.diagonal-appˡ

    reduceˡ : Act.F₁ˡ {X = X} {Y} ≈ H.mapˡ Y X Y
    reduceˡ = Δ.diagonal-appʳ

    eval-actionʳ : uncurry
      (uncurry (internal-∘ ∘ (H.mapʳ X X Y ⊗₁ ⌜ τ̂ {X = X} ⌝) ∘ ρ⇐))
      ≈ trace ev² ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
    eval-actionʳ {X = X} {Y = Y} = begin
      uncurry (uncurry (internal-∘ ∘ (H.mapʳ X X Y ⊗₁ ⌜ τ̂ ⌝) ∘ ρ⇐))
        ≈⟨ uncurry²-∘-⌜⌝ʳ ⟩
      uncurry (uncurry (H.mapʳ X X Y)) ∘ ((id ⊗₁ τ̂) ⊗₁ id)
        ≈⟨ eval-pre-⌜⌝ (homʳ₁ _ _ _ ∘ id) τ ⟩
      τ ∘ uncurry (homʳ₁ X Y (B ⊗₀ X) ∘ id) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ uncurry-resp-≈ identityʳ ⟩∘⟨refl ⟩
      τ ∘ uncurry (homʳ₁ X Y (B ⊗₀ X)) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ Tr-homʳ ⟩
      trace ev² ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id) ∎

    eval-actionˡ : uncurry
      (uncurry (internal-∘ ∘ (H.mapˡ Y X Y ⊗₁ ⌜ τ̂ {X = Y} ⌝) ∘ ρ⇐))
      ≈ trace ev²ˡ ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
    eval-actionˡ {Y = Y} {X = X} = begin
      uncurry (uncurry (internal-∘ ∘ (H.mapˡ Y X Y ⊗₁ ⌜ τ̂ ⌝) ∘ ρ⇐))
        ≈⟨ uncurry-resp-≈ uncurry-∘-⌜⌝ʳ ⟩
      uncurry (uncurry (H.mapˡ Y X Y) ∘ (id ⊗₁ τ̂))
        ≈⟨ uncurry-∘ ⟩
      uncurry (uncurry (H.mapˡ Y X Y)) ∘ ((id ⊗₁ τ̂) ⊗₁ id)
        ≈⟨ eval-pre-⌜⌝ (homˡ₁ _ _ _ ∘ B⊗.₁) τ ⟩
      τ ∘ uncurry (homˡ₁ Y (B ⊗₀ X) (B ⊗₀ Y) ∘ B⊗.₁) ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ Tr-homˡ ⟩
      trace ev²ˡ ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id) ∎

    τ̂-slide : internal-∘ ∘ (H.mapʳ X X Y ⊗₁ ⌜ τ̂ {X = X} ⌝) ∘ ρ⇐
      ≈ internal-∘ ∘ (H.mapˡ Y X Y ⊗₁ ⌜ τ̂ {X = Y} ⌝) ∘ ρ⇐
    τ̂-slide {X = X} {Y = Y} = uncurry²-injective (begin
      uncurry (uncurry (internal-∘ ∘ (H.mapʳ X X Y ⊗₁ ⌜ τ̂ ⌝) ∘ ρ⇐))
        ≈⟨ eval-actionʳ ⟩
      trace ev² ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
        ≈⟨ parameter-slide ⟩∘⟨refl ⟩
      trace ev²ˡ ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
        ≈˘⟨ eval-actionˡ ⟩
      uncurry (uncurry (internal-∘ ∘ (H.mapˡ Y X Y ⊗₁ ⌜ τ̂ ⌝) ∘ ρ⇐)) ∎)

  -- Hajgató--Hasegawa 2013, Lemma 3.1.
  τ-extraordinary : Extraordinary selfEnrichment selfEnrichment (traceFunctor B) unit
    (λ X → ⌜ τ̂ {X = X} ⌝)
  τ-extraordinary {X = X} {Y = Y} = begin
    internal-∘ ∘ (Act.F₁ʳ ⊗₁ ⌜ τ̂ ⌝) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ (reduceʳ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    internal-∘ ∘ (H.mapʳ X X Y ⊗₁ ⌜ τ̂ ⌝) ∘ ρ⇐
      ≈⟨ τ̂-slide ⟩
    internal-∘ ∘ (H.mapˡ Y X Y ⊗₁ ⌜ τ̂ ⌝) ∘ ρ⇐
      ≈˘⟨ refl⟩∘⟨ (reduceˡ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    internal-∘ ∘ (Act.F₁ˡ ⊗₁ ⌜ τ̂ ⌝) ∘ ρ⇐ ∎

  private
    trace-unit : {f : A ⊗₀ unit ⇒ B ⊗₀ unit} → trace f ≈ ρ⇒ ∘ f ∘ ρ⇐
    trace-unit {f = f} = begin
      trace f                       ≈⟨ trace⟨ ⟺ unit-feedback ⟩ ⟩
      trace ((ρ⇒ ∘ f ∘ ρ⇐) ⊗₁ id)   ≈⟨ vanishing₁ ⟩
      ρ⇒ ∘ f ∘ ρ⇐                   ∎
      where
        unit-feedback : (ρ⇒ ∘ f ∘ ρ⇐) ⊗₁ id ≈ f
        unit-feedback = begin
          (ρ⇒ ∘ f ∘ ρ⇐) ⊗₁ id              ≈⟨ introʳ unitorʳ.isoˡ ⟩
          ((ρ⇒ ∘ f ∘ ρ⇐) ⊗₁ id) ∘ ρ⇐ ∘ ρ⇒ ≈⟨ pullˡ (⟺ unitorʳ-commute-to) ⟩
          (ρ⇐ ∘ ρ⇒ ∘ f ∘ ρ⇐) ∘ ρ⇒         ≈⟨ cancelˡ unitorʳ.isoˡ ⟩∘⟨refl ⟩
          (f ∘ ρ⇐) ∘ ρ⇒                    ≈⟨ cancelʳ unitorʳ.isoˡ ⟩
          f                                ∎

  -- Hajgató--Hasegawa 2013, Lemma 3.1 at the tensor unit.
  τ-unit : τ {unit} {B} ≈ ρ⇒ ∘ unit-hom⇐
  τ-unit = trace-unit

open Lemma₃₁ public using (τ-extraordinary; τ-unit)
