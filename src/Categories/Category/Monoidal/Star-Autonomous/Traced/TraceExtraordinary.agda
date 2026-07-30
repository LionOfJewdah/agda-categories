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

open import Data.Product using (_,_)

open Category 𝒞
open Traced T
open Closed Cl using ([_,_]₀)

open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Closed.Currying Cl using (uncurry²-injective; uncurry²-∘)
open import Categories.Category.Monoidal.Closed.SelfEnrichment symmetric Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Tensor symmetric Cl
open import Categories.Category.Monoidal.Properties M using (coherence₁)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Symmetric.Properties symmetric using (middle-braid)
open import Categories.Category.Monoidal.Traced.Dinaturality T using (parameter-slide)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Bifunctor symmetric
  using ( BifunctorHelper; bifunctorHelper; postcompose-helper; reduce-flipped-helper
        ; module FromHelper; module Helper )
open import Categories.Enriched.Category.Opposite symmetric renaming (op to opE)
open import Categories.Enriched.Functor M using (Functor; _∘F_)
open import Categories.Enriched.Functor.Opposite symmetric using (op²F)
open import Categories.Enriched.Functor.TensorProduct.Symmetric symmetric using (swapF)
open import Categories.Enriched.Extraordinary symmetric using (module Actions)
open import Categories.Category.Monoidal.Braided.Properties braided
  using (braiding-coherence) renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Interchange.Braided braided
  using () renaming (hasInterchange to interchange)
open import Categories.Enriched.Functor.TensorProduct interchange using (_⊠F_)
open import Categories.Morphism.Reasoning 𝒞
open Shorthands
open BraidShorthands

private
  S₀ S₁ : Enriched.Category M o
  S₀ = selfEnrichment
  S₁ = opE selfEnrichment

  module S₀ = Enriched.Category S₀
  module S₁ = Enriched.Category S₁

  variable
    A B C : Obj -- continuation source, parameter, and target roles
    X Y Z : Obj -- feedback and comparison roles

  outputF : Obj → Functor S₁ S₀
  outputF B = SelfEnriched.homʳFunctor B

  module Continuation (B : Obj) where
    module Tensor = Functor (B ⊗Fᵒᵖ-)

    helper : BifunctorHelper S₁ S₀ S₁
    helper = reduce-flipped-helper SelfEnriched.homᵒᵖHelper (B ⊗Fᵒᵖ-) op²F

  traceHelper : Obj → BifunctorHelper S₁ S₀ S₀
  traceHelper B = postcompose-helper (outputF B) (Continuation.helper B)

  module Action (B : Obj) = BifunctorHelper (traceHelper B)
  module Tensor (B : Obj) = Functor (B ⊗F-)

-- The canonical action on the continuation object `[Y,B⊗X]`.
continuation₁ :
  [ Z , X ]₀ ⊗₀ [ Y , C ]₀ ⇒ [ [ C , B ⊗₀ Z ]₀ , [ Y , B ⊗₀ X ]₀ ]₀
continuation₁ {B = B} = FromHelper.diagonal (Continuation.helper B)

-- The enriched functor (X,Y) ↦ [[Y,B⊗X],B] from Lemma 3.1.
traceFunctor : Obj → SelfProfunctor
traceFunctor B = outputF B ∘F SelfEnriched.homᵒᵖFunctor
  ∘F (op²F ⊠F (B ⊗Fᵒᵖ-)) ∘F swapF

private
  module TraceF (B : Obj) = Functor (traceFunctor B)
  module OutputF (B : Obj) = Functor (outputF B)

  traceFunctor₁ : (B X Y Z C : Obj) → TraceF.₁ B {X = X , Y} {Y = Z , C}
                  ≈ OutputF.₁ B ∘ continuation₁ {Z = Z} {X} {Y} {C} {B}
  traceFunctor₁ B X Y Z C =
    refl⟩∘⟨ ⟺ (Helper.reduce-flipped-diagonal SelfEnriched.homᵒᵖHelper (B ⊗Fᵒᵖ-) op²F)

private
  module TraceAction (B : Obj) =
    Actions selfEnrichment selfEnrichment (traceFunctor B)

-- Trace evaluation over its argument.
τ : [ X , B ⊗₀ X ]₀ ⇒ B
τ = trace eval

-- The closed name of `τ`.
τ̂ : unit ⇒ [ [ X , B ⊗₀ X ]₀ , B ]₀
τ̂ = ⌜ τ ⌝

private
  τ̂ᵉ : (B X : Obj) → unit ⇒ [ unit , [ [ X , B ⊗₀ X ]₀ , B ]₀ ]₀
  τ̂ᵉ B X = ⌜ τ̂ ⌝

  parameter-evaluation : ([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ X ⇒ B ⊗₀ X
  parameter-evaluation = eval ∘ (id ⊗₁ eval) ∘ α⇒

  parameter-evaluationˡ : ([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ Y ⇒ B ⊗₀ Y
  parameter-evaluationˡ =
    (id ⊗₁ (eval ∘ σ⇒)) ∘ (α⇒ ∘ (eval ⊗₁ id)) ∘ (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒)

private abstract
  eval-⌜pre∘⌝ : (q : A ⇒ [ Y , X ]₀) (k : X ⇒ B) →
    uncurry (uncurry (SelfEnriched.homʳ₁ Y X B ∘ q)) ∘ ((id ⊗₁ ⌜ k ⌝) ⊗₁ id)
    ≈ k ∘ uncurry q ∘ (ρ⇒ ⊗₁ id)
  eval-⌜pre∘⌝ q k = begin
    uncurry (uncurry (SelfEnriched.homʳ₁ _ _ _ ∘ q)) ∘ ((id ⊗₁ ⌜ k ⌝) ⊗₁ id)
      ≈⟨ evaluate-precomposition ⟩
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

  tensor-parameter-evaluation :
    (eval {B ⊗₀ X} {B ⊗₀ Y} ∘ (id ⊗₁ eval {Y} {B ⊗₀ X}) ∘ α⇒)
      ∘ ((Tensor.₁ B ⊗₁ id) ⊗₁ id)
    ≈ parameter-evaluationˡ ∘ (σ⇒ ⊗₁ id)
  tensor-parameter-evaluation {B = B} {X} {Y} = begin
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((Tensor.₁ _ ⊗₁ id) ⊗₁ id)
      ≈⟨ pull-last assoc-commute-from ⟩
    eval ∘ (id ⊗₁ eval) ∘ (Tensor.₁ _ ⊗₁ (id ⊗₁ id)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
    eval ∘ (id ⊗₁ eval) ∘ (Tensor.₁ _ ⊗₁ id) ∘ α⇒
      ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    eval ∘ (Tensor.₁ _ ⊗₁ (eval ∘ id)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ identityʳ) ⟩∘⟨refl ⟩
    eval ∘ (Tensor.₁ _ ⊗₁ eval) ∘ α⇒
      ≈⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
    eval ∘ (Tensor.₁ _ ⊗₁ id) ∘ (id ⊗₁ eval) ∘ α⇒
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
    parameter-evaluationˡ ∘ (σ⇒ ⊗₁ id) ∎

  trace-precomposition :
    τ ∘ uncurry (SelfEnriched.homʳ₁ X Y (B ⊗₀ X)) ∘ (ρ⇒ ⊗₁ id)
    ≈ trace parameter-evaluation ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
  trace-precomposition = begin
    trace eval ∘ uncurry (SelfEnriched.homʳ₁ _ _ _) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ pullˡ (⟺ tightenᵣ) ⟩
    trace (eval ∘ (uncurry (SelfEnriched.homʳ₁ _ _ _) ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ trace⟨ refl⟩∘⟨ eval-curry ⟩⊗⟨refl ⟩ ⟩∘⟨refl ⟩
    trace (eval ∘ ((internal-∘ ∘ σ⇒) ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ trace⟨ refl⟩∘⟨ split₁ˡ ⟩ ⟩∘⟨refl ⟩
    trace (eval ∘ (internal-∘ ⊗₁ id) ∘ (σ⇒ ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ trace⟨ sym-assoc ⟩ ⟩∘⟨refl ⟩
    trace ((eval ∘ (internal-∘ ⊗₁ id)) ∘ (σ⇒ ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ pushˡ tightenᵣ ⟩
    trace (eval ∘ (internal-∘ ⊗₁ id)) ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ trace⟨ eval-curry ⟩ ⟩∘⟨refl ⟩
    trace parameter-evaluation ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id) ∎

  trace-postcomposition :
    τ {Y} {B} ∘
      uncurry (SelfEnriched.homˡ₁ Y (B ⊗₀ X) (B ⊗₀ Y) ∘ Tensor.₁ B) ∘
      (ρ⇒ ⊗₁ id)
    ≈ trace parameter-evaluationˡ ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
  trace-postcomposition {B = B} {X} = begin
    trace eval ∘
      uncurry (SelfEnriched.homˡ₁ _ _ _ ∘ Tensor.₁ _) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ uncurry-∘ ⟩∘⟨refl ⟩
    trace eval ∘
      (uncurry (SelfEnriched.homˡ₁ _ _ _) ∘ (Tensor.₁ _ ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ (eval-curry ⟩∘⟨refl) ⟩∘⟨refl ⟩
    trace eval ∘ (internal-∘ ∘ (Tensor.₁ _ ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    trace eval ∘ internal-∘ ∘ (Tensor.₁ _ ⊗₁ id) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ pullˡ (⟺ tightenᵣ) ⟩
    trace (eval ∘ (internal-∘ ⊗₁ id)) ∘ (Tensor.₁ _ ⊗₁ id) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ trace⟨ eval-curry ⟩ ⟩∘⟨refl ⟩
    trace (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (Tensor.₁ _ ⊗₁ id) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ pullˡ (⟺ tightenᵣ) ⟩
    trace ((eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((Tensor.₁ _ ⊗₁ id) ⊗₁ id))
      ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ trace⟨ tensor-parameter-evaluation ⟩ ⟩∘⟨refl ⟩
    trace (parameter-evaluationˡ ∘ (σ⇒ ⊗₁ id)) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ pushˡ tightenᵣ ⟩
    trace parameter-evaluationˡ ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id) ∎

private
  τ-actionʳ : (B X Y : Obj) → [ X , Y ]₀ ⇒ [ unit , [ [ Y , B ⊗₀ X ]₀ , B ]₀ ]₀
  τ-actionʳ B X Y = internal-∘ ∘ (Action.mapʳ B X X Y ⊗₁ τ̂ᵉ B X) ∘ ρ⇐

  τ-actionˡ : (B X Y : Obj) → [ X , Y ]₀ ⇒ [ unit , [ [ Y , B ⊗₀ X ]₀ , B ]₀ ]₀
  τ-actionˡ B X Y = internal-∘ ∘ (Action.mapˡ B Y X Y ⊗₁ τ̂ᵉ B Y) ∘ ρ⇐

private abstract
  trace-actionʳ : (B X Y : Obj) → TraceAction.F₁ʳ B {X = X} {Y}
    ≈ OutputF.₁ B {X = [ X , B ⊗₀ X ]₀} {Y = [ Y , B ⊗₀ X ]₀} ∘
      BifunctorHelper.mapʳ (Continuation.helper B) X X Y
  trace-actionʳ B X Y = let
    postcompose : [ [ Y , B ⊗₀ X ]₀ , [ X , B ⊗₀ X ]₀ ]₀ ⇒
      [ [ [ X , B ⊗₀ X ]₀ , B ]₀ , [ [ Y , B ⊗₀ X ]₀ , B ]₀ ]₀
    postcompose = OutputF.₁ B
    in begin
    TraceF.₁ B ∘ (S₁.id ⊗₁ id) ∘ λ⇐
      ≈⟨ traceFunctor₁ B X X X Y ⟩∘⟨refl ⟩
    (postcompose ∘ continuation₁) ∘ (S₁.id ⊗₁ id) ∘ λ⇐
      ≈⟨ pullʳ (FromHelper.diagonal-appˡ (Continuation.helper B)) ⟩
    postcompose ∘ BifunctorHelper.mapʳ (Continuation.helper B) X X Y ∎

  trace-actionˡ : (B X Y : Obj) → TraceAction.F₁ˡ B {X = X} {Y}
    ≈ OutputF.₁ B {X = [ Y , B ⊗₀ Y ]₀} {Y = [ Y , B ⊗₀ X ]₀} ∘
      BifunctorHelper.mapˡ (Continuation.helper B) Y X Y
  trace-actionˡ B X Y = let
    postcompose : [ [ Y , B ⊗₀ X ]₀ , [ Y , B ⊗₀ Y ]₀ ]₀ ⇒
      [ [ [ Y , B ⊗₀ Y ]₀ , B ]₀ , [ [ Y , B ⊗₀ X ]₀ , B ]₀ ]₀
    postcompose = OutputF.₁ B
    in begin
    TraceF.₁ B ∘ (id ⊗₁ S₀.id) ∘ ρ⇐
      ≈⟨ traceFunctor₁ B Y Y X Y ⟩∘⟨refl ⟩
    (postcompose ∘ continuation₁) ∘ (id ⊗₁ S₀.id) ∘ ρ⇐
      ≈⟨ pullʳ (FromHelper.diagonal-appʳ (Continuation.helper B)) ⟩
    postcompose ∘ BifunctorHelper.mapˡ (Continuation.helper B) Y X Y ∎

  actionʳ-eval : (B X Y : Obj) →
    uncurry (uncurry (τ-actionʳ B X Y))
    ≈ trace parameter-evaluation ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
  actionʳ-eval B X Y = begin
    uncurry (uncurry (τ-actionʳ B X Y))
      ≈⟨ uncurry²-∘-⌜⌝ʳ ⟩
    uncurry (uncurry (Action.mapʳ B X X Y)) ∘ ((id ⊗₁ τ̂) ⊗₁ id)
      ≈⟨ eval-⌜pre∘⌝ (SelfEnriched.homʳ₁ X Y (B ⊗₀ X) ∘ id) τ ⟩
    τ ∘ uncurry (SelfEnriched.homʳ₁ X Y (B ⊗₀ X) ∘ id) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ uncurry-resp-≈ identityʳ ⟩∘⟨refl ⟩
    τ ∘ uncurry (SelfEnriched.homʳ₁ X Y (B ⊗₀ X)) ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ trace-precomposition ⟩
    trace parameter-evaluation ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id) ∎

  actionˡ-eval : (B X Y : Obj) →
    uncurry (uncurry (τ-actionˡ B X Y))
    ≈ trace parameter-evaluationˡ ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
  actionˡ-eval B X Y = let
    q : [ X , Y ]₀ ⇒ [ [ Y , B ⊗₀ X ]₀ , [ Y , B ⊗₀ Y ]₀ ]₀
    q = SelfEnriched.homˡ₁ Y (B ⊗₀ X) (B ⊗₀ Y) ∘ Tensor.₁ B
    in begin
    uncurry (uncurry (τ-actionˡ B X Y))
      ≈⟨ uncurry²-∘-⌜⌝ʳ ⟩
    uncurry (uncurry (Action.mapˡ B Y X Y)) ∘ ((id ⊗₁ τ̂) ⊗₁ id)
      ≈⟨ eval-⌜pre∘⌝ q τ ⟩
    τ ∘ uncurry q ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ trace-postcomposition ⟩
    trace parameter-evaluationˡ ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id) ∎

  trace-helper-actions : (B X Y : Obj) →
    internal-∘ ∘ (Action.mapʳ B X X Y ⊗₁ τ̂ᵉ B X) ∘ ρ⇐
    ≈ internal-∘ ∘ (Action.mapˡ B Y X Y ⊗₁ τ̂ᵉ B Y) ∘ ρ⇐
  trace-helper-actions B X Y = uncurry²-injective (begin
    uncurry (uncurry (τ-actionʳ B X Y))
      ≈⟨ actionʳ-eval B X Y ⟩
    trace parameter-evaluation ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
      ≈⟨ parameter-slide ⟩∘⟨refl ⟩
    trace parameter-evaluationˡ ∘ σ⇒ ∘ (ρ⇒ ⊗₁ id)
      ≈˘⟨ actionˡ-eval B X Y ⟩
    uncurry (uncurry (τ-actionˡ B X Y)) ∎)

-- Hajgató--Hasegawa 2013, Lemma 3.1.
τ-extraordinary :
  S₀.⊚ ∘ (TraceAction.F₁ʳ B ⊗₁ τ̂ᵉ B X) ∘ ρ⇐
  ≈ S₀.⊚ ∘ (TraceAction.F₁ˡ B ⊗₁ τ̂ᵉ B Y) ∘ ρ⇐
τ-extraordinary {B = B} {X} {Y} = begin
  S₀.⊚ ∘ (TraceAction.F₁ʳ B ⊗₁ τ̂ᵉ B X) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ trace-actionʳ B X Y ⟩⊗⟨refl ⟩∘⟨refl ⟩
  τ-actionʳ B X Y  ≈⟨ trace-helper-actions B X Y ⟩
  τ-actionˡ B X Y
    ≈˘⟨ refl⟩∘⟨ trace-actionˡ B X Y ⟩⊗⟨refl ⟩∘⟨refl ⟩
  S₀.⊚ ∘ (TraceAction.F₁ˡ B ⊗₁ τ̂ᵉ B Y) ∘ ρ⇐  ∎

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
        ((ρ⇒ ∘ f ∘ ρ⇐) ⊗₁ id) ∘ ρ⇐ ∘ ρ⇒  ≈⟨ pullˡ (⟺ unitorʳ-commute-to) ⟩
        (ρ⇐ ∘ ρ⇒ ∘ f ∘ ρ⇐) ∘ ρ⇒          ≈⟨ cancelˡ unitorʳ.isoˡ ⟩∘⟨refl ⟩
        (f ∘ ρ⇐) ∘ ρ⇒                    ≈⟨ cancelʳ unitorʳ.isoˡ ⟩
        f                                ∎

-- Hajgató--Hasegawa 2013, Lemma 3.1 at the tensor unit.
τ-unit : τ {unit} {B} ≈ ρ⇒ ∘ unit-hom⇐
τ-unit = trace-unit
