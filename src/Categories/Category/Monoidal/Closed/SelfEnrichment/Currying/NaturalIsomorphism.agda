{-# OPTIONS --without-K --safe --lossy-unification #-}

-- --lossy-unification keeps enriched functor composition below a minute.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Enriched naturality of double currying follows Kelly,
-- "Basic Concepts of Enriched Category Theory", Section 1.11.

module Categories.Category.Monoidal.Closed.SelfEnrichment.Currying.NaturalIsomorphism
  {o ℓ e} {𝒱 : Category o ℓ e} {M : Monoidal 𝒱}
  (S : Symmetric M) (Cl : Closed M) where

open import Data.Product using (_,_)

import Categories.Category.Construction.Core 𝒱 as Core

open Category 𝒱
open Core.Shorthands using (idᵢ)
open Monoidal M
open Symmetric S using (braided; braided-iso; commutative; hexagon₁)
open Closed Cl using ([-,-]; [_,_]₀)
open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Closed.Currying Cl
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment S Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Adjunction S Cl using (evalᵀ)
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M
  using ( assoc-to-coherence; α⇒-id⊗-commute; α⇒-⊗id-commute
        ; α⇐-id⊗-commute; α⇐-⊗id-commute )
open import Categories.Category.Monoidal.Symmetric.Properties S
  using (braiding-selfInverse; module Rotation)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Interchange.Braided braided
  using (module swapInner) renaming (hasInterchange to interchange)
open import Categories.Enriched.Bifunctor S
  using ( BifunctorHelper; bifunctorHelper; op₂F; op₂-helper; postcompose-helper
        ; reduce-helper; appʳ; module FromHelper; module Helper; module Postcomposition )
open import Categories.Enriched.Bifunctor.NaturalTransformation S
  using (BifunctorNTHelper; bifunctorNTHelper)
open import Categories.Enriched.Category.TensorProduct interchange using (_⊠_)
open import Categories.Enriched.Category.Opposite S renaming (op to opE)
open import Categories.Enriched.Functor M using (Functor; _∘F_) renaming (id to idF)
open import Categories.Enriched.Functor.TensorProduct interchange using (_⊠F_)
open import Categories.Enriched.NaturalTransformation M using (NTHelper)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism; niHelper)
open import Categories.Morphism 𝒱 using (Iso; _≅_)
open import Categories.Morphism.Reasoning 𝒱
open Shorthands
open BraidShorthands
open Rotation using (rotate-tail)
open SelfEnriched using (homHelper; homFunctor; homˡ₁; homʳ₁)
  renaming (homʳFunctor to homʳ)

open import Categories.Category.Monoidal.Interchange.Symmetric S
  using (swapInner-braidingʳ)

open import Categories.Category.Monoidal.Closed.SelfEnrichment.Currying S Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Tensor S Cl

private
  i⇒ = swapInner.from

  variable
    A B C : Obj -- tensor arguments
    W X Y : Obj -- source, parameter, and target roles

private

  precompose-eval : {f : A ⇒ [ B , C ]₀} →
    uncurry (uncurry (homʳ₁ B C X ∘ f))
    ≈ eval ∘ (id ⊗₁ uncurry f) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
  precompose-eval {f = f} = begin
    uncurry (uncurry (homʳ₁ _ _ _ ∘ f))
      ≈˘⟨ identityʳ ⟩
    uncurry (uncurry (homʳ₁ _ _ _ ∘ f)) ∘ id
      ≈˘⟨ refl⟩∘⟨ ⊗.identity ⟩
    uncurry (uncurry (homʳ₁ _ _ _ ∘ f)) ∘ (id ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl) ⟩
    uncurry (uncurry (homʳ₁ _ _ _ ∘ f)) ∘ ((id ⊗₁ id) ⊗₁ id)
      ≈⟨ evaluate-precomposition ⟩
    uncurry id ∘ (id ⊗₁ uncurry f) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈⟨ elimʳ ⊗.identity ⟩∘⟨refl ⟩
    eval ∘ (id ⊗₁ uncurry f) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∎

  precompose-id-eval : {f : W ⇒ [ C , X ]₀} →
    uncurry (uncurry (homʳ₁ B C X)) ∘ ((id ⊗₁ f) ⊗₁ id)
    ≈ uncurry f ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
  precompose-id-eval {f = f} = begin
    uncurry (uncurry (homʳ₁ _ _ _)) ∘ ((id ⊗₁ f) ⊗₁ id)
      ≈˘⟨ uncurry-resp-≈ (uncurry-resp-≈ identityʳ) ⟩∘⟨refl ⟩
    uncurry (uncurry (homʳ₁ _ _ _ ∘ id)) ∘ ((id ⊗₁ f) ⊗₁ id)
      ≈⟨ evaluate-precomposition ⟩
    uncurry f ∘ (id ⊗₁ uncurry id) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ elimʳ ⊗.identity) ⟩∘⟨refl ⟩
    uncurry f ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∎

  ⊗-input-α : {f : A ⇒ B ⊗₀ C} →
    (id ⊗₁ α⇐) ∘ α⇒ ∘ (f ⊗₁ id {W ⊗₀ X}) ∘ α⇒
    ≈ α⇒ ∘ (α⇒ ⊗₁ id) ∘ ((f ⊗₁ id {W}) ⊗₁ id {X})
  ⊗-input-α {f = f} = begin
    (id ⊗₁ α⇐) ∘ α⇒ ∘ (f ⊗₁ id) ∘ α⇒
      ≈⟨ pullˡ assoc-to-coherence ⟩
    (α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐) ∘ (f ⊗₁ id) ∘ α⇒
      ≈⟨ assoc²βε ⟩
    α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐ ∘ (f ⊗₁ id) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ α⇐-⊗id-commute ⟩
    α⇒ ∘ (α⇒ ⊗₁ id) ∘ ((f ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimʳ associator.isoˡ ⟩
    α⇒ ∘ (α⇒ ⊗₁ id) ∘ ((f ⊗₁ id) ⊗₁ id) ∎

  σ-pair : (α⇒ {B} {C} {A} ⊗₁ id {W}) ∘
      (σ⇒ {A} {B ⊗₀ C} ⊗₁ id) ∘ (α⇒ ⊗₁ id)
    ≈ ((id ⊗₁ σ⇒) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ⊗₁ id)
  σ-pair = merge₁³ ○ ((⟺ hexagon₁) ⟩⊗⟨refl) ○ split₁³

  pentagon⇒ : (A : Obj) → α⇒ {A} {B ⊗₀ C} {W} ∘ (α⇒ ⊗₁ id)
    ≈ ((id ⊗₁ α⇐) ∘ α⇒) ∘ α⇒
  pentagon⇒ A = switch-tofromʳ associator (assoc ○ ⟺ assoc-to-coherence)

  ⊗σ-apply : (f : B ⊗₀ Y ⇒ X) →
    (id {W} ⊗₁ ((id {A} ⊗₁ f) ∘ α⇒ {A} {B} {Y} ∘
      (σ⇒ {B} {A} ⊗₁ id {Y}))) ∘
      (id ⊗₁ α⇐ {B} {A} {Y})
    ≈ id ⊗₁ ((id {A} ⊗₁ f) ∘ α⇒ {A} {B} {Y} ∘
      (σ⇒ {B} {A} ⊗₁ id {Y}) ∘ α⇐ {B} {A} {Y})
  ⊗σ-apply f = merge₂ʳ ○ (refl⟩⊗⟨ assoc²βε)

  ⊗σ-α : (f : B ⊗₀ Y ⇒ X) →
    (id {W} ⊗₁ (id {A} ⊗₁ f)) ∘ (id ⊗₁ α⇒) ∘
      (id ⊗₁ (σ⇒ {B} {A} ⊗₁ id {Y})) ∘ (id ⊗₁ α⇐)
    ≈ id ⊗₁ ((id ⊗₁ f) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)
  ⊗σ-α f = assoc²εβ ○ (merge₂³ ⟩∘⟨refl) ○ ⊗σ-apply f

  pentagon-σ : α⇒ {W} {A} {B ⊗₀ Y} ∘ α⇒ {W ⊗₀ A} {B} {Y} ∘
      (σ⇒ {B} {W ⊗₀ A} ⊗₁ id {Y}) ∘ (α⇒ {B} {W} {A} ⊗₁ id {Y})
    ≈ (id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘
      (σ⇒ ⊗₁ id) ∘ (α⇒ ⊗₁ id)
  pentagon-σ = sym-assoc ○ (⟺ pentagon ⟩∘⟨refl) ○ assoc²βε

  eval-⟲ : (W : Obj) (f : B ⊗₀ Y ⇒ X) →
    α⇒ {W} {A} {X} ∘ (id ⊗₁ f) ∘ α⇒ ∘
      (σ⇒ {B} {W ⊗₀ A} ⊗₁ id) ∘ (α⇒ ⊗₁ id)
    ≈ (id ⊗₁ ((id ⊗₁ f) ∘ α⇒ ∘ (σ⇒ {B} {A} ⊗₁ id) ∘ α⇐)) ∘
      (α⇒ ∘ (σ⇒ {B} {W} ⊗₁ id) ∘ α⇒)
  eval-⟲ W f = begin
    α⇒ ∘ (id ⊗₁ f) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈⟨ pullˡ α⇒-id⊗-commute ⟩
    ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ (α⇒ ⊗₁ id))
      ≈⟨ pullʳ pentagon-σ ⟩
    (id ⊗₁ (id ⊗₁ f)) ∘ (id ⊗₁ α⇒) ∘ α⇒ ∘
      (α⇒ ⊗₁ id) ∘ (σ⇒ ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ σ-pair ⟩
    (id ⊗₁ (id ⊗₁ f)) ∘ (id ⊗₁ α⇒) ∘ α⇒ ∘
      ((id ⊗₁ σ⇒) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
    (id ⊗₁ (id ⊗₁ f)) ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (σ⇒ ⊗₁ id)) ∘
      α⇒ ∘ (α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (pentagon⇒ W) ⟩
    (id ⊗₁ (id ⊗₁ f)) ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (σ⇒ ⊗₁ id)) ∘
      ((id ⊗₁ α⇐) ∘ α⇒) ∘ α⇒ ∘ ((σ⇒ ⊗₁ id) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    (id ⊗₁ (id ⊗₁ f)) ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (σ⇒ ⊗₁ id)) ∘
      (id ⊗₁ α⇐) ∘ α⇒ ∘ α⇒ ∘ ((σ⇒ ⊗₁ id) ⊗₁ id)
      ≈⟨ reassoc-tail₅ ⟩
    ((id ⊗₁ (id ⊗₁ f)) ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ (σ⇒ ⊗₁ id)) ∘
      (id ⊗₁ α⇐)) ∘ (α⇒ ∘ α⇒ ∘ ((σ⇒ ⊗₁ id) ⊗₁ id))
      ≈⟨ ⊗σ-α f ⟩∘⟨refl ⟩
    (id ⊗₁ ((id ⊗₁ f) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘
      α⇒ ∘ α⇒ ∘ ((σ⇒ ⊗₁ id) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ rotate-tail ⟩
    (id ⊗₁ ((id ⊗₁ f) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘
      α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇒ ∎

  curry₂-sourceH : Obj → BifunctorHelper
    (opE selfEnrichment) (opE selfEnrichment) selfEnrichment
  curry₂-sourceH C = postcompose-helper (homʳ C) (op₂-helper tensorHelper)

  curry₂-targetH : Obj → BifunctorHelper
    (opE selfEnrichment) (opE selfEnrichment) selfEnrichment
  curry₂-targetH C = reduce-helper homHelper idF (homʳ C)

curry₂-source : Obj → Functor
  (opE selfEnrichment ⊠ opE selfEnrichment) selfEnrichment
curry₂-source C = bifunctorHelper (curry₂-sourceH C)

curry₂-target : Obj → Functor
  (opE selfEnrichment ⊠ opE selfEnrichment) selfEnrichment
curry₂-target C = bifunctorHelper (curry₂-targetH C)

private module Tensorᵒ = Postcomposition {H = op₂-helper tensorHelper}

module Curry₂Source (C : Obj) where
  actionᵒ : Functor.₁ (op₂F (curry₂-source C)) {X = A , X} {Y = B , Y}
    ≈ homʳ₁ (A ⊗₀ X) (B ⊗₀ Y) C ∘ ⊗-map₁
  actionᵒ {A} {X} {B} {Y} = begin
    Functor.₁ (op₂F (curry₂-source C))
      ≈⟨ Tensorᵒ.diagonal (homʳ C) ⟩
    homʳ₁ (A ⊗₀ X) (B ⊗₀ Y) C ∘ FromHelper.diagonal (op₂-helper tensorHelper)
      ≈⟨ refl⟩∘⟨ Helper.op₂-diagonal tensorHelper B A Y X ⟩
    homʳ₁ (A ⊗₀ X) (B ⊗₀ Y) C ∘ FromHelper.diagonal tensorHelper
      ≈⟨ refl⟩∘⟨ tensor-diagonal ⟩
    homʳ₁ (A ⊗₀ X) (B ⊗₀ Y) C ∘ ⊗-map₁ ∎

private module Curry₂Naturality (C : Obj) where
  module SourceH = BifunctorHelper (curry₂-sourceH C)
  module TargetH = BifunctorHelper (curry₂-targetH C)
  module Naturalˡ X = SelfNatural
    {F = FromHelper.appʳ (curry₂-sourceH C) X} {G = FromHelper.appʳ (curry₂-targetH C) X}
  module Naturalʳ A = SelfNatural
    {F = FromHelper.appˡ (curry₂-sourceH C) A} {G = FromHelper.appˡ (curry₂-targetH C) A}
  module Naturalˡ⁻¹ X = SelfNatural
    {F = FromHelper.appʳ (curry₂-targetH C) X} {G = FromHelper.appʳ (curry₂-sourceH C) X}
  module Naturalʳ⁻¹ A = SelfNatural
    {F = FromHelper.appˡ (curry₂-targetH C) A} {G = FromHelper.appˡ (curry₂-sourceH C) A}

  sourceˡ : (A B X : Obj) → SourceH.mapˡ A B X
    ≈ homʳ₁ (B ⊗₀ X) (A ⊗₀ X) C ∘ ((B ⊗₁ˡ A) X)
  sourceˡ A B X = refl⟩∘⟨ tensorˡ-action B A X

  targetˡ : (A B X : Obj) → TargetH.mapˡ A B X ≈ homʳ₁ B A [ X , C ]₀
  targetˡ A B X = identityʳ

  sourceʳ : (A X Y : Obj) → SourceH.mapʳ A X Y
    ≈ homʳ₁ (A ⊗₀ Y) (A ⊗₀ X) C ∘ ((A ⊗₁ʳ Y) X)
  sourceʳ A X Y = refl⟩∘⟨ tensorʳ-action A Y X

  sourceβˡ : (A B X : Obj) →
    uncurry (uncurry (curry₂ {B} {X} {C} ∘ uncurry (SourceH.mapˡ A B X)))
    ≈ (eval ∘ (id ⊗₁ uncurry ((B ⊗₁ˡ A) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ α⇒
  sourceβˡ A B X = begin
    uncurry (uncurry (curry₂ ∘ uncurry (SourceH.mapˡ A B X)))
      ≈⟨ uncurry²-curry₂-∘ ⟩
    uncurry (uncurry (SourceH.mapˡ A B X)) ∘ α⇒
      ≈⟨ uncurry-resp-≈ (uncurry-resp-≈ (sourceˡ A B X)) ⟩∘⟨refl ⟩
    uncurry (uncurry (homʳ₁ _ _ _ ∘ ((B ⊗₁ˡ A) X))) ∘ α⇒
      ≈⟨ precompose-eval ⟩∘⟨refl ⟩
    (eval ∘ (id ⊗₁ uncurry ((B ⊗₁ˡ A) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ α⇒ ∎

  targetβˡ : (A B X : Obj) →
    uncurry (uncurry
      (uncurry (TargetH.mapˡ A B X) ∘ (id ⊗₁ curry₂ {A} {X} {C})))
    ≈ uncurry (uncurry curry₂ ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id))
  targetβˡ A B X = begin
    uncurry (uncurry (uncurry (TargetH.mapˡ A B X) ∘ (id ⊗₁ curry₂)))
      ≈⟨ uncurry-resp-≈ uncurry-∘ ⟩
    uncurry (uncurry (uncurry (TargetH.mapˡ A B X)) ∘ ((id ⊗₁ curry₂) ⊗₁ id))
      ≈⟨ uncurry-resp-≈ (uncurry-resp-≈ (uncurry-resp-≈ (targetˡ A B X)) ⟩∘⟨refl) ⟩
    uncurry (uncurry (uncurry (homʳ₁ B A [ X , C ]₀)) ∘ ((id ⊗₁ curry₂) ⊗₁ id))
      ≈⟨ uncurry-resp-≈ precompose-id-eval ⟩
    uncurry (uncurry curry₂ ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∎

  curry₂βˡ : (A B X : Obj) →
    uncurry (uncurry curry₂ ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id))
    ≈ (eval {A ⊗₀ X} {C} ∘ (id ⊗₁ uncurry ((B ⊗₁ˡ A) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ α⇒
  curry₂βˡ A B X = begin
    uncurry (uncurry curry₂ ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id))
      ≈⟨ uncurry-∘ ⟩
    uncurry (uncurry curry₂) ∘ (((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ⊗₁ id)
      ≈⟨ uncurry²-curry₂ ⟩∘⟨refl ⟩
    (eval ∘ α⇒) ∘ (((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ⊗₁ id)
      ≈⟨ pullʳ (refl⟩∘⟨ split₁³) ⟩
    eval ∘ α⇒ ∘ ((id ⊗₁ eval) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
    eval ∘ (id ⊗₁ (eval ⊗₁ id)) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-input-α ⟩
    eval ∘ (id ⊗₁ (eval ⊗₁ id)) ∘ (id ⊗₁ α⇐) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇒
      ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    eval ∘ (id ⊗₁ ((eval ⊗₁ id) ∘ α⇐)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇒
      ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ eval-curry ⟩∘⟨refl ⟩
    eval ∘ (id ⊗₁ uncurry ((B ⊗₁ˡ A) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇒
      ≈⟨ reassoc-tail₅ ⟩
    (eval ∘ (id ⊗₁ uncurry ((B ⊗₁ˡ A) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ α⇒ ∎

  curry₂□ˡ : (A B X : Obj) →
    curry₂ ∘ uncurry (SourceH.mapˡ A B X)
    ≈ uncurry (TargetH.mapˡ A B X) ∘ (id ⊗₁ curry₂)
  curry₂□ˡ A B X = uncurry²-injective
    (sourceβˡ A B X ○ ⟺ (targetβˡ A B X ○ curry₂βˡ A B X))

  sourceβʳ : (A X Y : Obj) →
    uncurry (uncurry (curry₂ {A} {Y} {C} ∘ uncurry (SourceH.mapʳ A X Y)))
    ≈ (eval ∘ (id ⊗₁ uncurry ((A ⊗₁ʳ Y) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ α⇒
  sourceβʳ A X Y = begin
    uncurry (uncurry (curry₂ ∘ uncurry (SourceH.mapʳ A X Y)))
      ≈⟨ uncurry²-curry₂-∘ ⟩
    uncurry (uncurry (SourceH.mapʳ A X Y)) ∘ α⇒
      ≈⟨ uncurry-resp-≈ (uncurry-resp-≈ (sourceʳ A X Y)) ⟩∘⟨refl ⟩
    uncurry (uncurry (homʳ₁ _ _ _ ∘ ((A ⊗₁ʳ Y) X))) ∘ α⇒
      ≈⟨ precompose-eval ⟩∘⟨refl ⟩
    (eval ∘ (id ⊗₁ uncurry ((A ⊗₁ʳ Y) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ α⇒ ∎

  target-evalʳ : (A X Y : Obj) → uncurry (TargetH.mapʳ A X Y)
    ≈ internal-∘ ∘ (homʳ₁ Y X C ⊗₁ id)
  target-evalʳ A X Y = begin
    uncurry (TargetH.mapʳ A X Y)
      ≈⟨ uncurry-∘ ⟩
    uncurry (homˡ₁ A [ X , C ]₀ [ Y , C ]₀) ∘ (homʳ₁ Y X C ⊗₁ id)
      ≈⟨ eval-curry ⟩∘⟨refl ⟩
    internal-∘ ∘ (homʳ₁ Y X C ⊗₁ id) ∎

  target-curryʳ : (A X Y : Obj) →
    uncurry (TargetH.mapʳ A X Y) ∘ (id ⊗₁ curry₂ {A} {X} {C})
    ≈ curry (uncurry (homʳ₁ Y X C) ∘ (id ⊗₁ uncurry curry₂) ∘ α⇒)
  target-curryʳ A X Y = begin
    uncurry (TargetH.mapʳ A X Y) ∘ (id ⊗₁ curry₂)
      ≈⟨ target-evalʳ A X Y ⟩∘⟨refl ⟩
    (internal-∘ ∘ (homʳ₁ Y X C ⊗₁ id)) ∘ (id ⊗₁ curry₂)
      ≈⟨ pullʳ merge₂ʳ ⟩
    internal-∘ ∘ (homʳ₁ Y X C ⊗₁ (id ∘ curry₂))
      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ identityˡ ⟩
    internal-∘ ∘ (homʳ₁ Y X C ⊗₁ curry₂)
      ≈⟨ internal-∘-curry′ (homʳ₁ Y X C) curry₂ ⟩
    curry (uncurry (homʳ₁ Y X C) ∘ (id ⊗₁ uncurry curry₂) ∘ α⇒) ∎

  targetβʳ : (A X Y : Obj) →
    uncurry (uncurry
      (uncurry (TargetH.mapʳ A X Y) ∘ (id ⊗₁ curry₂ {A} {X} {C})))
    ≈ (uncurry (uncurry curry₂) ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ (α⇒ ⊗₁ id)
  targetβʳ A X Y = begin
    uncurry (uncurry (uncurry (TargetH.mapʳ A X Y) ∘ (id ⊗₁ curry₂)))
      ≈⟨ uncurry-resp-≈ (uncurry-resp-≈ (target-curryʳ A X Y)) ⟩
    uncurry (uncurry (curry (uncurry (homʳ₁ Y X C) ∘ (id ⊗₁ uncurry curry₂) ∘ α⇒)))
      ≈⟨ uncurry-resp-≈ eval-curry ⟩
    uncurry (uncurry (homʳ₁ Y X C) ∘ (id ⊗₁ uncurry curry₂) ∘ α⇒)
      ≈⟨ uncurry-∘ ⟩
    uncurry (uncurry (homʳ₁ Y X C)) ∘ (((id ⊗₁ uncurry curry₂) ∘ α⇒) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    uncurry (uncurry (homʳ₁ Y X C)) ∘
      ((id ⊗₁ uncurry curry₂) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈⟨ pullˡ precompose-id-eval ⟩
    (uncurry (uncurry curry₂) ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ (α⇒ ⊗₁ id) ∎

  curry₂-rotate : (A X Y : Obj) →
    (eval {A ⊗₀ X} {C} ∘ α⇒ {[ A ⊗₀ X , C ]₀} {A} {X}) ∘
      (((id ⊗₁ eval {Y} {X}) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ (α⇒ ⊗₁ id))
    ≈ eval ∘ (id ⊗₁ ev⊗ʳ A Y X) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇒
  curry₂-rotate A X Y = begin
    (eval ∘ α⇒) ∘ (((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ (α⇒ ⊗₁ id))
      ≈⟨ pullʳ (refl⟩∘⟨ assoc²βε) ⟩
    eval ∘ α⇒ ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ eval-⟲ [ A ⊗₀ X , C ]₀ eval ⟩
    eval ∘ (id ⊗₁ ev⊗ʳ A Y X) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇒ ∎

  curry₂βʳ : (A X Y : Obj) →
    (uncurry (uncurry curry₂) ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ (α⇒ ⊗₁ id)
    ≈ (eval ∘ (id ⊗₁ uncurry ((A ⊗₁ʳ Y) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ α⇒
  curry₂βʳ A X Y = begin
    (uncurry (uncurry curry₂) ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ (α⇒ ⊗₁ id)
      ≈⟨ assoc ⟩
    uncurry (uncurry curry₂) ∘
      (((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ (α⇒ ⊗₁ id))
      ≈⟨ uncurry²-curry₂ ⟩∘⟨refl ⟩
    (eval ∘ α⇒) ∘ (((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ (α⇒ ⊗₁ id))
      ≈⟨ curry₂-rotate A X Y ⟩
    eval ∘ (id ⊗₁ ev⊗ʳ A Y X) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇒
      ≈˘⟨ refl⟩∘⟨ (refl⟩⊗⟨ eval-curry) ⟩∘⟨refl ⟩
    eval ∘ (id ⊗₁ uncurry ((A ⊗₁ʳ Y) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇒
      ≈⟨ reassoc-tail₅ ⟩
    (eval ∘ (id ⊗₁ uncurry ((A ⊗₁ʳ Y) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ α⇒ ∎

  curry₂□ʳ : (A X Y : Obj) →
    curry₂ ∘ uncurry (SourceH.mapʳ A X Y)
    ≈ uncurry (TargetH.mapʳ A X Y) ∘ (id ⊗₁ curry₂)
  curry₂□ʳ A X Y = uncurry²-injective
    (sourceβʳ A X Y ○ ⟺ (targetβʳ A X Y ○ curry₂βʳ A X Y))

  curry₂□ˡ⁻¹ : (A B X : Obj) →
    uncurry₂ ∘ uncurry (TargetH.mapˡ A B X)
    ≈ uncurry (SourceH.mapˡ A B X) ∘ (id ⊗₁ uncurry₂)
  curry₂□ˡ⁻¹ A B X = conjugate-from
    (idᵢ ⊗ᵢ curry₂-iso) curry₂-iso (⟺ (curry₂□ˡ A B X))

  curry₂□ʳ⁻¹ : (A X Y : Obj) →
    uncurry₂ ∘ uncurry (TargetH.mapʳ A X Y)
    ≈ uncurry (SourceH.mapʳ A X Y) ∘ (id ⊗₁ uncurry₂)
  curry₂□ʳ⁻¹ A X Y = conjugate-from
    (idᵢ ⊗ᵢ curry₂-iso) curry₂-iso (⟺ (curry₂□ʳ A X Y))

  forward : BifunctorNTHelper (curry₂-sourceH C) (curry₂-targetH C)
  forward = record
    { comp = λ A X → ⌜ curry₂ ⌝
    ; naturalˡ = λ X → NTHelper.commute
        (Naturalˡ.from-underlying X (λ A → curry₂) λ { {A} {B} → curry₂□ˡ A B X })
    ; naturalʳ = λ A → NTHelper.commute
        (Naturalʳ.from-underlying A (λ X → curry₂) λ { {X} {Y} → curry₂□ʳ A X Y })
    }

  backward : BifunctorNTHelper (curry₂-targetH C) (curry₂-sourceH C)
  backward = record
    { comp = λ A X → ⌜ uncurry₂ ⌝
    ; naturalˡ = λ X → NTHelper.commute
        (Naturalˡ⁻¹.from-underlying X (λ A → uncurry₂) λ { {A} {B} → curry₂□ˡ⁻¹ A B X })
    ; naturalʳ = λ A → NTHelper.commute
        (Naturalʳ⁻¹.from-underlying A (λ X → uncurry₂) λ { {X} {Y} → curry₂□ʳ⁻¹ A X Y })
    }

curry₂-NI : (C : Obj) → NaturalIsomorphism (curry₂-source C) (curry₂-target C)
curry₂-NI C = niHelper record
  { F⇒G = bifunctorNTHelper (Curry₂Naturality.forward C)
  ; F⇐G = bifunctorNTHelper (Curry₂Naturality.backward C)
  ; iso = λ { (A , X) → record
    { isoˡ = ⌜∘⌝ ○ ⌜⌝-resp-≈ curry₂-iso-uncurry₂
    ; isoʳ = ⌜∘⌝ ○ ⌜⌝-resp-≈ uncurry₂-iso-curry₂
    } }
  }
