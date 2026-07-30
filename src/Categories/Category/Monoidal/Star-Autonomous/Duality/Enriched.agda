{-# OPTIONS --without-K --safe --lossy-unification #-}

-- --lossy-unification keeps enriched functor composition under 4s instead of over 1min.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Enriched naturality for the isomorphisms used in
-- Hajgató--Hasegawa 2013, Lemma 3.2.

module Categories.Category.Monoidal.Star-Autonomous.Duality.Enriched
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (S : Symmetric M) (Cl : Closed M) where

open import Data.Product using (_,_)

import Categories.Enriched.Category as Enriched
import Categories.Morphism as Morphism

open Category 𝒞
open Monoidal M
open Symmetric S using (braided; commutative)
open Closed Cl using ([_,_]₀; [_,_]₁; [-,_]; [_,-]; [-,-])

open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Closed.Currying Cl
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment S Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Tensor S Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Adjunction S Cl
  using (swap-curry-NI)
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Currying.NaturalIsomorphism S Cl
  using (curry₂-NI; curry₂-source; curry₂-target; module Curry₂Source)
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M using (α⇒-⊗id-commute)
open import Categories.Category.Monoidal.Symmetric.Properties S
  using (braiding-selfInverse; mirrorʳ; module Rotation)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Bifunctor S using (op₂F; reduce-⊠)
open import Categories.Enriched.Category.Opposite S renaming (op to opE)
open import Categories.Enriched.Category.Underlying M using (Underlying)
open import Categories.Enriched.Functor M
  using (Functor; Endofunctor; UnderlyingFunctor; _∘F_) renaming (id to idF)
open import Categories.Enriched.Functor.Opposite S using (opF; op²F)
open import Categories.Enriched.Functor.TensorProduct.Symmetric S using (op-⊠F; swapF)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism; niHelper; _ᵢ[_]; _⁻¹; _ⓘᵥ_; _ⓘˡ_; _ⓘʳ_)
  renaming (associator to associator-NI; id to idNI; unitorˡ to unitorˡ-NI)
open import Categories.Enriched.NaturalTransformation M using (NTHelper)
open import Categories.Enriched.NaturalTransformation.Opposite S using (opNI)
open import Categories.Morphism 𝒞 using (_≅_; Iso; module ≅)
open import Categories.Morphism.Duality 𝒞 using (≅⇒op-≅)
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Functor.Properties using ([_]-resp-Iso; [_]-resp-≅)
open Shorthands
open BraidShorthands
open Rotation using (cycle)
open SelfEnriched
  using (homˡ₁; homʳ₁; homˡFunctor; whisker-comm)
  renaming (homʳFunctor to homʳ)

open import Categories.Category.Monoidal.Interchange.Braided braided
  using (module swapInner) renaming (hasInterchange to interchange)
open import Categories.Enriched.Category.TensorProduct interchange using (_⊠_)
open import Categories.Enriched.Functor.TensorProduct interchange using (_⊠F_)
open import Categories.Enriched.NaturalTransformation.TensorProduct interchange using (_⊠NI_)

private
  i⇒ = swapInner.from

import Categories.Category.Monoidal.Star-Autonomous.Duality as StarDuality
import Categories.Category.Monoidal.Star-Autonomous.Duality.Enriched.Functors as EnrichedFunctors
import Categories.Category.Construction.Core 𝒞 as Core

module Base = StarDuality S Cl
open Base using (δ; δ-natural; swap-curry-≅)
open Core.Shorthands using (idᵢ; _∘ᵢ_)

private
  variable
    A B C : Obj -- closed arguments
    W X Y Z : Obj -- source, comparison, and codomain roles

module Dualized (⊥ : Obj) (dualizing : Base.IsDualizing ⊥) where
  private module DualFunctors = EnrichedFunctors.Dualized S Cl ⊥
  open DualFunctors public using (dualᵒF; dual²F)
  open DualFunctors using (dualᵒβ; dualᵒ-action; op-dual²₁; homʳ≃)

  private
    Selfᵒ : _
    Selfᵒ = opE selfEnrichment

    Selfᵉ : _
    Selfᵉ = Selfᵒ ⊠ selfEnrichment

    inputF : Endofunctor Selfᵒ → Functor Selfᵉ Selfᵒ
    inputF F = SelfEnriched.homᵒᵖFunctor ∘F (op²F ⊠F F) ∘F swapF

    F⊗ : Endofunctor Selfᵒ
    F⊗ = ⊥ ⊗Fᵒᵖ-

    Φ : Endofunctor Selfᵒ → SelfProfunctor
    Φ F = homʳ ⊥ ∘F inputF F

  φ-source : SelfProfunctor
  φ-source = Φ F⊗

  φ-target : SelfProfunctor
  φ-target = reduce-⊠ -⊗F- idF (homʳ unit) ∘F swapF

  open Functor (idF {C = selfEnrichment}) using () renaming (₁ to id₁)
  open Functor dualᵒF using () renaming (₁ to dualᵒ₁)
  open Functor dual²F using () renaming (₁ to dual²₁)

  open Base.Dualized ⊥ dualizing

  private
    dualᵒ : A ≅ B → (A *) ≅ (B *)
    dualᵒ iso = [ [-, ⊥ ] ]-resp-≅ (≅⇒op-≅ iso)

    homˡ : (D : Obj) → A ≅ B → [ D , A ]₀ ≅ [ D , B ]₀
    homˡ D = [ [ D ,-] ]-resp-≅

    dual-∘ : (i : A ≅ B) (j : B ≅ C) →
      _≅_.from (dualᵒ j) ∘ _≅_.from (dualᵒ i) ≈ _≅_.from (dualᵒ (j ∘ᵢ i))
    dual-∘ i j = hom-∘ᵣ

    dual-hom-∘ : (i : A ≅ B) (j : B ≅ C) →
      _≅_.from (dualᵒ (homˡ Y j)) ∘ _≅_.from (dualᵒ (homˡ Y i))
      ≈ _≅_.from (dualᵒ (homˡ Y (j ∘ᵢ i)))
    dual-hom-∘ i j = begin
      _≅_.from (dualᵒ (homˡ _ j)) ∘ _≅_.from (dualᵒ (homˡ _ i))
        ≈⟨ hom-∘ᵣ ⟩
      [ [ id , _≅_.to i ]₁ ∘ [ id , _≅_.to j ]₁ , id ]₁
        ≈⟨ [-,-].F-resp-≈ (hom-∘ , Equiv.refl) ⟩
      [ [ id ∘ id , _≅_.to i ∘ _≅_.to j ]₁ , id ]₁
        ≈⟨ [-,-].F-resp-≈ ([-,-].F-resp-≈ (identity² , Equiv.refl) , Equiv.refl) ⟩
      _≅_.from (dualᵒ (homˡ _ (j ∘ᵢ i))) ∎

    feedback⁻ : ⊥ ⊗₀ X ≅ ([ X , unit ]₀ *)
    feedback⁻ =
      dualᵒ (homˡ _ ⊥*-≅) ∘ᵢ
        (dualᵒ swap-curry-≅ ∘ᵢ **-≅)

    feedback-hom : _≅_.from (dualᵒ (homˡ Y (dualᵒ (homˡ X ⊥*-≅)))) ∘
        _≅_.from (dualᵒ (homˡ Y (dualᵒ swap-curry-≅ ∘ᵢ **-≅)))
      ≈ _≅_.from (dualᵒ (homˡ Y feedback⁻))
    feedback-hom = dual-hom-∘ (dualᵒ swap-curry-≅ ∘ᵢ **-≅) (dualᵒ (homˡ _ ⊥*-≅))

    curry-feedback-hom : _≅_.from
        (dualᵒ (homˡ Y (dualᵒ (swap-curry-≅ {A = ⊥} {B = X})))) ∘
        _≅_.from (dualᵒ (homˡ Y **-≅))
      ≈ _≅_.from (dualᵒ (homˡ Y (dualᵒ swap-curry-≅ ∘ᵢ **-≅)))
    curry-feedback-hom = dual-hom-∘ **-≅ (dualᵒ swap-curry-≅)

    φᵀ-≅ : [ Y , ⊥ ⊗₀ X ]₀ ≅ (Y ⊗₀ [ X , unit ]₀) *
    φᵀ-≅ = ≅.sym curry₂-iso ∘ᵢ homˡ _ feedback⁻

    K⊗ K* : Functor Selfᵒ selfEnrichment
    K⊗ = homʳ ⊥ ∘F F⊗
    K* = homʳ (⊥ *)

    abstract
      κβ : uncurry (uncurry (_≅_.from (swap-curry-≅ {A} {B} {C})))
        ≈ eval ∘ (id ⊗₁ σ⇐ {A} {B}) ∘ α⇒ { [ A ⊗₀ B , C ]₀} {B} {A}
      κβ {A} {B} {C} = begin
        uncurry (uncurry (_≅_.from swap-curry-≅))
          ≈⟨ uncurry-resp-≈ uncurry-∘ ⟩
        uncurry (uncurry curry₂ ∘ ([ σ⇐ , id ]₁ ⊗₁ id))
          ≈⟨ uncurry-∘ ⟩
        uncurry (uncurry curry₂) ∘ (([ σ⇐ , id ]₁ ⊗₁ id) ⊗₁ id)
          ≈⟨ uncurry²-curry₂ ⟩∘⟨refl ⟩
        (eval ∘ α⇒) ∘ (([ σ⇐ , id ]₁ ⊗₁ id) ⊗₁ id)
          ≈⟨ swap-under-curry ⟩
        eval ∘ (id ⊗₁ σ⇐) ∘ α⇒ ∎
        where
          swap-under-curry : (eval {B ⊗₀ A} {C} ∘ α⇒ { [ B ⊗₀ A , C ]₀} {B} {A}) ∘
              (([ σ⇐ {A} {B} , id ]₁ ⊗₁ id) ⊗₁ id)
            ≈ eval ∘ (id ⊗₁ σ⇐) ∘ α⇒ { [ A ⊗₀ B , C ]₀} {B} {A}
          swap-under-curry = glue eval-comm-dom α⇒-⊗id-commute

    F² F²ᶜ Fᶜ Fⁱ : Endofunctor Selfᵒ
    F² = opF dual²F ∘F F⊗
    F²ᶜ = dualᵒF ∘F (homʳ ⊥ ∘F F⊗)
    Fᶜ = dualᵒF ∘F homʳ (⊥ *)
    Fⁱ = dualᵒF ∘F homʳ unit

    Fᵀ : Functor Selfᵉ Selfᵒ
    Fᵀ = dualᵒF ∘F φ-target

    Φ² Φᶜ Φⁱ Φᵀ : SelfProfunctor
    Φ² = Φ F²
    Φᶜ = Φ Fᶜ
    Φⁱ = Φ Fⁱ
    Φᵀ = dual²F ∘F φ-target

    σα⟲ : α⇐ {B *} {[ A , B ]₀} {A} ∘ σ⇒
      ≈ σ⇒ ∘ cycle {[ A , B ]₀} {A} {B *}
    σα⟲ = ⟺ (switch-tofromʳ σ (begin
      (σ⇒ ∘ cycle) ∘ σ⇐                       ≈˘⟨ reassoc-tail₅ ⟩
      σ⇒ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ σ⇐  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ mirrorʳ ⟩
      σ⇒ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ σ⇒ ∘ (id ⊗₁ σ⇒)  ≈˘⟨ braiding-selfInverse ⟩∘⟨refl ⟩
      σ⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ σ⇒ ∘ (id ⊗₁ σ⇒)  ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ braiding-selfInverse ⟩∘⟨refl ⟩
      σ⇐ ∘ (id ⊗₁ σ⇐) ∘ α⇒ ∘ σ⇒ ∘ (id ⊗₁ σ⇒)  ≈⟨ assoc-reverse ⟩
      α⇐                                      ∎))

  δ²□ : δ {A = B} ⊥ ∘ uncurry (id₁ {X = A} {Y = B})
    ≈ uncurry (dual²₁ {X = A} {Y = B}) ∘ (id ⊗₁ δ {A = A} ⊥)
  δ²□ {A} {B} = uncurry-injective (begin
    uncurry (δ ⊥ ∘ uncurry id₁)                        ≈⟨ uncurry-resp-≈ (refl⟩∘⟨ elimʳ ⊗.identity) ⟩
    uncurry (δ ⊥ ∘ eval)                                ≈˘⟨ uncurry-resp-≈ (δ-natural eval) ⟩
    uncurry (([ [ eval , id ]₁ , id ]₁) ∘ δ ⊥)          ≈˘⟨ uncurry-resp-≈ (refl⟩∘⟨ identityʳ) ⟩
    uncurry (([ [ eval , id ]₁ , id ]₁) ∘ δ ⊥ ∘ id)      ≈⟨ Base.uncurry-δ ⟩
    eval ∘ ([ eval , id ]₁ ⊗₁ id) ∘ σ⇒                    ≈⟨ pullˡ eval-comm-dom ⟩
    (eval ∘ (id ⊗₁ eval)) ∘ σ⇒                         ≈⟨ pullʳ (refl⟩∘⟨ introˡ associator.isoʳ) ⟩
    eval ∘ (id ⊗₁ eval) ∘ ((α⇒ ∘ α⇐) ∘ σ⇒)                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (α⇐ ∘ σ⇒)
      ≈⟨ assoc²εβ ⟩
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (α⇐ ∘ σ⇒)                  ≈˘⟨ eval-internal-∘ ⟩∘⟨refl ⟩
    (eval ∘ (internal-∘ ⊗₁ id)) ∘ (α⇐ ∘ σ⇒)                 ≈⟨ extendˡ (refl⟩∘⟨ σα⟲) ⟩
    (eval ∘ (internal-∘ ⊗₁ id)) ∘ (σ⇒ ∘ cycle)              ≈˘⟨ extend² σ⇒-comm ⟩
    (eval ∘ σ⇒) ∘ ((id ⊗₁ internal-∘) ∘ cycle)              ≈⟨ extendˡ (refl⟩∘⟨ pullˡ merge₂ˡ) ⟩
    (eval ∘ σ⇒) ∘ (id ⊗₁ (internal-∘ ∘ σ⇒)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈˘⟨ eval-curry ⟩∘⟨refl ⟩
    uncurry (δ ⊥) ∘ (id ⊗₁ (internal-∘ ∘ σ⇒)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ (refl⟩⊗⟨ dualᵒβ) ⟩∘⟨refl ⟩
    uncurry (δ ⊥) ∘ (id ⊗₁ uncurry dualᵒ₁) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)  ≈˘⟨ evaluate-precomposition ⟩
    uncurry (uncurry dual²₁) ∘ ((id ⊗₁ δ ⊥) ⊗₁ id)             ≈˘⟨ uncurry-∘ ⟩
    uncurry (uncurry dual²₁ ∘ (id ⊗₁ δ ⊥))                     ∎)

  private
    module **-Natural = SelfNatural {F = idF} {G = dual²F}

    **-NI : NaturalIsomorphism idF dual²F
    **-NI = **-Natural.pointwise-iso **-≅ δ²□

    open Functor F⊗ using () renaming (₁ to F⊗₁)
    open Functor F² using () renaming (₁ to F²₁)
    open Functor F²ᶜ using () renaming (₁ to F²ᶜ₁)

    double-dual-action : F²₁ {X = A} {Y = B} ≈ F²ᶜ₁ {X = A} {Y = B}
    double-dual-action = begin
      F²₁                                   ≈⟨ op-dual²₁ ⟩∘⟨refl ⟩
      Functor.₁ (dualᵒF ∘F homʳ ⊥) ∘ F⊗₁  ≈⟨ assoc ⟩
      F²ᶜ₁                                  ∎

    δ²⊗ : uncurry (F²₁ {X = X} {Y = Z}) ∘ (id ⊗₁ δ {A = ⊥ ⊗₀ Z} ⊥)
      ≈ δ {A = ⊥ ⊗₀ X} ⊥ ∘ uncurry (F⊗₁ {X = X} {Y = Z})
    δ²⊗ = begin
      uncurry F²₁ ∘ (id ⊗₁ δ ⊥)                       ≈⟨ uncurry-∘ ⟩∘⟨refl ⟩
      (uncurry dual²₁ ∘ (F⊗₁ ⊗₁ id)) ∘ (id ⊗₁ δ ⊥)  ≈⟨ pullʳ (⟺ serialize₁₂) ⟩
      uncurry dual²₁ ∘ (F⊗₁ ⊗₁ δ ⊥)                 ≈⟨ pushʳ serialize₂₁ ⟩
      (uncurry dual²₁ ∘ (id ⊗₁ δ ⊥)) ∘ (F⊗₁ ⊗₁ id)  ≈˘⟨ δ²□ ⟩∘⟨refl ⟩
      (δ ⊥ ∘ uncurry id₁) ∘ (F⊗₁ ⊗₁ id)             ≈⟨ pullʳ (⟺ uncurry-∘) ⟩
      δ ⊥ ∘ uncurry (id₁ ∘ F⊗₁)                     ≈⟨ refl⟩∘⟨ uncurry-resp-≈ identityˡ ⟩
      δ ⊥ ∘ uncurry F⊗₁                              ∎

    F²≃F⊗ : NaturalIsomorphism F² F⊗
    F²≃F⊗ = SelfNaturalᵒ.pointwise-iso (≅.sym **-≅) δ²⊗

    F²≃F²ᶜ : NaturalIsomorphism F² F²ᶜ
    F²≃F²ᶜ = SelfNaturalᵒ.pointwise-iso idᵢ (begin
      uncurry F²₁ ∘ (id ⊗₁ id)  ≈⟨ elimʳ ⊗.identity ⟩
      uncurry F²₁               ≈⟨ uncurry-resp-≈ double-dual-action ⟩
      uncurry F²ᶜ₁              ≈˘⟨ identityˡ ⟩
      id ∘ uncurry F²ᶜ₁         ∎)

    Fᶜ≃F²ᶜ : NaturalIsomorphism Fᶜ F²ᶜ
    Fᶜ≃F²ᶜ = dualᵒF ⓘˡ swap-curry-NI

    F²≃Fᶜ : NaturalIsomorphism F² Fᶜ
    F²≃Fᶜ = (Fᶜ≃F²ᶜ ⁻¹) ⓘᵥ F²≃F²ᶜ

    Φ₁ : {F G : Endofunctor Selfᵒ} → NaturalIsomorphism F G → NaturalIsomorphism (Φ F) (Φ G)
    Φ₁ η = homʳ ⊥ ⓘˡ (SelfEnriched.homᵒᵖFunctor ⓘˡ ((idNI ⊠NI η) ⓘʳ swapF))

    Fᶜ≃Fⁱ : NaturalIsomorphism Fᶜ Fⁱ
    Fᶜ≃Fⁱ = dualᵒF ⓘˡ homʳ≃ ⊥*-≅

    Φᶜ≃Φⁱ : NaturalIsomorphism Φᶜ Φⁱ
    Φᶜ≃Φⁱ = Φ₁ Fᶜ≃Fⁱ

    -- Insert the feedback object's double dual.
    Φ²≃ : NaturalIsomorphism φ-source Φ²
    Φ²≃ = (Φ₁ F²≃F⊗) ⁻¹

    Φ²≃Φᶜ : NaturalIsomorphism Φ² Φᶜ
    Φ²≃Φᶜ = Φ₁ F²≃Fᶜ

    Φᵀ≃φ : NaturalIsomorphism Φᵀ φ-target
    Φᵀ≃φ = unitorˡ-NI ⓘᵥ ((**-NI ⓘʳ φ-target) ⁻¹)

    curry-args : Functor Selfᵉ (opE Selfᵒ ⊠ opE Selfᵒ)
    curry-args = (op²F ⊠F (op²F ∘F homʳ unit)) ∘F swapF

    Kⁱ Kᵀ : Functor Selfᵉ Selfᵒ
    Kⁱ = opF (curry₂-target ⊥) ∘F (op-⊠F ∘F curry-args)
    Kᵀ = opF (curry₂-source ⊥) ∘F (op-⊠F ∘F curry-args)

    open Functor (inputF Fⁱ) using () renaming (₁ to inputⁱ₁)
    open Functor (op₂F (curry₂-target ⊥)) using () renaming (₁ to curryⁱ₁)
    open Functor (op₂F (curry₂-source ⊥)) using () renaming (₁ to curryᵀ₁)
    open Functor Fⁱ using () renaming (₀ to Fⁱ₀)
    open Functor SelfEnriched.homᵒᵖFunctor using () renaming (₁ to homᵒ₁)
    open Functor Fᵀ using () renaming (₁ to inputᵀ₁)
    open Functor Kⁱ using () renaming (₁ to Kⁱ₁)
    open Functor Kᵀ using () renaming (₁ to Kᵀ₁)
    open Functor φ-target using () renaming (₁ to φ-target₁)
    open Functor (homʳ unit) using () renaming (₀ to U₀; ₁ to U₁)
    module Curry₂⊥ = Curry₂Source ⊥

    nested-dual : homᵒ₁ {X = Y , Fⁱ₀ X} {Y = W , Fⁱ₀ Z} ∘
        (id ⊗₁ dualᵒ₁ {X = U₀ X} {Y = U₀ Z})
      ≈ curryⁱ₁ {X = Y , U₀ X} {Y = W , U₀ Z}
    nested-dual {Y} {X} {W} {Z} = begin
      ((internal-∘ ∘ σ⇒) ∘
        (homʳ₁ Y W (Fⁱ₀ Z) ⊗₁ homˡ₁ Y (Fⁱ₀ Z) (Fⁱ₀ X))) ∘
        (id ⊗₁ dualᵒ₁)
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ dualᵒ-action ⟩
      ((internal-∘ ∘ σ⇒) ∘
        (homʳ₁ Y W (Fⁱ₀ Z) ⊗₁ homˡ₁ Y (Fⁱ₀ Z) (Fⁱ₀ X))) ∘
        (id ⊗₁ homʳ₁ (U₀ X) (U₀ Z) ⊥)
        ≈⟨ SelfEnriched.whisker-commᵒ Y W (Fⁱ₀ X) (Fⁱ₀ Z) ⟩∘⟨refl ⟩
      (((internal-∘ ∘ σ⇒) ∘
        (homˡ₁ W (Fⁱ₀ Z) (Fⁱ₀ X) ⊗₁ homʳ₁ Y W (Fⁱ₀ X))) ∘ σ⇒) ∘
        (id ⊗₁ homʳ₁ (U₀ X) (U₀ Z) ⊥)
        ≈⟨ pullʳ σ⇒-comm ⟩
      ((internal-∘ ∘ σ⇒) ∘
        (homˡ₁ W (Fⁱ₀ Z) (Fⁱ₀ X) ⊗₁ homʳ₁ Y W (Fⁱ₀ X))) ∘
        ((homʳ₁ (U₀ X) (U₀ Z) ⊥ ⊗₁ id) ∘ σ⇒)
        ≈⟨ center merge₁ʳ ⟩
      (internal-∘ ∘ σ⇒) ∘
        (((homˡ₁ W (Fⁱ₀ Z) (Fⁱ₀ X) ∘ homʳ₁ (U₀ X) (U₀ Z) ⊥) ⊗₁
          homʳ₁ Y W (Fⁱ₀ X)) ∘ σ⇒)
        ≈⟨ center σ⇒-comm ⟩
      internal-∘ ∘
        ((homʳ₁ Y W (Fⁱ₀ X) ⊗₁
          (homˡ₁ W (Fⁱ₀ Z) (Fⁱ₀ X) ∘ homʳ₁ (U₀ X) (U₀ Z) ⊥)) ∘ σ⇒) ∘ σ⇒
        ≈⟨ refl⟩∘⟨ assoc ⟩
      internal-∘ ∘
        (homʳ₁ Y W (Fⁱ₀ X) ⊗₁
          (homˡ₁ W (Fⁱ₀ Z) (Fⁱ₀ X) ∘ homʳ₁ (U₀ X) (U₀ Z) ⊥)) ∘ σ⇒ ∘ σ⇒
        ≈⟨ refl⟩∘⟨ elimʳ commutative ⟩
      internal-∘ ∘
        (homʳ₁ Y W (Fⁱ₀ X) ⊗₁
          (homˡ₁ W (Fⁱ₀ Z) (Fⁱ₀ X) ∘ homʳ₁ (U₀ X) (U₀ Z) ⊥))
        ≈⟨ refl⟩∘⟨ ⟺ identityʳ ⟩⊗⟨refl ⟩
      curryⁱ₁ ∎

    input-action : inputⁱ₁ {X = X , Y} {Y = Z , W} ≈ Kⁱ₁ {X = X , Y} {Y = Z , W}
    input-action = begin
      homᵒ₁ ∘ ((id ⊗₁ (dualᵒ₁ ∘ U₁)) ∘ σ⇒)         ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
      homᵒ₁ ∘ ((id ⊗₁ dualᵒ₁) ∘ ((id ⊗₁ U₁) ∘ σ⇒)) ≈⟨ pullˡ nested-dual ⟩
      curryⁱ₁ ∘ ((id ⊗₁ U₁) ∘ σ⇒)                   ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ identityˡ ⟩∘⟨refl ⟩
      curryⁱ₁ ∘ ((id ⊗₁ (id ∘ U₁)) ∘ σ⇒)            ≈˘⟨ refl⟩∘⟨ identityˡ ⟩
      Kⁱ₁ ∎

    input≃Kⁱ : NaturalIsomorphism (inputF Fⁱ) Kⁱ
    input≃Kⁱ = SelfNaturalᵒ.pointwise-iso idᵢ (begin
      uncurry inputⁱ₁ ∘ (id ⊗₁ id)  ≈⟨ elimʳ ⊗.identity ⟩
      uncurry inputⁱ₁               ≈⟨ uncurry-resp-≈ input-action ⟩
      uncurry Kⁱ₁                   ≈˘⟨ identityˡ ⟩
      id ∘ uncurry Kⁱ₁              ∎)

    curry-action : curryᵀ₁ {X = Y , U₀ X} {Y = W , U₀ Z} ∘
        ((id ⊗₁ U₁ {X = X} {Y = Z}) ∘ σ⇒)
      ≈ Kᵀ₁ {X = X , Y} {Y = Z , W}
    curry-action = begin
      curryᵀ₁ ∘ ((id ⊗₁ U₁) ∘ σ⇒)
        ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ identityˡ ⟩∘⟨refl ⟩
      curryᵀ₁ ∘ ((id ⊗₁ (id ∘ U₁)) ∘ σ⇒)
        ≈˘⟨ refl⟩∘⟨ identityˡ ⟩
      Kᵀ₁ ∎

    curry₂-unit-action : curryᵀ₁ {X = Y , U₀ X} {Y = W , U₀ Z} ∘
        ((id ⊗₁ U₁ {X = X} {Y = Z}) ∘ σ⇒)
      ≈ homʳ₁ (Y ⊗₀ U₀ X) (W ⊗₀ U₀ Z) ⊥ ∘ (⊗-map₁ ∘ ((id ⊗₁ U₁) ∘ σ⇒))
    curry₂-unit-action = pushˡ Curry₂⊥.actionᵒ

    dual-unit-action : inputᵀ₁ {X = X , Y} {Y = Z , W}
      ≈ homʳ₁ (Y ⊗₀ U₀ X) (W ⊗₀ U₀ Z) ⊥ ∘ φ-target₁ {X = X , Y} {Y = Z , W}
    dual-unit-action = dualᵒ-action ⟩∘⟨refl

    dual-tensor-action : inputᵀ₁ {X = X , Y} {Y = Z , W}
      ≈ curryᵀ₁ {X = Y , U₀ X} {Y = W , U₀ Z} ∘ ((id ⊗₁ U₁ {X = X} {Y = Z}) ∘ σ⇒)
    dual-tensor-action {X} {Y} {Z} {W} = begin
      inputᵀ₁
        ≈⟨ dual-unit-action ⟩
      homʳ₁ (Y ⊗₀ U₀ X) (W ⊗₀ U₀ Z) ⊥ ∘ φ-target₁
        ≈⟨ refl⟩∘⟨ assoc ⟩
      homʳ₁ (Y ⊗₀ U₀ X) (W ⊗₀ U₀ Z) ⊥ ∘ (⊗-map₁ ∘ ((id ⊗₁ U₁) ∘ σ⇒))
        ≈˘⟨ curry₂-unit-action ⟩
      curryᵀ₁ ∘ ((id ⊗₁ U₁) ∘ σ⇒) ∎

    tensor-action : inputᵀ₁ {X = X , Y} {Y = Z , W} ≈ Kᵀ₁ {X = X , Y} {Y = Z , W}
    tensor-action = dual-tensor-action ○ curry-action

    tensor≃Kᵀ : NaturalIsomorphism Fᵀ Kᵀ
    tensor≃Kᵀ = SelfNaturalᵒ.pointwise-iso idᵢ (begin
      uncurry inputᵀ₁ ∘ (id ⊗₁ id)  ≈⟨ elimʳ ⊗.identity ⟩
      uncurry inputᵀ₁               ≈⟨ uncurry-resp-≈ tensor-action ⟩
      uncurry Kᵀ₁                   ≈˘⟨ identityˡ ⟩
      id ∘ uncurry Kᵀ₁              ∎)

    Kⁱ≃Kᵀ : NaturalIsomorphism Kⁱ Kᵀ
    Kⁱ≃Kᵀ = ((opNI (curry₂-NI ⊥)) ⁻¹) ⓘʳ (op-⊠F ∘F curry-args)

    Φⁱ≃Φᵀ : NaturalIsomorphism Φⁱ Φᵀ
    Φⁱ≃Φᵀ = (associator-NI ⁻¹) ⓘᵥ
      (homʳ ⊥ ⓘˡ ((tensor≃Kᵀ ⁻¹) ⓘᵥ Kⁱ≃Kᵀ ⓘᵥ input≃Kⁱ))

  abstract
    curry-component : Morphism._≅_.from
        (((tensor≃Kᵀ ⁻¹) ⓘᵥ Kⁱ≃Kᵀ ⓘᵥ input≃Kⁱ) ᵢ[ (X , Y) ])
      ≈ ⌜ curry₂ ⌝
    curry-component = Category.identityˡ (Underlying Selfᵒ) ○
      Category.identityʳ (Underlying Selfᵒ)

  private abstract
    ⌜uncurry-⊗⌝ : Morphism._≅_.from (Φⁱ≃Φᵀ ᵢ[ (X , Y) ])
      ≈ ⌜ _≅_.from (dualᵒ (≅.sym curry₂-iso)) ⌝
    ⌜uncurry-⊗⌝ {X} {Y} = begin
      Morphism._≅_.from (Φⁱ≃Φᵀ ᵢ[ (X , Y) ])
        ≈⟨ Category.identityˡ (Underlying selfEnrichment) ⟩
      Functor.₁ (homʳ ⊥) ∘
        Morphism._≅_.from
          (((tensor≃Kᵀ ⁻¹) ⓘᵥ Kⁱ≃Kᵀ ⓘᵥ input≃Kⁱ) ᵢ[ (X , Y) ])
        ≈⟨ refl⟩∘⟨ curry-component ⟩
      homʳ₁ _ _ ⊥ ∘ ⌜ curry₂ ⌝                    ≈⟨ ⌜homʳ⌝ ⟩
      ⌜ _≅_.from (dualᵒ (≅.sym curry₂-iso)) ⌝     ∎

  private abstract
    ⌜Φ₁⌝ : {F G : Endofunctor Selfᵒ} (η : NaturalIsomorphism F G)
      {g : Functor.₀ G X ⇒ Functor.₀ F X} →
      Morphism._≅_.from (η ᵢ[ X ]) ≈ ⌜ g ⌝ →
      Morphism._≅_.from (Φ₁ η ᵢ[ (X , Y) ]) ≈ ⌜ [ [ id , g ]₁ , id ]₁ ⌝
    ⌜Φ₁⌝ η {g = g} component = begin
      Morphism._≅_.from (Φ₁ η ᵢ[ _ ])
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ component ⟩∘⟨refl ⟩
      homʳ₁ _ _ ⊥ ∘ (homᵒ₁ ∘ ((⌜id⌝ ⊗₁ ⌜ g ⌝) ∘ λ⇐))
        ≈⟨ refl⟩∘⟨ ⌜homᵒᵖ⌝ _ ⟩
      homʳ₁ _ _ ⊥ ∘ ⌜ [ id , g ]₁ ⌝  ≈⟨ ⌜homʳ⌝ ⟩
      ⌜ [ [ id , g ]₁ , id ]₁ ⌝ ∎

  private abstract
    ⌜insert-**⌝ : Morphism._≅_.from (Φ²≃ ᵢ[ (X , Y) ])
      ≈ ⌜ _≅_.from (dualᵒ (homˡ Y **-≅)) ⌝
    ⌜insert-**⌝ {X} {Y} = begin
      homʳ₁ _ _ ⊥ ∘ (homᵒ₁ ∘ ((⌜id⌝ ⊗₁ ⌜ _≅_.to **-≅ ⌝) ∘ λ⇐))
        ≈⟨ refl⟩∘⟨ ⌜homᵒᵖ⌝ _ ⟩
      homʳ₁ _ _ ⊥ ∘ ⌜ [ id , _≅_.to **-≅ ]₁ ⌝  ≈⟨ ⌜homʳ⌝ ⟩
      ⌜ _≅_.from (dualᵒ (homˡ Y **-≅)) ⌝ ∎

  private abstract
    ⌜swap-feedback⌝ : Morphism._≅_.from (F²≃Fᶜ ᵢ[ X ])
      ≈ ⌜ _≅_.to (dualᵒ swap-curry-≅) ⌝
    ⌜swap-feedback⌝ {X} = begin
      Morphism._≅_.from (F²≃Fᶜ ᵢ[ X ])
        ≈⟨ Category.identityʳ (Underlying Selfᵒ) ⟩
      dualᵒ₁ ∘ ⌜ _≅_.from swap-curry-≅ ⌝
        ≈⟨ dualᵒ-action ⟩∘⟨refl ⟩
      homʳ₁ _ _ ⊥ ∘ ⌜ _≅_.from swap-curry-≅ ⌝  ≈⟨ ⌜homʳ⌝ ⟩
      ⌜ _≅_.to (dualᵒ swap-curry-≅) ⌝ ∎

  private abstract
    ⌜swap-curry⌝ : Morphism._≅_.from (Φ²≃Φᶜ ᵢ[ (X , Y) ])
      ≈ ⌜ _≅_.from (dualᵒ (homˡ Y (dualᵒ swap-curry-≅))) ⌝
    ⌜swap-curry⌝ = ⌜Φ₁⌝ F²≃Fᶜ ⌜swap-feedback⌝

  private abstract
    ⌜replace-feedback⌝ : Morphism._≅_.from (Fᶜ≃Fⁱ ᵢ[ X ])
      ≈ ⌜ _≅_.to (dualᵒ (homˡ X ⊥*-≅)) ⌝
    ⌜replace-feedback⌝ {X} = let
      f : ([ X , unit ]₀ *) ⇒ ([ X , ⊥ * ]₀ *)
      f = _≅_.to (dualᵒ (homˡ X ⊥*-≅))
      in begin
      Morphism._≅_.from (Fᶜ≃Fⁱ ᵢ[ X ])          ≈⟨ refl⟩∘⟨ ⌜homˡ⌝ ⟩
      dualᵒ₁ ∘ ⌜ _≅_.from (homˡ X ⊥*-≅) ⌝      ≈⟨ dualᵒ-action ⟩∘⟨refl ⟩
      homʳ₁ _ _ ⊥ ∘ ⌜ _≅_.from (homˡ X ⊥*-≅) ⌝  ≈⟨ ⌜homʳ⌝ ⟩
      ⌜ f ⌝ ∎

  private abstract
    ⌜replace-dual-unit⌝ : Morphism._≅_.from (Φᶜ≃Φⁱ ᵢ[ (X , Y) ])
      ≈ ⌜ _≅_.from (dualᵒ (homˡ Y (dualᵒ (homˡ X ⊥*-≅)))) ⌝
    ⌜replace-dual-unit⌝ = ⌜Φ₁⌝ Fᶜ≃Fⁱ ⌜replace-feedback⌝

  private abstract
    ⌜curry-feedback⌝ : Morphism._≅_.from
        ((Φ²≃Φᶜ ⓘᵥ Φ²≃) ᵢ[ (X , Y) ])
      ≈ ⌜ _≅_.from (dualᵒ (homˡ Y (dualᵒ swap-curry-≅ ∘ᵢ **-≅))) ⌝
    ⌜curry-feedback⌝ {X} {Y} = begin
      Morphism._≅_.from ((Φ²≃Φᶜ ⓘᵥ Φ²≃) ᵢ[ (X , Y) ])
        ≈⟨ refl⟩∘⟨ ⌜swap-curry⌝ ⟩⊗⟨ ⌜insert-**⌝ ⟩∘⟨refl ⟩
      internal-∘ ∘
        (⌜ _≅_.from (dualᵒ (homˡ Y (dualᵒ swap-curry-≅))) ⌝ ⊗₁
          ⌜ _≅_.from (dualᵒ (homˡ Y **-≅)) ⌝) ∘ λ⇐
        ≈⟨ ⌜∘⌝ ⟩
      ⌜ _≅_.from (dualᵒ (homˡ Y (dualᵒ swap-curry-≅))) ∘
        _≅_.from (dualᵒ (homˡ Y **-≅)) ⌝
        ≈⟨ ⌜⌝-resp-≈ curry-feedback-hom ⟩
      ⌜ _≅_.from (dualᵒ (homˡ Y (dualᵒ swap-curry-≅ ∘ᵢ **-≅))) ⌝ ∎

  private abstract
    ⌜feedback⌝ : Morphism._≅_.from
        ((Φᶜ≃Φⁱ ⓘᵥ Φ²≃Φᶜ ⓘᵥ Φ²≃) ᵢ[ (X , Y) ])
      ≈ ⌜ _≅_.from (dualᵒ (homˡ Y feedback⁻)) ⌝
    ⌜feedback⌝ {X} {Y} = begin
      Morphism._≅_.from ((Φᶜ≃Φⁱ ⓘᵥ Φ²≃Φᶜ ⓘᵥ Φ²≃) ᵢ[ (X , Y) ])
        ≈⟨ refl⟩∘⟨ (⌜replace-dual-unit⌝ ⟩⊗⟨ ⌜curry-feedback⌝) ⟩∘⟨refl ⟩
      internal-∘ ∘
        (⌜ _≅_.from (dualᵒ (homˡ Y (dualᵒ (homˡ X ⊥*-≅)))) ⌝ ⊗₁
          ⌜ _≅_.from
            (dualᵒ (homˡ Y (dualᵒ swap-curry-≅ ∘ᵢ **-≅))) ⌝) ∘ λ⇐
        ≈⟨ ⌜∘⌝ ⟩
      ⌜ _≅_.from (dualᵒ (homˡ Y (dualᵒ (homˡ X ⊥*-≅)))) ∘
        _≅_.from (dualᵒ (homˡ Y (dualᵒ swap-curry-≅ ∘ᵢ **-≅))) ⌝
        ≈⟨ ⌜⌝-resp-≈ feedback-hom ⟩
      ⌜ _≅_.from (dualᵒ (homˡ Y feedback⁻)) ⌝ ∎

  private abstract
    ⌜φᵀ⌝ : Morphism._≅_.from
        ((Φⁱ≃Φᵀ ⓘᵥ Φᶜ≃Φⁱ ⓘᵥ Φ²≃Φᶜ ⓘᵥ Φ²≃) ᵢ[ (X , Y) ])
      ≈ ⌜ _≅_.from (dualᵒ φᵀ-≅) ⌝
    ⌜φᵀ⌝ {X} {Y} = begin
      Morphism._≅_.from
        ((Φⁱ≃Φᵀ ⓘᵥ Φᶜ≃Φⁱ ⓘᵥ Φ²≃Φᶜ ⓘᵥ Φ²≃) ᵢ[ (X , Y) ])
        ≈⟨ refl⟩∘⟨ (⌜uncurry-⊗⌝ ⟩⊗⟨ ⌜feedback⌝) ⟩∘⟨refl ⟩
      internal-∘ ∘
        (⌜ _≅_.from (dualᵒ (≅.sym curry₂-iso)) ⌝ ⊗₁
          ⌜ _≅_.from (dualᵒ (homˡ Y feedback⁻)) ⌝) ∘ λ⇐
        ≈⟨ ⌜∘⌝ ⟩
      ⌜ _≅_.from (dualᵒ (≅.sym curry₂-iso)) ∘
        _≅_.from (dualᵒ (homˡ Y feedback⁻)) ⌝
        ≈⟨ ⌜⌝-resp-≈ (dual-∘ (homˡ Y feedback⁻) (≅.sym curry₂-iso)) ⟩
      ⌜ _≅_.from (dualᵒ φᵀ-≅) ⌝ ∎

  private abstract
    ⌜remove-**⌝ : Morphism._≅_.from (Φᵀ≃φ ᵢ[ (X , Y) ])
      ≈ ⌜ _≅_.to **-≅ ⌝
    ⌜remove-**⌝ = Category.identityˡ (Underlying selfEnrichment)

  abstract
    -- Hajgató--Hasegawa 2013, Lemma 3.2.
    φ-NI : NaturalIsomorphism φ-source φ-target
    φ-NI = Φᵀ≃φ ⓘᵥ Φⁱ≃Φᵀ ⓘᵥ Φᶜ≃Φⁱ ⓘᵥ Φ²≃Φᶜ ⓘᵥ Φ²≃

  φ-≅ : ([ Y , ⊥ ⊗₀ X ]₀ *) ≅ Y ⊗₀ [ X , unit ]₀
  φ-≅ = ≅.sym **-≅ ∘ᵢ dualᵒ φᵀ-≅

  abstract
    ⌜φ⌝ : Morphism._≅_.from (φ-NI ᵢ[ (X , Y) ]) ≈ ⌜ _≅_.from φ-≅ ⌝
    ⌜φ⌝ {X} {Y} = begin
      Morphism._≅_.from (φ-NI ᵢ[ (X , Y) ])
        ≈⟨ refl⟩∘⟨ (⌜remove-**⌝ ⟩⊗⟨ ⌜φᵀ⌝) ⟩∘⟨refl ⟩
      internal-∘ ∘ (⌜ _≅_.to **-≅ ⌝ ⊗₁ ⌜ _≅_.from (dualᵒ φᵀ-≅) ⌝) ∘ λ⇐
        ≈⟨ ⌜∘⌝ ⟩
      ⌜ _≅_.from φ-≅ ⌝ ∎
