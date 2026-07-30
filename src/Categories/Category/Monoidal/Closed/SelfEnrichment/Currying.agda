{-# OPTIONS --without-K --safe --lossy-unification #-}

-- --lossy-unification keeps enriched functor composition below a minute.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Enriched naturality of double currying follows Kelly,
-- "Basic Concepts of Enriched Category Theory", Section 1.11.

module Categories.Category.Monoidal.Closed.SelfEnrichment.Currying
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
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Tensor S Cl
open import Categories.Category.Monoidal.Closed.SelfEnrichment.Adjunction S Cl using (evalᵀ)
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M
  using ( assoc-to-coherence; α⇒-id⊗-commute; α⇒-⊗id-commute
        ; α⇐-id⊗-commute; α⇐-⊗id-commute )
open import Categories.Category.Monoidal.Symmetric.Properties S using (braiding-selfInverse)
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
open SelfEnriched using (homHelper; homFunctor; homˡ₁; homʳ₁)
  renaming (homʳFunctor to homʳ)

open import Categories.Category.Monoidal.Interchange.Symmetric S
  using (swapInner-braidingʳ)

private
  i⇒ = swapInner.from

  variable
    A B C : Obj -- tensor arguments
    W X Y : Obj -- source, parameter, and target roles

ev⊗ˡ : (A B X : Obj) → [ A , B ]₀ ⊗₀ (A ⊗₀ X) ⇒ B ⊗₀ X
ev⊗ˡ A B X = (eval ⊗₁ id) ∘ α⇐

ev⊗ʳ : (A X Y : Obj) → [ X , Y ]₀ ⊗₀ (A ⊗₀ X) ⇒ A ⊗₀ Y
ev⊗ʳ A X Y = (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐

_⊗₁ˡ_ : (A B X : Obj) → [ A , B ]₀ ⇒ [ A ⊗₀ X , B ⊗₀ X ]₀
A ⊗₁ˡ B = λ X → curry (ev⊗ˡ A B X)

_⊗₁ʳ_ : (A X Y : Obj) → [ X , Y ]₀ ⇒ [ A ⊗₀ X , A ⊗₀ Y ]₀
A ⊗₁ʳ X = λ Y → curry (ev⊗ʳ A X Y)

tensorˡ-eval : (A B X : Obj) → uncurry ((A ⊗₁ˡ B) X) ≈ ev⊗ˡ A B X
tensorˡ-eval A B X = eval-curry

tensorʳ-eval : (A X Y : Obj) → uncurry ((A ⊗₁ʳ X) Y) ≈ ev⊗ʳ A X Y
tensorʳ-eval A X Y = eval-curry

tensorʳ-action : (A X Y : Obj) →
  Functor.₁ (A ⊗F-) {X = X} {Y = Y} ≈ (A ⊗₁ʳ X) Y
tensorʳ-action A X Y = uncurry-injective (⊗F-eval ○ ⟺ eval-curry)

private

  tensorˡ-identity-eval : (A B X : Obj) →
    ⊗-eval {A} {B} {X} {X} ∘ ((id { [ A , B ]₀ } ⊗₁ ⌜id⌝) ⊗₁ id)
    ≈ (eval ⊗₁ λ⇒ {X}) ∘ i⇒
  tensorˡ-identity-eval A B X = begin
    ⊗-eval ∘ ((id ⊗₁ ⌜id⌝) ⊗₁ id)    ≈⟨ ⊗-eval-map id ⌜ id ⌝ ⟩
    (uncurry id ⊗₁ uncurry ⌜ id ⌝) ∘ i⇒  ≈⟨ (elimʳ ⊗.identity ⟩⊗⟨ eval-⌜id⌝) ⟩∘⟨refl ⟩
    (eval ⊗₁ λ⇒) ∘ i⇒                      ∎

  interchange-unit : (A B X : Obj) → ((eval {A} {B} ⊗₁ λ⇒ {X}) ∘ i⇒) ∘ (ρ⇐ ⊗₁ id)
    ≈ (eval ⊗₁ id) ∘ α⇐
  interchange-unit A B X = begin
    ((eval ⊗₁ λ⇒) ∘ i⇒) ∘ (ρ⇐ ⊗₁ id)
      ≈⟨ assoc²βε ⟩
    (eval ⊗₁ λ⇒) ∘ α⇐ ∘
      (((id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒) ∘ (ρ⇐ ⊗₁ id))
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ pullʳ triangle-inv′) ⟩
    (eval ⊗₁ λ⇒) ∘ α⇐ ∘
      (id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ (id ⊗₁ λ⇐)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₂ˡ ⟩
    (eval ⊗₁ λ⇒) ∘ α⇐ ∘
      (id ⊗₁ ((α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ λ⇐))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ unit-swap) ⟩
    (eval ⊗₁ λ⇒) ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ λ⇐))
      ≈˘⟨ refl⟩∘⟨ α⇐-id⊗-commute ⟩
    (eval ⊗₁ λ⇒) ∘ (id ⊗₁ λ⇐) ∘ α⇐
      ≈⟨ pullˡ (⟺ ⊗-distrib-over-∘) ⟩
    ((eval ∘ id) ⊗₁ (λ⇒ ∘ λ⇐)) ∘ α⇐
      ≈⟨ identityʳ ⟩⊗⟨ unitorˡ.isoʳ ⟩∘⟨refl ⟩
    (eval ⊗₁ id) ∘ α⇐ ∎
    where
    unit-swap : (α⇒ ∘ (σ⇒ {unit} {A} ⊗₁ id {X}) ∘ α⇐) ∘ λ⇐ ≈ id ⊗₁ λ⇐
    unit-swap = begin
      (α⇒ ∘ ((σ⇒ ⊗₁ id) ∘ α⇐)) ∘ λ⇐
        ≈⟨ pull-last coherence-inv₁ ⟩
      α⇒ ∘ ((σ⇒ ⊗₁ id) ∘ (λ⇐ ⊗₁ id))               ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
      α⇒ ∘ ((σ⇒ ∘ λ⇐) ⊗₁ id)                       ≈⟨ refl⟩∘⟨ (⟺ braiding-selfInverse ⟩∘⟨refl) ⟩⊗⟨refl ⟩
      α⇒ ∘ ((σ⇐ ∘ λ⇐) ⊗₁ id)                       ≈⟨ refl⟩∘⟨ braiding-coherence-inv ⟩⊗⟨refl ⟩
      α⇒ ∘ (ρ⇐ ⊗₁ id)                                   ≈⟨ triangle-inv′ ⟩
      id ⊗₁ λ⇐                                                ∎

  tensorˡ-unit-eval : (A B X : Obj) →
    ⊗-eval {A} {B} {X} {X} ∘
      (((id { [ A , B ]₀ } ⊗₁ ⌜ id {X} ⌝) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id))
    ≈ ev⊗ˡ A B X
  tensorˡ-unit-eval A B X = begin
    ⊗-eval ∘ (((id ⊗₁ ⌜id⌝) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id))
      ≈⟨ pullˡ (tensorˡ-identity-eval A B X) ⟩
    ((eval ⊗₁ λ⇒) ∘ i⇒) ∘ (ρ⇐ ⊗₁ id)  ≈⟨ interchange-unit A B X ⟩
    ev⊗ˡ A B X ∎

  tensorˡ-input : (A B X : Obj) →
    (σ⇒ { [ X , X ]₀ } { [ A , B ]₀ } ∘ ((⌜ id {X} ⌝ ⊗₁ id) ∘ λ⇐)) ⊗₁ id {A ⊗₀ X}
    ≈ ((id ⊗₁ ⌜id⌝) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)
  tensorˡ-input A B X = begin
    (σ⇒ ∘ ((⌜id⌝ ⊗₁ id) ∘ λ⇐)) ⊗₁ id
      ≈⟨ split₁ˡ ⟩
    (σ⇒ ⊗₁ id) ∘ (((⌜id⌝ ⊗₁ id) ∘ λ⇐) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    (σ⇒ ⊗₁ id) ∘ (((⌜id⌝ ⊗₁ id) ⊗₁ id) ∘ (λ⇐ ⊗₁ id))
      ≈⟨ extendʳ (parallel σ⇒-comm id-comm) ⟩
    ((id ⊗₁ ⌜id⌝) ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ∘ (λ⇐ ⊗₁ id))
      ≈⟨ refl⟩∘⟨ ((⟺ braiding-selfInverse ⟩⊗⟨refl) ⟩∘⟨refl) ⟩
    ((id ⊗₁ ⌜id⌝) ⊗₁ id) ∘ ((σ⇐ ⊗₁ id) ∘ (λ⇐ ⊗₁ id))
      ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
    ((id ⊗₁ ⌜id⌝) ⊗₁ id) ∘ ((σ⇐ ∘ λ⇐) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ (braiding-coherence-inv ⟩⊗⟨refl) ⟩
    ((id ⊗₁ ⌜id⌝) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id) ∎

tensorˡ-action-eval : (A B X : Obj) →
  ⊗-eval {A} {B} {X} {X} ∘ ((σ⇒ ∘ ((⌜ id {X} ⌝ ⊗₁ id) ∘ λ⇐)) ⊗₁ id)
  ≈ ev⊗ˡ A B X
tensorˡ-action-eval A B X =
  (refl⟩∘⟨ tensorˡ-input A B X) ○ tensorˡ-unit-eval A B X

tensorˡ-action : (A B X : Obj) →
  Functor.₁ (appʳ -⊗F- X) {X = A} {Y = B} ≈ (A ⊗₁ˡ B) X
tensorˡ-action A B X =
  ⟺ curry-∘ ○ curry-resp-≈ (tensorˡ-action-eval A B X)

private

  evaluate-in-parallel : (f : A ⊗₀ B ⇒ C) (g : X ⇒ Y) →
    (f ⊗₁ id) ∘ ((id ⊗₁ id) ⊗₁ g) ≈ f ⊗₁ g
  evaluate-in-parallel f g = begin
    (f ⊗₁ id) ∘ ((id ⊗₁ id) ⊗₁ g)  ≈˘⟨ ⊗-distrib-over-∘ ⟩
    (f ∘ (id ⊗₁ id)) ⊗₁ (id ∘ g)    ≈⟨ (refl⟩∘⟨ ⊗.identity) ⟩⊗⟨ identityˡ ⟩
    (f ∘ id) ⊗₁ g                    ≈⟨ identityʳ ⟩⊗⟨refl ⟩
    f ⊗₁ g                            ∎

  eval⊗ˡʳ : (A B X Y : Obj) →
    uncurry ((A ⊗₁ˡ B) Y) ∘ (id ⊗₁ uncurry ((A ⊗₁ʳ X) Y)) ∘ α⇒
    ≈ ⊗-eval {A} {B} {X} {Y}
  eval⊗ˡʳ A B X Y = begin
    uncurry ((A ⊗₁ˡ B) Y) ∘ (id ⊗₁ uncurry ((A ⊗₁ʳ X) Y)) ∘ α⇒
      ≈⟨ eval-curry ⟩∘⟨ (refl⟩⊗⟨ eval-curry) ⟩∘⟨refl ⟩
    ((eval ⊗₁ id) ∘ α⇐) ∘
      (id ⊗₁ ((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒
      ≈⟨ assoc ⟩
    (eval ⊗₁ id) ∘ α⇐ ∘
      (id ⊗₁ ((id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ eval)) ∘
      (id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ extendʳ assoc-commute-to ⟩
    (eval ⊗₁ id) ∘ ((id ⊗₁ id) ⊗₁ eval) ∘ α⇐ ∘
      (id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒
      ≈⟨ pullˡ (evaluate-in-parallel eval eval) ⟩
    ⊗-eval ∎

  tensor-evalᵀ : (A X Y : Obj) → σ⇒ {A} {Y} ∘ uncurry ((A ⊗₁ʳ X) Y)
    ≈ uncurry ((X ⊗₁ˡ Y) A) ∘ (id { [ X , Y ]₀ } ⊗₁ σ⇒ {A} {X})
  tensor-evalᵀ A X Y = begin
    σ⇒ ∘ uncurry ((A ⊗₁ʳ X) Y)                         ≈⟨ refl⟩∘⟨ eval-curry ⟩
    σ⇒ ∘ ev⊗ʳ A X Y                                    ≈⟨ evalᵀ A X Y ⟩
    (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒)                    ≈⟨ pullˡ (⟺ eval-curry) ⟩
    uncurry ((X ⊗₁ˡ Y) A) ∘ (id ⊗₁ σ⇒)                 ∎

  tensor-evalᵀ⁻¹ : (A B X : Obj) → σ⇒ {B} {X} ∘ uncurry ((A ⊗₁ˡ B) X)
    ≈ uncurry ((X ⊗₁ʳ A) B) ∘ (id { [ A , B ]₀ } ⊗₁ σ⇒ {A} {X})
  tensor-evalᵀ⁻¹ A B X =
    switch-tofromʳ (idᵢ ⊗ᵢ braided-iso)
      (assoc ○ ⟺ (switch-tofromˡ braided-iso (tensor-evalᵀ X A B)))

  tensor-eval-rotate : (A X Y : Obj) → uncurry ((A ⊗₁ʳ X) Y)
    ≈ σ⇒ {Y} {A} ∘ uncurry ((X ⊗₁ˡ Y) A) ∘ (id { [ X , Y ]₀ } ⊗₁ σ⇒ {A} {X})
  tensor-eval-rotate A X Y = switch-tofromˡ braided-iso (tensor-evalᵀ A X Y)

  evaluations-commute : (A B X Y : Obj) → σ⇒ {Y} {B} ∘
      (eval {X} {Y} ⊗₁ eval {A} {B}) ∘
      σ⇒ { [ A , B ]₀ ⊗₀ A} { [ X , Y ]₀ ⊗₀ X}
    ≈ eval {A} {B} ⊗₁ eval {X} {Y}
  evaluations-commute A B X Y = begin
    σ⇒ ∘ (eval ⊗₁ eval) ∘ σ⇒  ≈⟨ refl⟩∘⟨ ⟺ σ⇒-comm ⟩
    σ⇒ ∘ σ⇒ ∘ (eval ⊗₁ eval)  ≈⟨ pullˡ commutative ⟩
    id ∘ (eval ⊗₁ eval)             ≈⟨ identityˡ ⟩
    eval ⊗₁ eval                        ∎

  parallel-evaluation-symmetric : (A B X Y : Obj) →
    σ⇒ {Y} {B} ∘ ⊗-eval {X} {Y} {A} {B} ∘
      (σ⇒ { [ A , B ]₀} { [ X , Y ]₀} ⊗₁ σ⇒ {A} {X}) ≈ ⊗-eval
  parallel-evaluation-symmetric A B X Y = begin
    σ⇒ ∘ ⊗-eval ∘ (σ⇒ ⊗₁ σ⇒)      ≈⟨ refl⟩∘⟨ pullʳ (⟺ swapInner-braidingʳ) ⟩
    σ⇒ ∘ (eval ⊗₁ eval) ∘ σ⇒ ∘ i⇒  ≈⟨ assoc²εβ ⟩
    (σ⇒ ∘ (eval ⊗₁ eval) ∘ σ⇒) ∘ i⇒  ≈⟨ evaluations-commute A B X Y ⟩∘⟨refl ⟩
    (eval ⊗₁ eval) ∘ i⇒               ∎

  transpose-inner-evaluation : (A B X Y : Obj) →
    (id { [ X , Y ]₀ } ⊗₁ σ⇒ {B} {X}) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X))
    ≈ (id ⊗₁ uncurry ((X ⊗₁ʳ A) B)) ∘ (id ⊗₁ (id ⊗₁ σ⇒ {A} {X}))
  transpose-inner-evaluation A B X Y = begin
    (id ⊗₁ σ⇒) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X))  ≈⟨ merge₂ˡ ⟩
    id ⊗₁ (σ⇒ ∘ uncurry ((A ⊗₁ˡ B) X))                 ≈⟨ refl⟩⊗⟨ tensor-evalᵀ⁻¹ A B X ⟩
    id ⊗₁ (uncurry ((X ⊗₁ʳ A) B) ∘ (id ⊗₁ σ⇒))       ≈⟨ split₂ˡ ⟩
    (id ⊗₁ uncurry ((X ⊗₁ʳ A) B)) ∘ (id ⊗₁ (id ⊗₁ σ⇒))       ∎

  parallel-input-braids : (A B X Y : Obj) →
    (id { [ X , Y ]₀ } ⊗₁ (id { [ A , B ]₀ } ⊗₁ σ⇒ {A} {X})) ∘ α⇒ ∘
      (σ⇒ { [ A , B ]₀} { [ X , Y ]₀} ⊗₁ id {A ⊗₀ X}) ≈ α⇒ ∘ (σ⇒ ⊗₁ σ⇒)
  parallel-input-braids A B X Y = begin
    (id ⊗₁ (id ⊗₁ σ⇒)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)  ≈⟨ pullˡ (⟺ α⇒-id⊗-commute) ⟩
    (α⇒ ∘ (id ⊗₁ σ⇒)) ∘ (σ⇒ ⊗₁ id)            ≈⟨ assoc ⟩
    α⇒ ∘ (id ⊗₁ σ⇒) ∘ (σ⇒ ⊗₁ id)              ≈˘⟨ refl⟩∘⟨ serialize₂₁ ⟩
    α⇒ ∘ (σ⇒ ⊗₁ σ⇒)                                   ∎

  transpose-sequential-evaluation : (A B X Y : Obj) →
    (id { [ X , Y ]₀ } ⊗₁ σ⇒ {B} {X}) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘
      α⇒ ∘ (σ⇒ ⊗₁ id) ≈ (id ⊗₁ uncurry ((X ⊗₁ʳ A) B)) ∘ α⇒ ∘ (σ⇒ ⊗₁ σ⇒)
  transpose-sequential-evaluation A B X Y = begin
    (id ⊗₁ σ⇒) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈⟨ sym-assoc ⟩
    ((id ⊗₁ σ⇒) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X))) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))
      ≈⟨ transpose-inner-evaluation A B X Y ⟩∘⟨refl ⟩
    ((id ⊗₁ uncurry ((X ⊗₁ʳ A) B)) ∘ (id ⊗₁ (id ⊗₁ σ⇒))) ∘
      (α⇒ ∘ (σ⇒ ⊗₁ id))
      ≈⟨ assoc ⟩
    (id ⊗₁ uncurry ((X ⊗₁ʳ A) B)) ∘ (id ⊗₁ (id ⊗₁ σ⇒)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ parallel-input-braids A B X Y ⟩
    (id ⊗₁ uncurry ((X ⊗₁ʳ A) B)) ∘ α⇒ ∘ (σ⇒ ⊗₁ σ⇒) ∎

  swapped-sequential-evaluation : (A B X Y : Obj) →
    uncurry ((X ⊗₁ˡ Y) B) ∘ (id ⊗₁ σ⇒) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘
      α⇒ ∘ (σ⇒ ⊗₁ id) ≈ ⊗-eval {X} {Y} {A} {B} ∘ (σ⇒ ⊗₁ σ⇒)
  swapped-sequential-evaluation A B X Y = begin
    uncurry ((X ⊗₁ˡ Y) B) ∘ (id ⊗₁ σ⇒) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘
      α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ transpose-sequential-evaluation A B X Y ⟩
    uncurry ((X ⊗₁ˡ Y) B) ∘ (id ⊗₁ uncurry ((X ⊗₁ʳ A) B)) ∘ α⇒ ∘
      (σ⇒ ⊗₁ σ⇒)
      ≈⟨ assoc²εβ ⟩
    (uncurry ((X ⊗₁ˡ Y) B) ∘ (id ⊗₁ uncurry ((X ⊗₁ʳ A) B)) ∘ α⇒) ∘
      (σ⇒ ⊗₁ σ⇒)
      ≈⟨ eval⊗ˡʳ X Y A B ⟩∘⟨refl ⟩
    ⊗-eval ∘ (σ⇒ ⊗₁ σ⇒) ∎

  eval⊗ʳˡ : (A B X Y : Obj) → uncurry ((B ⊗₁ʳ X) Y) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘
      α⇒ ∘ (σ⇒ ⊗₁ id) ≈ ⊗-eval {A} {B} {X} {Y}
  eval⊗ʳˡ A B X Y = begin
    uncurry ((B ⊗₁ʳ X) Y) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈⟨ tensor-eval-rotate B X Y ⟩∘⟨refl ⟩
    (σ⇒ ∘ uncurry ((X ⊗₁ˡ Y) B) ∘ (id ⊗₁ σ⇒)) ∘
      (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈⟨ assoc²βε ⟩
    σ⇒ ∘ uncurry ((X ⊗₁ˡ Y) B) ∘ (id ⊗₁ σ⇒) ∘
      (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ swapped-sequential-evaluation A B X Y ⟩
    σ⇒ ∘ ⊗-eval ∘ (σ⇒ ⊗₁ σ⇒)  ≈⟨ parallel-evaluation-symmetric A B X Y ⟩
    ⊗-eval ∎

  tensor-actions : (A B X Y : Obj) →
    internal-∘ ∘ (((A ⊗₁ˡ B) Y) ⊗₁ ((A ⊗₁ʳ X) Y)) ≈ ⊗-map₁
  tensor-actions A B X Y = begin
    internal-∘ ∘ (((A ⊗₁ˡ B) Y) ⊗₁ ((A ⊗₁ʳ X) Y))
      ≈⟨ internal-∘-curry′ ((A ⊗₁ˡ B) Y) ((A ⊗₁ʳ X) Y) ⟩
    curry (uncurry ((A ⊗₁ˡ B) Y) ∘ (id ⊗₁ uncurry ((A ⊗₁ʳ X) Y)) ∘ α⇒)
      ≈⟨ curry-resp-≈ (eval⊗ˡʳ A B X Y) ⟩
    ⊗-map₁ ∎

  tensor-actions-commute : (A B X Y : Obj) →
    internal-∘ ∘ (((A ⊗₁ˡ B) Y) ⊗₁ ((A ⊗₁ʳ X) Y))
    ≈ (internal-∘ ∘ (((B ⊗₁ʳ X) Y) ⊗₁ ((A ⊗₁ˡ B) X))) ∘ σ⇒
  tensor-actions-commute A B X Y = begin
    internal-∘ ∘ (((A ⊗₁ˡ B) Y) ⊗₁ ((A ⊗₁ʳ X) Y))
      ≈⟨ internal-∘-curry′ ((A ⊗₁ˡ B) Y) ((A ⊗₁ʳ X) Y) ⟩
    curry (uncurry ((A ⊗₁ˡ B) Y) ∘ (id ⊗₁ uncurry ((A ⊗₁ʳ X) Y)) ∘ α⇒)
      ≈⟨ curry-resp-≈ (eval⊗ˡʳ A B X Y) ⟩
    ⊗-map₁
      ≈˘⟨ curry-resp-≈ (eval⊗ʳˡ A B X Y) ⟩
    curry (uncurry ((B ⊗₁ʳ X) Y) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘
      α⇒ ∘ (σ⇒ ⊗₁ id))
      ≈⟨ curry-resp-≈ assoc²εβ ⟩
    curry ((uncurry ((B ⊗₁ʳ X) Y) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘ α⇒) ∘
      (σ⇒ ⊗₁ id))
      ≈⟨ curry-∘ ⟩
    curry (uncurry ((B ⊗₁ʳ X) Y) ∘ (id ⊗₁ uncurry ((A ⊗₁ˡ B) X)) ∘ α⇒) ∘ σ⇒
      ≈˘⟨ internal-∘-curry′ ((B ⊗₁ʳ X) Y) ((A ⊗₁ˡ B) X) ⟩∘⟨refl ⟩
    (internal-∘ ∘ (((B ⊗₁ʳ X) Y) ⊗₁ ((A ⊗₁ˡ B) X))) ∘ σ⇒ ∎

  module Tensorˡ (X : Obj) = Functor (appʳ -⊗F- X)
  module Tensorʳ (A : Obj) = Functor (A ⊗F-)

  tensor-commute : (A B X Y : Obj) →
    internal-∘ ∘ (Tensorˡ.₁ Y ⊗₁ Tensorʳ.₁ A)
    ≈ (internal-∘ ∘ (Tensorʳ.₁ B ⊗₁ Tensorˡ.₁ X)) ∘ σ⇒
  tensor-commute A B X Y = begin
    internal-∘ ∘ (Tensorˡ.₁ Y ⊗₁ Tensorʳ.₁ A)
      ≈⟨ refl⟩∘⟨ tensorˡ-action A B Y ⟩⊗⟨ tensorʳ-action A X Y ⟩
    internal-∘ ∘ (((A ⊗₁ˡ B) Y) ⊗₁ ((A ⊗₁ʳ X) Y))
      ≈⟨ tensor-actions-commute A B X Y ⟩
    (internal-∘ ∘ (((B ⊗₁ʳ X) Y) ⊗₁ ((A ⊗₁ˡ B) X))) ∘ σ⇒
      ≈˘⟨ (refl⟩∘⟨ (tensorʳ-action B X Y ⟩⊗⟨ tensorˡ-action A B X)) ⟩∘⟨refl ⟩
    (internal-∘ ∘ (Tensorʳ.₁ B ⊗₁ Tensorˡ.₁ X)) ∘ σ⇒ ∎

tensorHelper : BifunctorHelper selfEnrichment selfEnrichment selfEnrichment
tensorHelper = record
  { map₀ = _⊗₀_
  ; mapˡ = λ A B X → Tensorˡ.₁ X
  ; mapʳ = λ A X Y → Tensorʳ.₁ A
  ; identityˡ = λ A X → Tensorˡ.identity X
  ; identityʳ = λ A X → Tensorʳ.identity A
  ; homomorphismˡ = λ A B C X → Tensorˡ.homomorphism X
  ; homomorphismʳ = λ A X Y Z → Tensorʳ.homomorphism A
  ; commute = tensor-commute
  }

tensor-diagonal : FromHelper.diagonal tensorHelper {A₁ = A} {A₂ = B} {B₁ = X} {B₂ = Y}
  ≈ ⊗-map₁ {A} {B} {X} {Y}
tensor-diagonal {A} {B} {X} {Y} = begin
  FromHelper.diagonal tensorHelper
    ≈⟨ refl⟩∘⟨ tensorˡ-action A B Y ⟩⊗⟨ tensorʳ-action A X Y ⟩
  internal-∘ ∘ (((A ⊗₁ˡ B) Y) ⊗₁ ((A ⊗₁ʳ X) Y))  ≈⟨ tensor-actions A B X Y ⟩
  ⊗-map₁ ∎
