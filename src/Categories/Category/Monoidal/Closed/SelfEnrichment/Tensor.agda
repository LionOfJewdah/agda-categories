{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Definitions)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Interchange using (HasInterchange)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- The canonical enriched tensor functor of a symmetric monoidal closed category.

module Categories.Category.Monoidal.Closed.SelfEnrichment.Tensor
  {o ℓ e} {𝒱 : Category o ℓ e} {M : Monoidal 𝒱}
  (S : Symmetric M) (Cl : Closed M) where

open import Data.Product using (_,_)

import Categories.Enriched.Category as Enriched
import Categories.Enriched.Category.Opposite as EnrichedOpposite
import Categories.Category.Construction.Core 𝒱 as Core

open Category 𝒱
open Core.Shorthands using (idᵢ)
open Definitions 𝒱 using (CommutativeSquare)
open Monoidal M
open Closed Cl using ([_,_]₀; [_,_]₁)
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Closed.Currying Cl using (uncurry²-∘)
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M using (λ⇒-assoc; λ⇐-assoc)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Bifunctor S
  using (BifunctorHelper; bifunctorHelper; appˡ; module FromHelper)
open import Categories.Enriched.Category M using (_[_,_])
open import Categories.Enriched.Functor M using (Functor; Endofunctor)
open import Categories.Enriched.Functor.Opposite S using (opF)
open import Categories.Enriched.NaturalTransformation M using (NaturalTransformation; NTHelper)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism; niHelper)
open import Categories.Morphism 𝒱 using (_≅_; Iso)
open import Categories.Morphism.Reasoning 𝒱
open Shorthands
open Symmetric S using (braided; commutative; hexagon₁)
open import Categories.Category.Monoidal.Braided.Properties braided
  using (braiding-coherence-inv; braiding-coherence-inv′; braiding-coherence-σ′)
open import Categories.Category.Monoidal.Symmetric.Properties S
  using (braiding-selfInverse) renaming (module Shorthands to BraidShorthands)
open BraidShorthands

open import Categories.Category.Monoidal.Interchange.Braided braided
  using (module swapInner) renaming (hasInterchange to interchange)
open import Categories.Enriched.Category.TensorProduct interchange using (_⊠_)
open HasInterchange interchange
  using ()
  renaming ( natural to interchange-natural
           ; assoc to interchange-assoc
           ; unitˡ to interchange-unitˡ
           )

open import Categories.Category.Monoidal.Closed.SelfEnrichment S Cl

private
  i⇒ = swapInner.from

-- Enriched profunctors valued in the canonical self-enrichment.
module SelfTensor where
  private
    module Self² = Enriched.Category (selfEnrichment ⊠ selfEnrichment)
    variable
      A B C : Obj -- closed arguments
      W X Y Z : Obj -- source, tensor, comparison, and codomain roles

  ⊗-eval : ([ A , B ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ (A ⊗₀ X) ⇒ B ⊗₀ Y
  ⊗-eval = (eval ⊗₁ eval) ∘ i⇒

  -- Tensoring two internal maps evaluates them in parallel.
  ⊗-map₁ : [ A , B ]₀ ⊗₀ [ X , Y ]₀ ⇒ [ A ⊗₀ X , B ⊗₀ Y ]₀
  ⊗-map₁ = curry ⊗-eval

  abstract
    ⊗-eval-map : (f : W ⇒ [ A , B ]₀) (g : Z ⇒ [ X , Y ]₀) →
      ⊗-eval ∘ ((f ⊗₁ g) ⊗₁ id) ≈ (uncurry f ⊗₁ uncurry g) ∘ i⇒
    ⊗-eval-map f g = begin
      ⊗-eval ∘ ((f ⊗₁ g) ⊗₁ id)                       ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity ⟩
      ⊗-eval ∘ ((f ⊗₁ g) ⊗₁ (id ⊗₁ id))               ≈⟨ pullʳ interchange-natural ⟩
      (eval ⊗₁ eval) ∘ ((f ⊗₁ id) ⊗₁ (g ⊗₁ id)) ∘ i⇒  ≈⟨ pullˡ (⟺ ⊗.homomorphism) ⟩
      (uncurry f ⊗₁ uncurry g) ∘ i⇒                   ∎

    ⊗-eval-mapˡ : (g : Z ⇒ [ X , Y ]₀) →
      ⊗-eval ∘ ((id { [ A , B ]₀ } ⊗₁ g) ⊗₁ id) ≈ (eval ⊗₁ uncurry g) ∘ i⇒
    ⊗-eval-mapˡ g = begin
      ⊗-eval ∘ ((id ⊗₁ g) ⊗₁ id)        ≈⟨ ⊗-eval-map id g ⟩
      (uncurry id ⊗₁ uncurry g) ∘ i⇒    ≈⟨ elimʳ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
      (eval ⊗₁ uncurry g) ∘ i⇒          ∎

  private abstract
    ⊗-map₁-id : ⊗-map₁ {A = A} {B = A} {X = X} {Y = X} ∘ ((⌜id⌝ ⊗₁ ⌜id⌝) ∘ λ⇐)
                ≈ ⌜id⌝ {A ⊗₀ X}
    ⊗-map₁-id = uncurry-injective (begin
      uncurry (⊗-map₁ ∘ ((⌜id⌝ ⊗₁ ⌜id⌝) ∘ λ⇐))                      ≈⟨ uncurry-∘ ⟩
      uncurry ⊗-map₁ ∘ (((⌜id⌝ ⊗₁ ⌜id⌝) ∘ λ⇐) ⊗₁ id)                ≈⟨ eval-curry ⟩∘⟨refl ⟩
      ((eval ⊗₁ eval) ∘ i⇒) ∘ (((⌜id⌝ ⊗₁ ⌜id⌝) ∘ λ⇐) ⊗₁ id)         ≈⟨ pushʳ split₁ˡ ⟩
      (((eval ⊗₁ eval) ∘ i⇒) ∘ ((⌜id⌝ ⊗₁ ⌜id⌝) ⊗₁ id)) ∘ (λ⇐ ⊗₁ id)
        ≈˘⟨ (refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
      (((eval ⊗₁ eval) ∘ i⇒) ∘ ((⌜id⌝ ⊗₁ ⌜id⌝) ⊗₁ (id ⊗₁ id))) ∘ (λ⇐ ⊗₁ id)
        ≈⟨ pullʳ interchange-natural ⟩∘⟨refl ⟩
      ((eval ⊗₁ eval) ∘ (((⌜id⌝ ⊗₁ id) ⊗₁ (⌜id⌝ ⊗₁ id)) ∘ i⇒)) ∘ (λ⇐ ⊗₁ id)
        ≈⟨ pullˡ (⟺ ⊗.homomorphism) ⟩∘⟨refl ⟩
      (((eval ∘ (⌜id⌝ ⊗₁ id)) ⊗₁ (eval ∘ (⌜id⌝ ⊗₁ id))) ∘ i⇒) ∘ (λ⇐ ⊗₁ id)
        ≈⟨ (eval-⌜id⌝ ⟩⊗⟨ eval-⌜id⌝ ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((λ⇒ ⊗₁ λ⇒) ∘ i⇒) ∘ (λ⇐ ⊗₁ id)                                ≈⟨ assoc ⟩
      (λ⇒ ⊗₁ λ⇒) ∘ i⇒ ∘ (λ⇐ ⊗₁ id)                                  ≈⟨ interchange-unitˡ ⟩
      λ⇒                                                            ≈˘⟨ eval-⌜id⌝ ⟩
      uncurry ⌜id⌝                                                  ∎)

    parallel-∘-eval : ⊗-eval {A} {C} {X} {Z}
                        ∘ (Self².⊚ {A = A , X} {B = B , Y} {C = C , Z} ⊗₁ id)
                      ≈ ((eval ∘ (id ⊗₁ eval) ∘ α⇒) ⊗₁ (eval ∘ (id ⊗₁ eval) ∘ α⇒))
                        ∘ (i⇒ ∘ (i⇒ ⊗₁ id))
    parallel-∘-eval = begin
      ⊗-eval ∘ (((internal-∘ ⊗₁ internal-∘) ∘ i⇒) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
      ⊗-eval ∘ ((internal-∘ ⊗₁ internal-∘) ⊗₁ id) ∘ (i⇒ ⊗₁ id)
        ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩
      ⊗-eval ∘ ((internal-∘ ⊗₁ internal-∘) ⊗₁ (id ⊗₁ id)) ∘ (i⇒ ⊗₁ id)
        ≈⟨ extend² interchange-natural ⟩
      ((eval ⊗₁ eval) ∘ ((internal-∘ ⊗₁ id) ⊗₁ (internal-∘ ⊗₁ id))) ∘ (i⇒ ∘ (i⇒ ⊗₁ id))
        ≈˘⟨ ⊗.homomorphism ⟩∘⟨refl ⟩
      ((eval ∘ (internal-∘ ⊗₁ id)) ⊗₁ (eval ∘ (internal-∘ ⊗₁ id))) ∘ (i⇒ ∘ (i⇒ ⊗₁ id))
        ≈⟨ eval-internal-∘ ⟩⊗⟨ eval-internal-∘ ⟩∘⟨refl ⟩
      ((eval ∘ (id ⊗₁ eval) ∘ α⇒) ⊗₁ (eval ∘ (id ⊗₁ eval) ∘ α⇒)) ∘
        (i⇒ ∘ (i⇒ ⊗₁ id)) ∎

    parallel-eval-assoc : ((eval ∘ (id ⊗₁ eval) ∘ α⇒) ⊗₁ (eval ∘ (id ⊗₁ eval) ∘ α⇒))
                            ∘ (i⇒ ∘ (i⇒ ⊗₁ id))
                          ≈ ⊗-eval {B} {C} {Y} {Z} ∘ (id ⊗₁ ⊗-eval {A} {B} {X} {Y}) ∘ α⇒
    parallel-eval-assoc = begin
      ((eval ∘ (id ⊗₁ eval) ∘ α⇒) ⊗₁ (eval ∘ (id ⊗₁ eval) ∘ α⇒)) ∘ (i⇒ ∘ (i⇒ ⊗₁ id))
        ≈⟨ pushˡ ⊗.homomorphism ⟩
      (eval ⊗₁ eval) ∘ ((((id ⊗₁ eval) ∘ α⇒) ⊗₁ ((id ⊗₁ eval) ∘ α⇒)) ∘ (i⇒ ∘ (i⇒ ⊗₁ id)))
        ≈⟨ refl⟩∘⟨ pushˡ ⊗.homomorphism ⟩
      (eval ⊗₁ eval) ∘ ((id ⊗₁ eval) ⊗₁ (id ⊗₁ eval)) ∘ (α⇒ ⊗₁ α⇒) ∘ i⇒ ∘ (i⇒ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ interchange-assoc ⟩
      (eval ⊗₁ eval) ∘ ((id ⊗₁ eval) ⊗₁ (id ⊗₁ eval)) ∘ i⇒ ∘ (id ⊗₁ i⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ pullˡ (⟺ interchange-natural) ⟩
      (eval ⊗₁ eval) ∘ (i⇒ ∘ ((id ⊗₁ id) ⊗₁ (eval ⊗₁ eval))) ∘ (id ⊗₁ i⇒) ∘ α⇒
        ≈⟨ assoc²δγ ⟩
      ⊗-eval ∘ ((id ⊗₁ id) ⊗₁ (eval ⊗₁ eval)) ∘ (id ⊗₁ i⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ʳ ⟩
      ⊗-eval ∘ ((id ⊗₁ id) ⊗₁ ⊗-eval) ∘ α⇒
        ≈⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
      ⊗-eval ∘ (id ⊗₁ ⊗-eval) ∘ α⇒ ∎

    ⊗-eval-∘ : ⊗-eval {A} {C} {X} {Z}
                  ∘ (Self².⊚ {A = A , X} {B = B , Y} {C = C , Z} ⊗₁ id)
               ≈ ⊗-eval {B} {C} {Y} {Z} ∘ (id ⊗₁ ⊗-eval) ∘ α⇒
    ⊗-eval-∘ = parallel-∘-eval ○ parallel-eval-assoc

    ⊗-map₁-homomorphism :
      ⊗-map₁ {A} {C} {X} {Z} ∘ Self².⊚ {A = A , X} {B = B , Y} {C = C , Z}
      ≈ internal-∘ ∘ (⊗-map₁ {B} {C} {Y} {Z} ⊗₁ ⊗-map₁ {A} {B} {X} {Y})
    ⊗-map₁-homomorphism = begin
      ⊗-map₁ ∘ Self².⊚                        ≈˘⟨ curry-∘ ⟩
      curry (⊗-eval ∘ (Self².⊚ ⊗₁ id))        ≈⟨ curry-resp-≈ ⊗-eval-∘ ⟩
      curry (⊗-eval ∘ (id ⊗₁ ⊗-eval) ∘ α⇒)    ≈˘⟨ internal-∘-curry ⟩
      internal-∘ ∘ (⊗-map₁ ⊗₁ ⊗-map₁)         ∎

  -⊗F- : Functor (selfEnrichment ⊠ selfEnrichment) selfEnrichment
  -⊗F- = record
    { map₀ = λ (A , X) → A ⊗₀ X
    ; map₁ = ⊗-map₁
    ; identity = ⊗-map₁-id
    ; homomorphism = ⊗-map₁-homomorphism
    }

  _⊗F- : Obj → SelfEndofunctor
  A ⊗F- = record
    { map₀ = A ⊗₀_
    ; map₁ = ⊗-map₁ ∘ (⌜id⌝ ⊗₁ id) ∘ λ⇐
    ; identity = Functor.identity (appˡ -⊗F- A)
    ; homomorphism = Functor.homomorphism (appˡ -⊗F- A)
    }

  private
    module Selfᵒ = Enriched.Category (EnrichedOpposite.op S selfEnrichment)
    module Tensorˡ (A : Obj) = Functor (A ⊗F-)

    abstract
      ⊗Fᵒᵖ-homomorphism :
        Tensorˡ.₁ A {X = Z} {Y = X} ∘ Selfᵒ.⊚ {A = X} {B = Y} {C = Z}
        ≈ Selfᵒ.⊚ {A = A ⊗₀ X} {B = A ⊗₀ Y} {C = A ⊗₀ Z} ∘
          (Tensorˡ.₁ A {X = Z} {Y = Y} ⊗₁ Tensorˡ.₁ A {X = Y} {Y = X})
      ⊗Fᵒᵖ-homomorphism {A = A} = begin
        Tensorˡ.₁ A ∘ (internal-∘ ∘ σ⇒)                   ≈⟨ pullˡ (Tensorˡ.homomorphism A) ⟩
        (internal-∘ ∘ (Tensorˡ.₁ A ⊗₁ Tensorˡ.₁ A)) ∘ σ⇒  ≈⟨ pullʳ (⟺ σ⇒-comm) ⟩
        internal-∘ ∘ σ⇒ ∘ (Tensorˡ.₁ A ⊗₁ Tensorˡ.₁ A)    ≈⟨ sym-assoc ⟩
        (internal-∘ ∘ σ⇒) ∘ (Tensorˡ.₁ A ⊗₁ Tensorˡ.₁ A)  ∎

  _⊗Fᵒᵖ- : Obj → Endofunctor (EnrichedOpposite.op S selfEnrichment)
  A ⊗Fᵒᵖ- = record
    { map₀ = A ⊗₀_
    ; map₁ = Tensorˡ.₁ A
    ; identity = Tensorˡ.identity A
    ; homomorphism = ⊗Fᵒᵖ-homomorphism
    }

  private abstract
    tensorˡ-coherence :
      ((λ⇒ {B} ⊗₁ id) ∘ i⇒) ∘ (λ⇐ { [ X , Y ]₀ } ⊗₁ id {B ⊗₀ X})
      ≈ α⇒ ∘ (σ⇒ { [ X , Y ]₀ } {B} ⊗₁ id) ∘ α⇐
    tensorˡ-coherence {B = B} {X} {Y} = begin
      ((λ⇒ ⊗₁ id) ∘ i⇒) ∘ (λ⇐ ⊗₁ id)                          ≈⟨ assoc ⟩
      (λ⇒ ⊗₁ id) ∘ i⇒ ∘ (λ⇐ ⊗₁ id)                            ≈⟨ pull-first λ⇒-assoc ⟩
      λ⇒ ∘ ((id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒) ∘ (λ⇐ ⊗₁ id) ≈⟨ refl⟩∘⟨ pullʳ λ⇐-assoc ⟩
      λ⇒ ∘ (id ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐)) ∘ λ⇐                ≈⟨ extendʳ unitorˡ-commute-from ⟩
      (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ λ⇒ ∘ λ⇐                        ≈⟨ elimʳ unitorˡ.isoʳ ⟩
      α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐  ∎

  ⊗F-eval : uncurry (Functor.₁ (B ⊗F-))
    ≈ (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ { [ X , Y ]₀ } {B} ⊗₁ id) ∘ α⇐
  ⊗F-eval {B = B} {X} {Y} = begin
    uncurry (Functor.₁ (B ⊗F-))                           ≈⟨ uncurry-∘ ⟩
    uncurry ⊗-map₁ ∘ (((⌜id⌝ ⊗₁ id) ∘ λ⇐) ⊗₁ id)          ≈⟨ eval-curry ⟩∘⟨refl ⟩
    ⊗-eval ∘ (((⌜id⌝ ⊗₁ id) ∘ λ⇐) ⊗₁ id)                  ≈⟨ pushʳ split₁ˡ ⟩
    (⊗-eval ∘ ((⌜id⌝ ⊗₁ id) ⊗₁ id)) ∘ (λ⇐ ⊗₁ id)          ≈˘⟨ (refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
    (⊗-eval ∘ ((⌜id⌝ ⊗₁ id) ⊗₁ (id ⊗₁ id))) ∘ (λ⇐ ⊗₁ id)  ≈⟨ pullʳ interchange-natural ⟩∘⟨refl ⟩
    ((eval ⊗₁ eval) ∘ (((⌜id⌝ ⊗₁ id) ⊗₁ (id ⊗₁ id)) ∘ i⇒))
      ∘ (λ⇐ ⊗₁ id)
      ≈⟨ pullˡ (⟺ ⊗.homomorphism) ⟩∘⟨refl ⟩
    (((eval ∘ (⌜id⌝ ⊗₁ id)) ⊗₁ (eval ∘ (id ⊗₁ id)))
      ∘ i⇒) ∘ (λ⇐ ⊗₁ id)
      ≈⟨ (eval-⌜id⌝ ⟩⊗⟨ (refl⟩∘⟨ ⊗.identity)) ⟩∘⟨refl ⟩∘⟨refl ⟩
    ((λ⇒ ⊗₁ (eval ∘ id)) ∘ i⇒) ∘ (λ⇐ ⊗₁ id)
      ≈⟨ (refl⟩⊗⟨ identityʳ ⟩∘⟨refl) ⟩∘⟨refl ⟩
    ((λ⇒ ⊗₁ eval) ∘ i⇒) ∘ (λ⇐ ⊗₁ id)                    ≈˘⟨ identityˡ ⟩⊗⟨ identityʳ ⟩∘⟨refl ⟩∘⟨refl ⟩
    (((id ∘ λ⇒) ⊗₁ (eval ∘ id)) ∘ i⇒) ∘ (λ⇐ ⊗₁ id)      ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩∘⟨refl ⟩
    (((id ⊗₁ eval) ∘ (λ⇒ ⊗₁ id)) ∘ i⇒) ∘ (λ⇐ ⊗₁ id)     ≈⟨ assoc²αδ ⟩
    (id ⊗₁ eval) ∘ ((λ⇒ ⊗₁ id) ∘ i⇒) ∘ (λ⇐ ⊗₁ id)       ≈⟨ refl⟩∘⟨ tensorˡ-coherence ⟩
    (id ⊗₁ eval) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐                 ∎

open SelfTensor public
