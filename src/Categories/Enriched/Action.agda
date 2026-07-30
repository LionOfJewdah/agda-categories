{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Kelly, "Basic Concepts of Enriched Category Theory", Sections 1.5--1.6:
-- equation (1.21) characterizes a bifunctor by two commuting partial actions.

module Categories.Enriched.Action
  {o ℓ e} {V : Category o ℓ e} {M : Monoidal V} (S : Symmetric M) where

open import Level using (_⊔_; levelOfTerm)

import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
import Categories.Enriched.Category as Enriched
import Categories.Enriched.Category.Properties as EnrichedProperties
import Categories.Enriched.Category.Underlying as Underlying

open Category V renaming (id to idV)
open Commutation V
open Monoidal M
open Symmetric S using (braided)
open import Categories.Category.Monoidal.Interchange.Braided braided
  using (module swapInner)
  renaming (hasInterchange to interchange)
open import Categories.Category.Monoidal.Interchange.Symmetric S
  using (swapInner-commutative)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Category M using (_[_,_])
open import Categories.Enriched.Category.TensorProduct interchange using (_⊠_)
open import Categories.Enriched.Functor M using (Functor)
open import Categories.Morphism.Reasoning V
open BraidedProperties.Shorthands braided
open Shorthands

module Composition {c} (𝒞 : Enriched.Category M c) where
  private
    module 𝒞 = Enriched.Category 𝒞

    variable
      A B C : 𝒞.Obj
      X Y : Obj

  ⊚ᵥ : (A B C : 𝒞.Obj) → (X ⇒ 𝒞 [ B , C ]) → (Y ⇒ 𝒞 [ A , B ]) →
    X ⊗₀ Y ⇒ 𝒞 [ A , C ]
  ⊚ᵥ A B C f g = 𝒞.⊚ {A = A} {B} {C} ∘ (f ⊗₁ g)

  module CompositionLaws {A B C W : 𝒞.Obj} {X Y Z : Obj} where
    abstract
      ⊚ᵥ-assoc :
        {f : X ⇒ 𝒞 [ C , W ]} {g : Y ⇒ 𝒞 [ B , C ]} {h : Z ⇒ 𝒞 [ A , B ]} →
        ⊚ᵥ A B W (⊚ᵥ B C W f g) h ≈ ⊚ᵥ A C W f (⊚ᵥ A B C g h) ∘ α⇒
      ⊚ᵥ-assoc {f = f} {g} {h} = begin
        ⊚ᵥ A B W (⊚ᵥ B C W f g) h                       ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
        𝒞.⊚ ∘ (𝒞.⊚ ⊗₁ idV) ∘ ((f ⊗₁ g) ⊗₁ h)             ≈⟨ pullˡ 𝒞.⊚-assoc ⟩
        (𝒞.⊚ ∘ (idV ⊗₁ 𝒞.⊚) ∘ α⇒) ∘ ((f ⊗₁ g) ⊗₁ h)
          ≈⟨ pullʳ (pullʳ assoc-commute-from) ⟩
        𝒞.⊚ ∘ (idV ⊗₁ 𝒞.⊚) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ α⇒
          ≈˘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
        𝒞.⊚ ∘ (f ⊗₁ (𝒞.⊚ ∘ (g ⊗₁ h))) ∘ α⇒            ≈⟨ sym-assoc ⟩
        ⊚ᵥ A C W f (⊚ᵥ A B C g h) ∘ α⇒                ∎

  open CompositionLaws public

module HelperDefinition {a b c}
  (𝒜 : Enriched.Category M a) (ℬ : Enriched.Category M b)
  (𝒞 : Enriched.Category M c) where

  private
    module 𝒜 = Enriched.Category 𝒜
    module ℬ = Enriched.Category ℬ
    module 𝒞 = Enriched.Category 𝒞
    open Composition 𝒞

    variable
      A₁ A₂ A₃ : 𝒜.Obj
      B₁ B₂ B₃ : ℬ.Obj

  record CommutingActions : Set (levelOfTerm 𝒜 ⊔ levelOfTerm ℬ ⊔ levelOfTerm 𝒞) where
    field
      map₀ : 𝒜.Obj → ℬ.Obj → 𝒞.Obj

      mapˡ : (A₁ A₂ : 𝒜.Obj) (B : ℬ.Obj) →
        𝒜 [ A₁ , A₂ ] ⇒ 𝒞 [ map₀ A₁ B , map₀ A₂ B ]
      mapʳ : (A : 𝒜.Obj) (B₁ B₂ : ℬ.Obj) →
        ℬ [ B₁ , B₂ ] ⇒ 𝒞 [ map₀ A B₁ , map₀ A B₂ ]

      identityˡ : (A₁ : 𝒜.Obj) (B₁ : ℬ.Obj) → mapˡ A₁ A₁ B₁ ∘ 𝒜.id ≈ 𝒞.id
      identityʳ : (A₁ : 𝒜.Obj) (B₁ : ℬ.Obj) → mapʳ A₁ B₁ B₁ ∘ ℬ.id ≈ 𝒞.id

      homomorphismˡ : (A₁ A₂ A₃ : 𝒜.Obj) (B₁ : ℬ.Obj) →
        mapˡ A₁ A₃ B₁ ∘ 𝒜.⊚
        ≈ 𝒞.⊚ ∘ (mapˡ A₂ A₃ B₁ ⊗₁ mapˡ A₁ A₂ B₁)

      homomorphismʳ : (A₁ : 𝒜.Obj) (B₁ B₂ B₃ : ℬ.Obj) →
        mapʳ A₁ B₁ B₃ ∘ ℬ.⊚
        ≈ 𝒞.⊚ ∘ (mapʳ A₁ B₂ B₃ ⊗₁ mapʳ A₁ B₁ B₂)

      commute : (A₁ A₂ : 𝒜.Obj) (B₁ B₂ : ℬ.Obj) →
        𝒞.⊚ ∘ (mapˡ A₁ A₂ B₂ ⊗₁ mapʳ A₁ B₁ B₂)
        ≈ (𝒞.⊚ ∘ (mapʳ A₂ B₁ B₂ ⊗₁ mapˡ A₁ A₂ B₁)) ∘ σ⇒

open HelperDefinition public using (CommutingActions)

module FromActions {a b c}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} (H : CommutingActions 𝒜 ℬ 𝒞) where

  module H = CommutingActions H
  open H using (map₀; mapˡ; mapʳ)
    renaming ( identityˡ to idˡ ; identityʳ to idʳ ;
               homomorphismˡ to homoˡ ; homomorphismʳ to homoʳ ;
               commute to H-commute )
  module 𝒜 = Enriched.Category 𝒜
  module ℬ = Enriched.Category ℬ
  module 𝒞 = Enriched.Category 𝒞
  module 𝒞ᵤ = Category (Underlying.Underlying M 𝒞)
  module 𝒞ₚ = EnrichedProperties M 𝒞
  module 𝒜⊠ℬ = Enriched.Category (𝒜 ⊠ ℬ)
  open Composition 𝒞

  variable
    A₁ A₂ A₃ : 𝒜.Obj
    B₁ B₂ B₃ : ℬ.Obj

  appˡ : 𝒜.Obj → Functor ℬ 𝒞
  appˡ A = record
    { map₀ = map₀ A
    ; map₁ = λ {X} {Y} → mapʳ A X Y
    ; identity = λ {X} → idʳ A X
    ; homomorphism = λ {X} {Y} {Z} → homoʳ A X Y Z
    }

  appʳ : ℬ.Obj → Functor 𝒜 𝒞
  appʳ B = record
    { map₀ = λ A → map₀ A B
    ; map₁ = λ {X} {Y} → mapˡ X Y B
    ; identity = λ {X} → idˡ X B
    ; homomorphism = λ {X} {Y} {Z} → homoˡ X Y Z B
    }

  module Appˡ (A : 𝒜.Obj) = Functor (appˡ A)
  module Appʳ (B : ℬ.Obj) = Functor (appʳ B)

  diagonal : 𝒜 [ A₁ , A₂ ] ⊗₀ ℬ [ B₁ , B₂ ] ⇒ 𝒞 [ map₀ A₁ B₁ , map₀ A₂ B₂ ]
  diagonal {A₁ = A₁} {A₂} {B₁} {B₂} =
    𝒞.⊚ ∘ (mapˡ A₁ A₂ B₂ ⊗₁ mapʳ A₁ B₁ B₂)

  abstract
    diagonal-appˡ : diagonal ∘ ((𝒜.id ⊗₁ idV) ∘ λ⇐) ≈ mapʳ A₁ B₁ B₂
    diagonal-appˡ {A₁ = A₁} {B₁} {B₂} = begin
      diagonal ∘ ((𝒜.id ⊗₁ idV) ∘ λ⇐)
        ≈⟨ pullʳ (pullˡ (⟺ ⊗.homomorphism)) ⟩
      𝒞.⊚ ∘ ((mapˡ A₁ A₁ B₂ ∘ 𝒜.id) ⊗₁
             (mapʳ A₁ B₁ B₂ ∘ idV)) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ idˡ A₁ B₂ ⟩⊗⟨ identityʳ ⟩∘⟨refl ⟩
      𝒞.⊚ ∘ (𝒞.id ⊗₁ mapʳ A₁ B₁ B₂) ∘ λ⇐                 ≈⟨ 𝒞ₚ.unitˡ-var ⟩
      mapʳ A₁ B₁ B₂                                      ∎

    diagonal-appʳ : diagonal ∘ ((idV ⊗₁ ℬ.id) ∘ ρ⇐) ≈ mapˡ A₁ A₂ B₁
    diagonal-appʳ {A₁ = A₁} {A₂} {B₁} = begin
      diagonal ∘ ((idV ⊗₁ ℬ.id) ∘ ρ⇐)
        ≈⟨ pullʳ (pullˡ (⟺ ⊗.homomorphism)) ⟩
      𝒞.⊚ ∘ ((mapˡ A₁ A₂ B₁ ∘ idV) ⊗₁
             (mapʳ A₁ B₁ B₁ ∘ ℬ.id)) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ identityʳ ⟩⊗⟨ idʳ A₁ B₁ ⟩∘⟨refl ⟩
      𝒞.⊚ ∘ (mapˡ A₁ A₂ B₁ ⊗₁ 𝒞.id) ∘ ρ⇐                 ≈⟨ 𝒞ₚ.unitʳ-var ⟩
      mapˡ A₁ A₂ B₁                                      ∎

  abstract
    identity : [ unit ⇒ 𝒞 [ map₀ A₁ B₁ , map₀ A₁ B₁ ] ]⟨
                 diagonal ∘ 𝒜⊠ℬ.id ≈ 𝒞.id
               ⟩
    identity {A₁ = A₁} {B₁ = B₁} = begin
      diagonal ∘ 𝒜⊠ℬ.id
        ≈⟨ pullʳ (pullˡ (⟺ ⊗.homomorphism)) ⟩
      𝒞.⊚ ∘ ((mapˡ A₁ A₁ B₁ ∘ 𝒜.id) ⊗₁
             (mapʳ A₁ B₁ B₁ ∘ ℬ.id)) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ idˡ A₁ B₁ ⟩⊗⟨ idʳ A₁ B₁ ⟩∘⟨refl ⟩
      𝒞.⊚ ∘ (𝒞.id ⊗₁ 𝒞.id) ∘ λ⇐                            ≈⟨ 𝒞ᵤ.identityˡ ⟩
      𝒞.id                                                 ∎

  module ActionComposition
    {A B C W X Y : 𝒞.Obj} {U V W₀ Z : Obj}
    (after : U ⇒ 𝒞 [ X , Y ]) {across : V ⇒ 𝒞 [ C , X ]}
    {before : W₀ ⇒ 𝒞 [ B , C ]} (initial : Z ⇒ 𝒞 [ A , B ])
    {across′ : V ⇒ 𝒞 [ B , W ]} {before′ : W₀ ⇒ 𝒞 [ W , X ]}
    (middle-commute : [ V ⊗₀ W₀ ⇒ 𝒞 [ B , X ] ]⟨
        ⊚ᵥ B C X across before ≈ ⊚ᵥ B W X before′ across′ ∘ σ⇒
      ⟩)
    where

    private abstract
      action-exchange : [ (U ⊗₀ W₀) ⊗₀ (V ⊗₀ Z) ⇒ U ⊗₀ (W₀ ⊗₀ (V ⊗₀ Z)) ]⟨
          (idV ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐)) ∘ α⇒ ∘ swapInner.from ≈ α⇒
        ⟩
      action-exchange = begin
        (idV ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐)) ∘ α⇒ ∘ swapInner.from
          ≈⟨ sym-assoc ⟩
        ((idV ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐)) ∘ α⇒) ∘ swapInner.from
          ≈˘⟨ cancelˡ associator.isoʳ ⟩∘⟨refl ⟩
        (α⇒ ∘ swapInner.from) ∘ swapInner.from  ≈⟨ pullʳ swapInner-commutative ⟩
        α⇒ ∘ idV                                 ≈⟨ identityʳ ⟩
        α⇒                                      ∎

      cross-middle-action : [ (V ⊗₀ W₀) ⊗₀ Z ⇒ 𝒞 [ A , X ] ]⟨
          ⊚ᵥ A B X (⊚ᵥ B W X before′ across′) initial ∘ (σ⇒ ⊗₁ idV)
        ≈ ⊚ᵥ A B X (⊚ᵥ B W X before′ across′ ∘ σ⇒) initial
        ⟩
      cross-middle-action = begin
        ⊚ᵥ A B X (⊚ᵥ B W X before′ across′) initial ∘ (σ⇒ ⊗₁ idV)
          ≈⟨ pullʳ (⟺ split₁ʳ) ⟩
        ⊚ᵥ A B X (⊚ᵥ B W X before′ across′ ∘ σ⇒) initial ∎

      commute-below : [ V ⊗₀ (W₀ ⊗₀ Z) ⇒ 𝒞 [ A , X ] ]⟨
          (⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial) ∘ α⇒)
            ∘ ((σ⇒ ⊗₁ idV) ∘ α⇐)
        ≈ ⊚ᵥ A C X across (⊚ᵥ A B C before initial)
        ⟩
      commute-below = begin
        (⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial) ∘ α⇒)
          ∘ ((σ⇒ ⊗₁ idV) ∘ α⇐)
          ≈˘⟨ ⊚ᵥ-assoc ⟩∘⟨refl ⟩
        ⊚ᵥ A B X (⊚ᵥ B W X before′ across′) initial ∘ ((σ⇒ ⊗₁ idV) ∘ α⇐)
          ≈⟨ pullˡ cross-middle-action ⟩
        ⊚ᵥ A B X (⊚ᵥ B W X before′ across′ ∘ σ⇒) initial ∘ α⇐
          ≈˘⟨ (refl⟩∘⟨ (middle-commute ⟩⊗⟨refl)) ⟩∘⟨refl ⟩
        ⊚ᵥ A B X (⊚ᵥ B C X across before) initial ∘ α⇐
          ≈⟨ ⊚ᵥ-assoc ⟩∘⟨refl ⟩
        (⊚ᵥ A C X across (⊚ᵥ A B C before initial) ∘ α⇒) ∘ α⇐
          ≈⟨ cancelʳ associator.isoʳ ⟩
        ⊚ᵥ A C X across (⊚ᵥ A B C before initial) ∎

      extend-after : [ U ⊗₀ (V ⊗₀ (W₀ ⊗₀ Z)) ⇒ 𝒞 [ A , Y ] ]⟨
          ⊚ᵥ A X Y after ((⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial) ∘ α⇒)
            ∘ ((σ⇒ ⊗₁ idV) ∘ α⇐))
        ≈ ⊚ᵥ A X Y after (⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial))
            ∘ (idV ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐))
        ⟩
      extend-after = begin
        ⊚ᵥ A X Y after ((⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial) ∘ α⇒)
          ∘ ((σ⇒ ⊗₁ idV) ∘ α⇐))
          ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ assoc) ⟩
        ⊚ᵥ A X Y after (⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial)
          ∘ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐))
          ≈⟨ refl⟩∘⟨ split₂ʳ ⟩
        𝒞.⊚ ∘ (after ⊗₁ ⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial))
          ∘ (idV ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐))
          ≈⟨ sym-assoc ⟩
        ⊚ᵥ A X Y after (⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial))
          ∘ (idV ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐)) ∎

      commute-middle : [ (U ⊗₀ W₀) ⊗₀ (V ⊗₀ Z) ⇒ 𝒞 [ A , Y ] ]⟨
          (⊚ᵥ A X Y after (⊚ᵥ A C X across (⊚ᵥ A B C before initial)) ∘ α⇒)
            ∘ swapInner.from
        ≈ ⊚ᵥ A X Y after (⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial))
            ∘ (idV ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐))
            ∘ α⇒ ∘ swapInner.from
        ⟩
      commute-middle = begin
        (⊚ᵥ A X Y after (⊚ᵥ A C X across (⊚ᵥ A B C before initial)) ∘ α⇒)
          ∘ swapInner.from
          ≈˘⟨ ((refl⟩∘⟨ refl⟩⊗⟨ commute-below) ⟩∘⟨refl) ⟩∘⟨refl ⟩
        (⊚ᵥ A X Y after ((⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial) ∘ α⇒)
          ∘ ((σ⇒ ⊗₁ idV) ∘ α⇐)) ∘ α⇒) ∘ swapInner.from
          ≈⟨ (extend-after ⟩∘⟨refl) ⟩∘⟨refl ⟩
        ((⊚ᵥ A X Y after (⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial))
          ∘ (idV ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐))) ∘ α⇒) ∘ swapInner.from
          ≈⟨ assoc²αε ⟩
        ⊚ᵥ A X Y after (⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial))
          ∘ (idV ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐)) ∘ α⇒ ∘ swapInner.from ∎

    abstract
      compose : ⊚ᵥ A C Y (⊚ᵥ C X Y after across) (⊚ᵥ A B C before initial)
                  ∘ swapInner.from
                ≈ ⊚ᵥ A W Y (⊚ᵥ W X Y after before′) (⊚ᵥ A B W across′ initial)
      compose = begin
        ⊚ᵥ A C Y (⊚ᵥ C X Y after across) (⊚ᵥ A B C before initial) ∘ swapInner.from
          ≈⟨ ⊚ᵥ-assoc ⟩∘⟨refl ⟩
        (⊚ᵥ A X Y after (⊚ᵥ A C X across (⊚ᵥ A B C before initial)) ∘ α⇒)
          ∘ swapInner.from
          ≈⟨ commute-middle ⟩
        ⊚ᵥ A X Y after (⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial))
          ∘ (idV ⊗₁ (α⇒ ∘ (σ⇒ ⊗₁ idV) ∘ α⇐)) ∘ α⇒ ∘ swapInner.from
          ≈⟨ refl⟩∘⟨ action-exchange ⟩
        ⊚ᵥ A X Y after (⊚ᵥ A W X before′ (⊚ᵥ A B W across′ initial)) ∘ α⇒
          ≈˘⟨ ⊚ᵥ-assoc ⟩
        ⊚ᵥ A W Y (⊚ᵥ W X Y after before′) (⊚ᵥ A B W across′ initial) ∎

  open ActionComposition

  abstract
    homomorphism : {A₁ A₂ A₃ : 𝒜.Obj} {B₁ B₂ B₃ : ℬ.Obj} →
      [ (𝒜 [ A₂ , A₃ ] ⊗₀ ℬ [ B₂ , B₃ ]) ⊗₀ (𝒜 [ A₁ , A₂ ] ⊗₀ ℬ [ B₁ , B₂ ])
        ⇒ 𝒞 [ map₀ A₁ B₁ , map₀ A₃ B₃ ] ]⟨
          diagonal ∘ 𝒜⊠ℬ.⊚
        ≈ 𝒞.⊚ ∘ (diagonal ⊗₁ diagonal)
        ⟩
    homomorphism {A₁ = A₁} {A₂} {A₃} {B₁} {B₂} {B₃} = begin
      diagonal ∘ 𝒜⊠ℬ.⊚
        ≈⟨ pullʳ (pullˡ (⟺ ⊗.homomorphism)) ⟩
      𝒞.⊚ ∘ ((mapˡ A₁ A₃ B₃ ∘ 𝒜.⊚) ⊗₁
             (mapʳ A₁ B₁ B₃ ∘ ℬ.⊚)) ∘ swapInner.from
        ≈⟨ refl⟩∘⟨ homoˡ A₁ A₂ A₃ B₃ ⟩⊗⟨ homoʳ A₁ B₁ B₂ B₃ ⟩∘⟨refl ⟩
      𝒞.⊚ ∘
        ((𝒞.⊚ ∘ (mapˡ A₂ A₃ B₃ ⊗₁ mapˡ A₁ A₂ B₃)) ⊗₁
         (𝒞.⊚ ∘ (mapʳ A₁ B₂ B₃ ⊗₁ mapʳ A₁ B₁ B₂))) ∘ swapInner.from
        ≈⟨ sym-assoc ⟩
      (𝒞.⊚ ∘
        ((𝒞.⊚ ∘ (mapˡ A₂ A₃ B₃ ⊗₁ mapˡ A₁ A₂ B₃)) ⊗₁
         (𝒞.⊚ ∘ (mapʳ A₁ B₂ B₃ ⊗₁ mapʳ A₁ B₁ B₂)))) ∘ swapInner.from
        ≈⟨ compose (mapˡ A₂ A₃ B₃) (mapʳ A₁ B₁ B₂) (H-commute A₁ A₂ B₂ B₃) ⟩
      𝒞.⊚ ∘ (diagonal ⊗₁ diagonal)                         ∎
