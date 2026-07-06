{-# OPTIONS --without-K --safe #-}
open import Categories.Category
import Categories.Category.Monoidal.Core as M

-- Properties of Monoidal Categories

module Categories.Category.Monoidal.Properties
  {o ℓ e} {C : Category o ℓ e} (MC : M.Monoidal C) where

open import Data.Product using (_,_; Σ; uncurry′)

open Category C
open M.Monoidal MC
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Category.Monoidal.Utilities MC hiding (triangle-inv)
open import Categories.Category.Monoidal.Reasoning MC
  using (_⟩⊗⟨_; ⊗-distrib-over-∘)
open import Categories.Category.Construction.Core C as Core using (Core)
open import Categories.Category.Product using (Product)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Properties
open import Categories.Morphism.Isomorphism C
  using (elim-triangleˡ′; triangle-prism; cut-squareʳ)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
  using (push-eq)

private
  module C = Category C
  variable
    A B P Q R : Obj
open Core.Shorthands

monoidal-Op : M.Monoidal C.op
monoidal-Op = record
  { ⊗ = Functor.op ⊗
  ; unit = unit
  ; unitorˡ = ≅⇒op-≅ unitorˡ
  ; unitorʳ = ≅⇒op-≅ unitorʳ
  ; associator = ≅⇒op-≅ associator
  ; unitorˡ-commute-from = sym unitorˡ-commute-to
  ; unitorˡ-commute-to = sym unitorˡ-commute-from
  ; unitorʳ-commute-from = sym unitorʳ-commute-to
  ; unitorʳ-commute-to = sym unitorʳ-commute-from
  ; assoc-commute-from = sym assoc-commute-to
  ; assoc-commute-to = sym assoc-commute-from
  ; triangle = MonoidalUtilities.triangle-inv MC
  ; pentagon = pentagon-inv
  }
  where
  open import Categories.Morphism.Duality C using (≅⇒op-≅)
  open Equiv using (sym)

⊗-iso : Bifunctor Core Core Core
⊗-iso = record
  { F₀           = uncurry′ _⊗₀_
  ; F₁           =  λ where (f , g) → f ⊗ᵢ g
  ; identity     = refl⊗refl≃refl
  ; homomorphism = ⌞ homomorphism ⌟
  ; F-resp-≈     = λ where (⌞ eq₁ ⌟ , ⌞ eq₂ ⌟) → ⌞ F-resp-≈ (eq₁ , eq₂) ⌟
  }
  where open Functor ⊗

_⊗ᵢ- : Obj → Functor Core Core
X ⊗ᵢ- = appˡ ⊗-iso X

-⊗ᵢ_ : Obj → Functor Core Core
-⊗ᵢ X = appʳ ⊗-iso X

-- Coherence laws due to Mac Lane (1963) that were subsequently proven
-- admissible by Max Kelly (1964).  See
-- https://ncatlab.org/nlab/show/monoidal+category#other_coherence_conditions
-- for more details.

module Kelly's where
  open Functor
  open Shorthands
  open Commutation C
  open Commutationᵢ

  private
    variable
      f f′ g h h′ i i′ j k : A ≅ B

  module _ {X Y : Obj} where
    open HomReasoningᵢ

    -- TS: following three isos commute

    ua : unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ unit ⊗₀ X ⊗₀ Y
    ua = idᵢ ⊗ᵢ associator

    u[λY] : unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
    u[λY] = idᵢ ⊗ᵢ unitorˡ ⊗ᵢ idᵢ

    uλ : unit ⊗₀ unit ⊗₀ X ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
    uλ = idᵢ ⊗ᵢ unitorˡ

    -- setups

    perimeter : [ ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y ]⟨
                  (unitorʳ ⊗ᵢ idᵢ) ⊗ᵢ idᵢ    ≅⟨ (unit ⊗₀ X) ⊗₀ Y ⟩
                  associator
                ≈ associator                 ≅⟨ (unit ⊗₀ unit) ⊗₀ X ⊗₀ Y ⟩
                  associator                 ≅⟨ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ⟩
                  uλ
                ⟩
    perimeter = ⟺ (glue◃◽′ triangle-iso
                             (⟺ ⌞ Equiv.trans assoc-commute-from
                                                (∘-resp-≈ˡ (F-resp-≈ ⊗ (Equiv.refl , identity ⊗))) ⌟))
      where open MR Core

    [uλ]Y : (unit ⊗₀ (unit ⊗₀ X)) ⊗₀ Y ≅ (unit ⊗₀ X) ⊗₀ Y
    [uλ]Y = (idᵢ ⊗ᵢ unitorˡ) ⊗ᵢ idᵢ

    aY : ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ (unit ⊗₀ unit ⊗₀ X) ⊗₀ Y
    aY = associator ⊗ᵢ idᵢ

    [ρX]Y : ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ (unit ⊗₀ X) ⊗₀ Y
    [ρX]Y = (unitorʳ ⊗ᵢ idᵢ) ⊗ᵢ idᵢ

    tri : [uλ]Y ∘ᵢ aY ≈ᵢ [ρX]Y
    tri = ⌞ [ appʳ ⊗ Y ]-resp-∘ triangle ⌟

    sq : associator ∘ᵢ [uλ]Y ≈ᵢ u[λY] ∘ᵢ associator
    sq = ⌞ assoc-commute-from ⌟

    -- proofs

    perimeter′ : [ ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y ]⟨
                   (unitorʳ ⊗ᵢ idᵢ) ⊗ᵢ idᵢ    ≅⟨ (unit ⊗₀ X) ⊗₀ Y ⟩
                   associator
                 ≈ aY                         ≅⟨ (unit ⊗₀ (unit ⊗₀ X)) ⊗₀ Y ⟩
                   associator                 ≅⟨ unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ⟩
                   ua                         ≅⟨ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ⟩
                   uλ
                 ⟩
    perimeter′ = begin
      associator ∘ᵢ (unitorʳ ⊗ᵢ idᵢ) ⊗ᵢ idᵢ    ≈⟨ perimeter ⟩
      uλ ∘ᵢ associator ∘ᵢ associator           ≈˘⟨ refl⟩∘⟨ pentagon-iso ⟩
      uλ ∘ᵢ ua ∘ᵢ associator ∘ᵢ aY             ∎

    top-face : uλ ∘ᵢ ua ≈ᵢ u[λY]
    top-face = elim-triangleˡ′ (⟺ perimeter′) (glue◽◃ (⟺ sq) tri)
      where open MR Core

    coherence-iso₁ : [ (unit ⊗₀ X) ⊗₀ Y ≅ X ⊗₀ Y ]⟨
                       associator       ≅⟨ unit ⊗₀ X ⊗₀ Y ⟩
                       unitorˡ
                     ≈ unitorˡ ⊗ᵢ idᵢ
                     ⟩
    coherence-iso₁ = triangle-prism top-face square₁ square₂ square₃
      where square₁ : [ unit ⊗₀ X ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y ]⟨
                        unitorˡ ⁻¹ ∘ᵢ unitorˡ
                      ≈ idᵢ ⊗ᵢ unitorˡ ∘ᵢ unitorˡ ⁻¹
                      ⟩
            square₁ = ⌞ unitorˡ-commute-to ⌟

            square₂ : [ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ]⟨
                        unitorˡ ⁻¹ ∘ᵢ associator
                      ≈ idᵢ ⊗ᵢ associator ∘ᵢ unitorˡ ⁻¹
                      ⟩
            square₂ = ⌞ unitorˡ-commute-to ⌟

            square₃ : [ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y ]⟨
                        unitorˡ ⁻¹ ∘ᵢ unitorˡ ⊗ᵢ idᵢ
                      ≈ idᵢ ⊗ᵢ unitorˡ ⊗ᵢ idᵢ ∘ᵢ unitorˡ ⁻¹
                      ⟩
            square₃ = ⌞ unitorˡ-commute-to ⌟

    coherence₁ : [ (unit ⊗₀ X) ⊗₀ Y ⇒ X ⊗₀ Y ]⟨
                   α⇒               ⇒⟨ unit ⊗₀ X ⊗₀ Y ⟩
                   λ⇒
                 ≈ λ⇒ ⊗₁ id
                 ⟩
    coherence₁ = from-≈ coherence-iso₁

    coherence-inv₁ : [ X ⊗₀ Y ⇒ (unit ⊗₀ X) ⊗₀ Y ]⟨
                       λ⇐               ⇒⟨ unit ⊗₀ X ⊗₀ Y ⟩
                       α⇐
                     ≈ λ⇐ ⊗₁ id
                     ⟩
    coherence-inv₁ = to-≈ coherence-iso₁

    -- another coherence property

    -- TS : the following three commute

    ρu : ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y) ⊗₀ unit
    ρu = unitorʳ ⊗ᵢ idᵢ

    au : ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit
    au = associator ⊗ᵢ idᵢ

    [Xρ]u : (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y) ⊗₀ unit
    [Xρ]u = (idᵢ ⊗ᵢ unitorʳ) ⊗ᵢ idᵢ


    perimeter″ : [ ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ X ⊗₀ Y ⊗₀ unit ]⟨
                   associator                 ≅⟨ (X ⊗₀ Y) ⊗₀ unit ⊗₀ unit ⟩
                   associator                 ≅⟨ X ⊗₀ Y ⊗₀ unit ⊗₀ unit ⟩
                   idᵢ ⊗ᵢ idᵢ ⊗ᵢ unitorˡ
                 ≈ ρu                         ≅⟨ (X ⊗₀ Y) ⊗₀ unit ⟩
                   associator
                 ⟩
    perimeter″ = glue▹◽ triangle-iso (⟺ ⌞
        Equiv.trans (∘-resp-≈ʳ (F-resp-≈ ⊗ (Equiv.sym (identity ⊗) , Equiv.refl)))
                     assoc-commute-from ⌟)
      where open MR Core

    perimeter‴ : [ ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ X ⊗₀ Y ⊗₀ unit  ]⟨
                   associator ⊗ᵢ idᵢ          ≅⟨ (X ⊗₀ (Y ⊗₀ unit)) ⊗₀ unit ⟩
                   (associator                ≅⟨ X ⊗₀ (Y ⊗₀ unit) ⊗₀ unit ⟩
                   idᵢ ⊗ᵢ associator          ≅⟨ X ⊗₀ Y ⊗₀ unit ⊗₀ unit ⟩
                   idᵢ ⊗ᵢ idᵢ ⊗ᵢ unitorˡ)
                 ≈ ρu                         ≅⟨ (X ⊗₀ Y) ⊗₀ unit ⟩
                   associator
                 ⟩
    perimeter‴ = let α = associator in let λλ = unitorˡ in begin
      (idᵢ ⊗ᵢ idᵢ ⊗ᵢ λλ ∘ᵢ idᵢ ⊗ᵢ α ∘ᵢ α) ∘ᵢ α ⊗ᵢ idᵢ  ≈⟨ ⌞ assoc ⌟ ⟩
       idᵢ ⊗ᵢ idᵢ ⊗ᵢ λλ ∘ᵢ (idᵢ ⊗ᵢ α ∘ᵢ α) ∘ᵢ α ⊗ᵢ idᵢ ≈⟨ refl⟩∘⟨ ⌞ assoc ⌟ ⟩
       idᵢ ⊗ᵢ idᵢ ⊗ᵢ λλ ∘ᵢ idᵢ ⊗ᵢ α ∘ᵢ α ∘ᵢ α ⊗ᵢ idᵢ   ≈⟨ refl⟩∘⟨ pentagon-iso ⟩
       idᵢ ⊗ᵢ idᵢ ⊗ᵢ λλ ∘ᵢ α ∘ᵢ α                      ≈⟨ perimeter″ ⟩
       α ∘ᵢ ρu                                         ∎

    top-face′ : [Xρ]u ∘ᵢ au ≈ᵢ ρu
    top-face′ = cut-squareʳ perimeter‴ (⟺ (glue◃◽′ tri′ (⟺ ⌞ assoc-commute-from ⌟)))
      where open MR Core
            tri′ : [ X ⊗₀ (Y ⊗₀ unit) ⊗₀ unit ≅ X ⊗₀ Y ⊗₀ unit ]⟨
                     (idᵢ ⊗ᵢ idᵢ ⊗ᵢ unitorˡ ∘ᵢ idᵢ ⊗ᵢ associator)
                   ≈ idᵢ ⊗ᵢ unitorʳ ⊗ᵢ idᵢ
                   ⟩
            tri′ = ⌞ [ X ⊗- ]-resp-∘ triangle ⌟

    coherence-iso₂ : [ (X ⊗₀ Y) ⊗₀ unit ≅ X ⊗₀ Y ]⟨
                       idᵢ ⊗ᵢ unitorʳ ∘ᵢ associator
                     ≈ unitorʳ
                     ⟩
    coherence-iso₂ = triangle-prism top-face′ square₁ square₂ ⌞ unitorʳ-commute-to ⌟
      where square₁ : [ X ⊗₀ Y ⊗₀ unit ≅ (X ⊗₀ Y) ⊗₀ unit ]⟨
                        unitorʳ ⁻¹ ∘ᵢ idᵢ ⊗ᵢ unitorʳ
                      ≈ (idᵢ ⊗ᵢ unitorʳ) ⊗ᵢ idᵢ ∘ᵢ unitorʳ ⁻¹
                      ⟩
            square₁ = ⌞ unitorʳ-commute-to ⌟

            square₂ : [ (X ⊗₀ Y) ⊗₀ unit ≅ (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit ]⟨
                        unitorʳ ⁻¹ ∘ᵢ associator
                      ≈ associator ⊗ᵢ idᵢ ∘ᵢ unitorʳ ⁻¹
                      ⟩
            square₂ = ⌞ unitorʳ-commute-to ⌟

    coherence₂ : [ (X ⊗₀ Y) ⊗₀ unit ⇒ X ⊗₀ Y ]⟨
                   α⇒               ⇒⟨ X ⊗₀ (Y ⊗₀ unit) ⟩
                   id ⊗₁ ρ⇒
                 ≈ ρ⇒
                 ⟩
    coherence₂ = from-≈ coherence-iso₂

    coherence-inv₂ : [ X ⊗₀ Y      ⇒ (X ⊗₀ Y) ⊗₀ unit ]⟨
                       id ⊗₁ ρ⇐    ⇒⟨ X ⊗₀ (Y ⊗₀ unit) ⟩
                       α⇐
                     ≈ ρ⇐
                     ⟩
    coherence-inv₂ = to-≈ coherence-iso₂

  -- A third coherence condition (Lemma 2.3)

  coherence₃ : [ unit ⊗₀ unit ⇒ unit ]⟨ λ⇒ ≈ ρ⇒ ⟩
  coherence₃ = push-eq unitorˡ-naturalIsomorphism (begin
    C.id ⊗₁ λ⇒               ≈˘⟨ cancelʳ associator.isoʳ ⟩
    (C.id ⊗₁ λ⇒ ∘ α⇒) ∘ α⇐   ≈⟨ triangle ⟩∘⟨refl ⟩
    ρ⇒ ⊗₁ C.id ∘ α⇐          ≈⟨ unitor-coherenceʳ ⟩∘⟨refl ⟩
    ρ⇒ ∘ α⇐                  ≈˘⟨ coherence₂ ⟩∘⟨refl ⟩
    (C.id ⊗₁ ρ⇒ ∘ α⇒) ∘ α⇐   ≈⟨ cancelʳ associator.isoʳ ⟩
    C.id ⊗₁ ρ⇒               ∎)
    where
      open MR C hiding (push-eq)
      open C.HomReasoning

  coherence-iso₃ : [ unit ⊗₀ unit ≅ unit ]⟨ unitorˡ ≈ unitorʳ ⟩
  coherence-iso₃ = ⌞ coherence₃ ⌟

  coherence-inv₃ : [ unit ⇒ unit ⊗₀ unit ]⟨ λ⇐ ≈ ρ⇐ ⟩
  coherence-inv₃ = to-≈ coherence-iso₃

open Kelly's public using
  ( coherence₁; coherence-iso₁; coherence-inv₁
  ; coherence₂; coherence-iso₂; coherence-inv₂
  ; coherence₃; coherence-iso₃; coherence-inv₃
  )

open Shorthands

private
  id⊗α-iso : (id {A} ⊗₁ α⇐ {P} {Q} {R}) ∘ (id ⊗₁ α⇒) ≈ id
  id⊗α-iso {A} {P} {Q} {R} = begin
    (id {A} ⊗₁ α⇐ {P} {Q} {R}) ∘ (id ⊗₁ α⇒)  ≈˘⟨ ⊗-distrib-over-∘ ⟩
    (id ∘ id) ⊗₁ (α⇐ ∘ α⇒)                   ≈⟨ identity² ⟩⊗⟨ associator.isoˡ ⟩
    id ⊗₁ id                                  ≈⟨ ⊗.identity ⟩
    id                                        ∎
    where open C.HomReasoning

assoc-shuffle
  : α⇒ {A ⊗₀ P} {Q} {R} ∘ (α⇐ {A} {P} {Q} ⊗₁ id) ∘ α⇐ {A} {P ⊗₀ Q} {R}
    ≈ α⇐ {A} {P} {Q ⊗₀ R} ∘ (id ⊗₁ α⇒ {P} {Q} {R})
assoc-shuffle = begin
  α⇒ ∘ (α⇐ ⊗₁ id) ∘ α⇐                                  ≈⟨ refl⟩∘⟨ Cancellers.insertʳ id⊗α-iso ⟩
  α⇒ ∘ (((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ α⇒)  ≈⟨ refl⟩∘⟨ pentagon-inv ⟩∘⟨refl ⟩
  α⇒ ∘ (α⇐ ∘ α⇐) ∘ (id ⊗₁ α⇒)                          ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ α⇐ ∘ α⇐ ∘ (id ⊗₁ α⇒)                            ≈⟨ Cancellers.cancelˡ associator.isoʳ ⟩
  α⇐ ∘ (id ⊗₁ α⇒)                                      ∎
  where
    open C.HomReasoning
    open MR C

unitorˡ-assoc-absorb : α⇒ ∘ (λ⇐ {A} ⊗₁ id {B}) ≈ λ⇐
unitorˡ-assoc-absorb = begin
  α⇒ ∘ (λ⇐ ⊗₁ id) ≈⟨ refl⟩∘⟨ Equiv.sym coherence-inv₁ ⟩
  α⇒ ∘ (α⇐ ∘ λ⇐) ≈⟨ Cancellers.cancelˡ associator.isoʳ ⟩
  λ⇐ ∎
  where
    open C.HomReasoning
    open MR C

unitorʳ-assoc-absorb : ρ⇒ ∘ α⇐ {A} {B} {unit} ≈ id ⊗₁ ρ⇒
unitorʳ-assoc-absorb = begin
  ρ⇒ ∘ α⇐                    ≈˘⟨ coherence₂ ⟩∘⟨refl ⟩
  (id ⊗₁ ρ⇒ ∘ α⇒) ∘ α⇐       ≈⟨ Cancellers.cancelʳ associator.isoʳ ⟩
  id ⊗₁ ρ⇒                   ∎
  where
    open C.HomReasoning
    open MR C

module Structural where
  open import Categories.Category.Monoidal.Reasoning MC
  open TensorIdentity using (id⊗id; ⊗id-∘)
  open MR C

  cancel-middle : ∀ {A B C D}
    {prefix : B ⇒ D} {from : C ⇒ B} {to : B ⇒ C} {suffix : A ⇒ B} →
    from ∘ to ≈ id → (prefix ∘ from) ∘ (to ∘ suffix) ≈ prefix ∘ suffix
  cancel-middle {prefix = prefix} {from = from} {to = to} {suffix = suffix} from∘to = begin
    (prefix ∘ from) ∘ (to ∘ suffix)
      ≈⟨ assoc ⟩
    prefix ∘ (from ∘ (to ∘ suffix))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    prefix ∘ ((from ∘ to) ∘ suffix)
      ≈⟨ refl⟩∘⟨ from∘to ⟩∘⟨refl ⟩
    prefix ∘ (id ∘ suffix)
      ≈⟨ refl⟩∘⟨ identityˡ ⟩
    prefix ∘ suffix
      ∎

  α-slide : ∀ {A P Q Z} {h : P ⇒ Q} →
    (id {A} ⊗₁ (h ⊗₁ id {Z})) ∘ α⇒ {A} {P} {Z}
    ≈ α⇒ {A} {Q} {Z} ∘ ((id {A} ⊗₁ h) ⊗₁ id {Z})
  α-slide = ⟺ assoc-commute-from

  α-sweep : ∀ {Y B P Q} {k : P ⇒ Q} →
    α⇒ {Y} {B} {Q} ∘ (id {Y ⊗₀ B} ⊗₁ k)
      ≈ (id {Y} ⊗₁ (id {B} ⊗₁ k)) ∘ α⇒ {Y} {B} {P}
  α-sweep {Y} {B} {P} {Q} {k} = begin
    α⇒ {Y} {B} {Q} ∘ (id {Y ⊗₀ B} ⊗₁ k)
      ≈˘⟨ refl⟩∘⟨ (id⊗id ⟩⊗⟨refl) ⟩
    α⇒ {Y} {B} {Q} ∘ ((id {Y} ⊗₁ id {B}) ⊗₁ k)
      ≈⟨ assoc-commute-from ⟩
    (id {Y} ⊗₁ (id {B} ⊗₁ k)) ∘ α⇒ {Y} {B} {P}
      ∎

  α⊗id-cancel : ∀ {A B C Z} →
    (α⇒ {A} {B} {C} ⊗₁ id {Z}) ∘ (α⇐ {A} {B} {C} ⊗₁ id {Z}) ≈ id
  α⊗id-cancel = ⊗-cancel associator.isoʳ identity²

  α-inner-slide : ∀ {A X P Q Z} {h : P ⇒ Q} →
    ((id {A} ⊗₁ (id {X} ⊗₁ h)) ⊗₁ id {Z})
      ∘ (α⇒ {A} {X} {P} ⊗₁ id {Z})
    ≈ (α⇒ {A} {X} {Q} ⊗₁ id {Z})
        ∘ ((id {A ⊗₀ X} ⊗₁ h) ⊗₁ id {Z})
  α-inner-slide {A} {X} {P} {Q} {Z} {h} = begin
    ((id {A} ⊗₁ (id {X} ⊗₁ h)) ⊗₁ id {Z})
      ∘ (α⇒ {A} {X} {P} ⊗₁ id {Z})
      ≈˘⟨ ⊗id-∘ ⟩
    ((id {A} ⊗₁ (id {X} ⊗₁ h)) ∘ α⇒ {A} {X} {P}) ⊗₁ id {Z}
      ≈˘⟨ assoc-commute-from {f = id {A}} {g = id {X}} {h = h} ⟩⊗⟨refl ⟩
    (α⇒ {A} {X} {Q} ∘ ((id {A} ⊗₁ id {X}) ⊗₁ h)) ⊗₁ id {Z}
      ≈⟨ (refl⟩∘⟨ id⊗id ⟩⊗⟨refl) ⟩⊗⟨refl ⟩
    (α⇒ {A} {X} {Q} ∘ (id {A ⊗₀ X} ⊗₁ h)) ⊗₁ id {Z}
      ≈⟨ ⊗id-∘ ⟩
    (α⇒ {A} {X} {Q} ⊗₁ id {Z})
      ∘ ((id {A ⊗₀ X} ⊗₁ h) ⊗₁ id {Z})
      ∎

  α-inner : ∀ {A X P Q Z} {h : P ⇒ Q} →
    (id {A} ⊗₁ ((id {X} ⊗₁ h) ⊗₁ id {Z}))
      ∘ α⇒ {A} {X ⊗₀ P} {Z}
      ∘ (α⇒ {A} {X} {P} ⊗₁ id {Z})
    ≈ α⇒ {A} {X ⊗₀ Q} {Z}
        ∘ (α⇒ {A} {X} {Q} ⊗₁ id {Z})
        ∘ ((id {A ⊗₀ X} ⊗₁ h) ⊗₁ id {Z})
  α-inner {A} {X} {P} {Q} {Z} {h} = begin
    (id {A} ⊗₁ ((id {X} ⊗₁ h) ⊗₁ id {Z}))
      ∘ α⇒ {A} {X ⊗₀ P} {Z}
      ∘ (α⇒ {A} {X} {P} ⊗₁ id {Z})
      ≈⟨ pullˡ α-slide ⟩
    (α⇒ {A} {X ⊗₀ Q} {Z}
      ∘ ((id {A} ⊗₁ (id {X} ⊗₁ h)) ⊗₁ id {Z}))
      ∘ (α⇒ {A} {X} {P} ⊗₁ id {Z})
      ≈⟨ assoc ⟩
    α⇒ {A} {X ⊗₀ Q} {Z}
      ∘ (((id {A} ⊗₁ (id {X} ⊗₁ h)) ⊗₁ id {Z})
      ∘ (α⇒ {A} {X} {P} ⊗₁ id {Z}))
      ≈⟨ refl⟩∘⟨ α-inner-slide ⟩
    α⇒ {A} {X ⊗₀ Q} {Z}
      ∘ (α⇒ {A} {X} {Q} ⊗₁ id {Z})
      ∘ ((id {A ⊗₀ X} ⊗₁ h) ⊗₁ id {Z})
      ∎

  ρ-peel : ∀ {A X Z} →
    (id {A} ⊗₁ (ρ⇒ {X} ⊗₁ id {Z}))
      ∘ α⇒ {A} {X ⊗₀ unit} {Z}
      ∘ (α⇒ {A} {X} {unit} ⊗₁ id {Z})
    ≈ α⇒ {A} {X} {Z} ∘ (ρ⇒ {A ⊗₀ X} ⊗₁ id {Z})
  ρ-peel {A} {X} {Z} = begin
    (id {A} ⊗₁ (ρ⇒ {X} ⊗₁ id {Z}))
      ∘ α⇒ {A} {X ⊗₀ unit} {Z}
      ∘ (α⇒ {A} {X} {unit} ⊗₁ id {Z})
      ≈⟨ pullˡ (⟺ (assoc-commute-from {f = id {A}} {g = ρ⇒ {X}} {h = id {Z}})) ⟩
    (α⇒ {A} {X} {Z} ∘ ((id {A} ⊗₁ ρ⇒ {X}) ⊗₁ id {Z}))
      ∘ (α⇒ {A} {X} {unit} ⊗₁ id {Z})
      ≈⟨ assoc ⟩
    α⇒ {A} {X} {Z}
      ∘ (((id {A} ⊗₁ ρ⇒ {X}) ⊗₁ id {Z})
      ∘ (α⇒ {A} {X} {unit} ⊗₁ id {Z}))
      ≈˘⟨ refl⟩∘⟨ ⊗id-∘ ⟩
    α⇒ {A} {X} {Z}
      ∘ ((id {A} ⊗₁ ρ⇒ {X}) ∘ α⇒ {A} {X} {unit}) ⊗₁ id {Z}
      ≈⟨ refl⟩∘⟨ coherence₂ ⟩⊗⟨refl ⟩
    α⇒ {A} {X} {Z} ∘ (ρ⇒ {A ⊗₀ X} ⊗₁ id {Z})
      ∎

  triangle-inv : ∀ {A Z} →
    α⇒ {A} {unit} {Z} ∘ (ρ⇐ {A} ⊗₁ id {Z})
      ≈ id {A} ⊗₁ λ⇐ {Z}
  triangle-inv {A} {Z} = begin
    α⇒ {A} {unit} {Z} ∘ (ρ⇐ {A} ⊗₁ id {Z})
      ≈˘⟨ switch-tofromˡ (associator {A} {unit} {Z})
            (MonoidalUtilities.triangle-inv MC) ⟩
    id {A} ⊗₁ λ⇐ {Z}
      ∎

  α-unit : ∀ {A B Z} →
    α⇒ {A} {B} {unit ⊗₀ Z}
      ∘ α⇒ {A ⊗₀ B} {unit} {Z}
      ∘ (ρ⇐ ⊗₁ id {Z})
      ∘ α⇐ {A} {B} {Z}
    ≈ id {A} ⊗₁ (id {B} ⊗₁ λ⇐ {Z})
  α-unit {A} {B} {Z} = begin
    α⇒ {A} {B} {unit ⊗₀ Z}
      ∘ α⇒ {A ⊗₀ B} {unit} {Z}
      ∘ (ρ⇐ {A ⊗₀ B} ⊗₁ id {Z})
      ∘ α⇐ {A} {B} {Z}
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    α⇒ {A} {B} {unit ⊗₀ Z}
      ∘ (α⇒ {A ⊗₀ B} {unit} {Z}
      ∘ (ρ⇐ {A ⊗₀ B} ⊗₁ id {Z}))
      ∘ α⇐ {A} {B} {Z}
      ≈⟨ refl⟩∘⟨ (triangle-inv {A = A ⊗₀ B} {Z = Z} ⟩∘⟨refl) ⟩
    α⇒ {A} {B} {unit ⊗₀ Z}
      ∘ (id {A ⊗₀ B} ⊗₁ λ⇐ {Z})
      ∘ α⇐ {A} {B} {Z}
      ≈˘⟨ refl⟩∘⟨ (id⊗id {A} {B} ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    α⇒ {A} {B} {unit ⊗₀ Z}
      ∘ ((id {A} ⊗₁ id {B}) ⊗₁ λ⇐ {Z})
      ∘ α⇐ {A} {B} {Z}
      ≈˘⟨ refl⟩∘⟨ assoc-commute-to {f = id {A}} {g = id {B}} {h = λ⇐ {Z}} ⟩
    α⇒ {A} {B} {unit ⊗₀ Z}
      ∘ α⇐ {A} {B} {unit ⊗₀ Z}
      ∘ (id {A} ⊗₁ (id {B} ⊗₁ λ⇐ {Z}))
      ≈⟨ cancelˡ associator.isoʳ ⟩
    id {A} ⊗₁ (id {B} ⊗₁ λ⇐ {Z})
      ∎

  assoc-to-coherence : ∀ {A B C D} →
    (id {A} ⊗₁ α⇐ {B} {C} {D})
      ∘ α⇒ {A} {B} {C ⊗₀ D}
    ≈ α⇒ {A} {B ⊗₀ C} {D}
        ∘ (α⇒ {A} {B} {C} ⊗₁ id {D})
        ∘ α⇐ {A ⊗₀ B} {C} {D}
  assoc-to-coherence {A} {B} {C} {D} = begin
    (id {A} ⊗₁ α⇐ {B} {C} {D}) ∘ α⇒ {A} {B} {C ⊗₀ D}
      ≈⟨ conjugate-from
           (associator {A ⊗₀ B} {C} {D})
           (idᵢ {A} ⊗ᵢ associator {B} {C} {D})
           {f = α⇒ {A} {B} {C ⊗₀ D}}
           {g = α⇒ {A} {B ⊗₀ C} {D} ∘ (α⇒ {A} {B} {C} ⊗₁ id {D})}
           (⟺ (pentagon {X = A} {Y = B} {Z = C} {W = D})) ⟩
    (α⇒ {A} {B ⊗₀ C} {D} ∘ (α⇒ {A} {B} {C} ⊗₁ id {D}))
      ∘ α⇐ {A ⊗₀ B} {C} {D}
      ≈⟨ assoc ⟩
    α⇒ {A} {B ⊗₀ C} {D}
      ∘ (α⇒ {A} {B} {C} ⊗₁ id {D})
      ∘ α⇐ {A ⊗₀ B} {C} {D}
      ∎

  assoc-peel : ∀ {A B C D} →
    (id {A} ⊗₁ α⇒ {B} {C} {D})
      ∘ α⇒ {A} {B ⊗₀ C} {D}
    ≈ α⇒ {A} {B} {C ⊗₀ D}
        ∘ α⇒ {A ⊗₀ B} {C} {D}
        ∘ (α⇐ {A} {B} {C} ⊗₁ id {D})
  assoc-peel {A} {B} {C} {D} =
    conjugate-to
      (associator {A} {B ⊗₀ C} {D})
      (associator {A} {B} {C ⊗₀ D})
      {f = id {A} ⊗₁ α⇒ {B} {C} {D}}
      {g = α⇒ {A ⊗₀ B} {C} {D}
        ∘ (α⇐ {A} {B} {C} ⊗₁ id {D})}
      (⟺ (assoc-shuffle {A = A} {P = B} {Q = C} {R = D}) ○ sym-assoc)

  α-peel⊗id : ∀ {A B C D E} →
    (id {A} ⊗₁ (α⇒ {B} {C} {D} ⊗₁ id {E}))
      ∘ α⇒ {A} {(B ⊗₀ C) ⊗₀ D} {E}
      ∘ (α⇒ {A} {B ⊗₀ C} {D} ⊗₁ id {E})
    ≈ α⇒ {A} {B ⊗₀ (C ⊗₀ D)} {E}
        ∘ (α⇒ {A} {B} {C ⊗₀ D} ⊗₁ id {E})
        ∘ (α⇒ {A ⊗₀ B} {C} {D} ⊗₁ id {E})
        ∘ ((α⇐ {A} {B} {C} ⊗₁ id {D}) ⊗₁ id {E})
  α-peel⊗id {A} {B} {C} {D} {E} = begin
    (id {A} ⊗₁ (α⇒ {B} {C} {D} ⊗₁ id {E}))
      ∘ α⇒ {A} {(B ⊗₀ C) ⊗₀ D} {E}
      ∘ (α⇒ {A} {B ⊗₀ C} {D} ⊗₁ id {E})
      ≈⟨ pullˡ α-slide ⟩
    (α⇒ {A} {B ⊗₀ (C ⊗₀ D)} {E}
      ∘ ((id {A} ⊗₁ α⇒ {B} {C} {D}) ⊗₁ id {E}))
      ∘ (α⇒ {A} {B ⊗₀ C} {D} ⊗₁ id {E})
      ≈⟨ assoc ⟩
    α⇒ {A} {B ⊗₀ (C ⊗₀ D)} {E}
      ∘ (((id {A} ⊗₁ α⇒ {B} {C} {D}) ⊗₁ id {E})
      ∘ (α⇒ {A} {B ⊗₀ C} {D} ⊗₁ id {E}))
      ≈˘⟨ refl⟩∘⟨ ⊗id-∘ ⟩
    α⇒ {A} {B ⊗₀ (C ⊗₀ D)} {E}
      ∘ (((id {A} ⊗₁ α⇒ {B} {C} {D})
      ∘ α⇒ {A} {B ⊗₀ C} {D}) ⊗₁ id {E})
      ≈⟨ refl⟩∘⟨ (assoc-peel {A} {B} {C} {D} ⟩⊗⟨refl) ⟩
    α⇒ {A} {B ⊗₀ (C ⊗₀ D)} {E}
      ∘ ((α⇒ {A} {B} {C ⊗₀ D}
      ∘ α⇒ {A ⊗₀ B} {C} {D}
      ∘ (α⇐ {A} {B} {C} ⊗₁ id {D})) ⊗₁ id {E})
      ≈⟨ refl⟩∘⟨ ⊗id-∘ ⟩
    α⇒ {A} {B ⊗₀ (C ⊗₀ D)} {E}
      ∘ ((α⇒ {A} {B} {C ⊗₀ D} ⊗₁ id {E})
      ∘ ((α⇒ {A ⊗₀ B} {C} {D}
      ∘ (α⇐ {A} {B} {C} ⊗₁ id {D})) ⊗₁ id {E}))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗id-∘ ⟩
    α⇒ {A} {B ⊗₀ (C ⊗₀ D)} {E}
      ∘ (α⇒ {A} {B} {C ⊗₀ D} ⊗₁ id {E})
      ∘ (α⇒ {A ⊗₀ B} {C} {D} ⊗₁ id {E})
      ∘ ((α⇐ {A} {B} {C} ⊗₁ id {D}) ⊗₁ id {E})
      ∎

  pentagon-tail : ∀ {A B C D} →
    α⇐ {A} {B} {C ⊗₀ D}
      ∘ (id {A} ⊗₁ α⇒ {B} {C} {D})
      ∘ α⇒ {A} {B ⊗₀ C} {D}
      ∘ (α⇒ {A} {B} {C} ⊗₁ id {D})
    ≈ α⇒ {A ⊗₀ B} {C} {D}
  pentagon-tail {A} {B} {C} {D} = begin
    α⇐ {A} {B} {C ⊗₀ D}
      ∘ (id {A} ⊗₁ α⇒ {B} {C} {D})
      ∘ α⇒ {A} {B ⊗₀ C} {D}
      ∘ (α⇒ {A} {B} {C} ⊗₁ id {D})
      ≈⟨ refl⟩∘⟨ pentagon {X = A} {Y = B} {Z = C} {W = D} ⟩
    α⇐ {A} {B} {C ⊗₀ D}
      ∘ α⇒ {A} {B} {C ⊗₀ D}
      ∘ α⇒ {A ⊗₀ B} {C} {D}
      ≈⟨ sym-assoc ⟩
    (α⇐ {A} {B} {C ⊗₀ D} ∘ α⇒ {A} {B} {C ⊗₀ D})
      ∘ α⇒ {A ⊗₀ B} {C} {D}
      ≈⟨ associator.isoˡ ⟩∘⟨refl ⟩
    id ∘ α⇒ {A ⊗₀ B} {C} {D}
      ≈⟨ identityˡ ⟩
    α⇒ {A ⊗₀ B} {C} {D}
      ∎

  assoc-pair-coherence : ∀ {A B C D E} →
      α⇒ {A} {B ⊗₀ C} {D ⊗₀ E}
        ∘ (α⇒ {A} {B} {C} ⊗₁ id {D ⊗₀ E})
        ∘ α⇒ {(A ⊗₀ B) ⊗₀ C} {D} {E}
    ≈ (id {A} ⊗₁ α⇐ {B} {C} {D ⊗₀ E})
        ∘ α⇒ {A} {B} {C ⊗₀ (D ⊗₀ E)}
        ∘ (id {A ⊗₀ B} ⊗₁ α⇒ {C} {D} {E})
        ∘ α⇒ {A ⊗₀ B} {C ⊗₀ D} {E}
        ∘ (α⇒ {A ⊗₀ B} {C} {D} ⊗₁ id {E})
  assoc-pair-coherence {A} {B} {C} {D} {E} = begin
    α⇒ {A} {B ⊗₀ C} {D ⊗₀ E}
      ∘ (α⇒ {A} {B} {C} ⊗₁ id {D ⊗₀ E})
      ∘ α⇒ {(A ⊗₀ B) ⊗₀ C} {D} {E}
      ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ pentagon-tail {A = A ⊗₀ B} {B = C} {C = D} {D = E}) ⟩
    α⇒ {A} {B ⊗₀ C} {D ⊗₀ E}
      ∘ (α⇒ {A} {B} {C} ⊗₁ id {D ⊗₀ E})
      ∘ (α⇐ {A ⊗₀ B} {C} {D ⊗₀ E}
      ∘ (id {A ⊗₀ B} ⊗₁ α⇒ {C} {D} {E})
      ∘ α⇒ {A ⊗₀ B} {C ⊗₀ D} {E}
      ∘ (α⇒ {A ⊗₀ B} {C} {D} ⊗₁ id {E}))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    α⇒ {A} {B ⊗₀ C} {D ⊗₀ E}
      ∘ ((α⇒ {A} {B} {C} ⊗₁ id {D ⊗₀ E})
      ∘ α⇐ {A ⊗₀ B} {C} {D ⊗₀ E})
      ∘ (id {A ⊗₀ B} ⊗₁ α⇒ {C} {D} {E})
      ∘ α⇒ {A ⊗₀ B} {C ⊗₀ D} {E}
      ∘ (α⇒ {A ⊗₀ B} {C} {D} ⊗₁ id {E})
      ≈⟨ sym-assoc ⟩
    (α⇒ {A} {B ⊗₀ C} {D ⊗₀ E}
      ∘ (α⇒ {A} {B} {C} ⊗₁ id {D ⊗₀ E})
      ∘ α⇐ {A ⊗₀ B} {C} {D ⊗₀ E})
      ∘ (id {A ⊗₀ B} ⊗₁ α⇒ {C} {D} {E})
      ∘ α⇒ {A ⊗₀ B} {C ⊗₀ D} {E}
      ∘ (α⇒ {A ⊗₀ B} {C} {D} ⊗₁ id {E})
      ≈⟨ ⟺ (assoc-to-coherence {A} {B} {C} {D ⊗₀ E}) ⟩∘⟨refl ⟩
    ((id {A} ⊗₁ α⇐ {B} {C} {D ⊗₀ E})
      ∘ α⇒ {A} {B} {C ⊗₀ (D ⊗₀ E)})
      ∘ (id {A ⊗₀ B} ⊗₁ α⇒ {C} {D} {E})
      ∘ α⇒ {A ⊗₀ B} {C ⊗₀ D} {E}
      ∘ (α⇒ {A ⊗₀ B} {C} {D} ⊗₁ id {E})
      ≈⟨ assoc ⟩
    (id {A} ⊗₁ α⇐ {B} {C} {D ⊗₀ E})
      ∘ α⇒ {A} {B} {C ⊗₀ (D ⊗₀ E)}
      ∘ (id {A ⊗₀ B} ⊗₁ α⇒ {C} {D} {E})
      ∘ α⇒ {A ⊗₀ B} {C ⊗₀ D} {E}
      ∘ (α⇒ {A ⊗₀ B} {C} {D} ⊗₁ id {E})
      ∎

  pentagon′ : ∀ {A B C D} →
      α⇒ {A ⊗₀ B} {C} {D}
        ∘ (α⇐ {A} {B} {C} ⊗₁ id {D})
    ≈ α⇐ {A} {B} {C ⊗₀ D}
        ∘ (id {A} ⊗₁ α⇒ {B} {C} {D})
        ∘ α⇒ {A} {B ⊗₀ C} {D}
  pentagon′ {A} {B} {C} {D} = begin
    α⇒ {A ⊗₀ B} {C} {D}
      ∘ (α⇐ {A} {B} {C} ⊗₁ id {D})
      ≈⟨ switch-tofromʳ (associator {A} {B ⊗₀ C} {D})
           (assoc ○ assoc-shuffle {A = A} {P = B} {Q = C} {R = D}) ⟩
    (α⇐ {A} {B} {C ⊗₀ D} ∘ (id {A} ⊗₁ α⇒ {B} {C} {D}))
      ∘ α⇒ {A} {B ⊗₀ C} {D}
      ≈⟨ assoc ⟩
    α⇐ {A} {B} {C ⊗₀ D}
      ∘ (id {A} ⊗₁ α⇒ {B} {C} {D})
      ∘ α⇒ {A} {B ⊗₀ C} {D}
      ∎

  λ-left : ∀ {P Q} →
    α⇒ {unit} {P} {Q} ∘ (λ⇐ ⊗₁ id {Q})
      ≈ λ⇐ {P ⊗₀ Q}
  λ-left = unitorˡ-assoc-absorb

  ρ-sweep : ∀ {X Y L} {h : L ⇒ unit} →
    ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ h) ∘ α⇐ {X} {Y} {L}
      ≈ id {X} ⊗₁ (ρ⇒ ∘ (id {Y} ⊗₁ h))
  ρ-sweep {X} {Y} {L} {h} = begin
    ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ h) ∘ α⇐ {X} {Y} {L}
      ≈⟨ refl⟩∘⟨ ρ-nat ⟩
    ρ⇒ ∘ α⇐ {X} {Y} {unit} ∘ (id {X} ⊗₁ (id {Y} ⊗₁ h))
      ≈⟨ pullˡ ρ-coh ⟩
    (id {X} ⊗₁ ρ⇒) ∘ (id {X} ⊗₁ (id {Y} ⊗₁ h))
      ≈⟨ merge₂ˡ ⟩
    id {X} ⊗₁ (ρ⇒ ∘ (id {Y} ⊗₁ h))
      ∎
    where
      ρ-nat :
        (id {X ⊗₀ Y} ⊗₁ h) ∘ α⇐ {X} {Y} {L}
        ≈ α⇐ {X} {Y} {unit} ∘ (id {X} ⊗₁ (id {Y} ⊗₁ h))
      ρ-nat = begin
        (id {X ⊗₀ Y} ⊗₁ h) ∘ α⇐ {X} {Y} {L}
          ≈˘⟨ ((id⊗id {X} {Y}) ⟩⊗⟨refl) ⟩∘⟨refl ⟩
        ((id {X} ⊗₁ id {Y}) ⊗₁ h) ∘ α⇐ {X} {Y} {L}
          ≈˘⟨ assoc-commute-to {f = id {X}} {g = id {Y}} {h = h} ⟩
        α⇐ {X} {Y} {unit} ∘ (id {X} ⊗₁ (id {Y} ⊗₁ h))
          ∎

      ρ-coh :
        ρ⇒ ∘ α⇐ {X} {Y} {unit}
        ≈ id {X} ⊗₁ ρ⇒
      ρ-coh = ⟺ (switch-fromtoʳ associator coherence₂)

  ρ-sweep-open : ∀ {X Y L} {h : L ⇒ unit} →
    (id {X} ⊗₁ (ρ⇒ ∘ (id {Y} ⊗₁ h)))
      ∘ α⇒ {X} {Y} {L}
    ≈ ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ h)
  ρ-sweep-open {X} {Y} {L} {h} = begin
    (id {X} ⊗₁ (ρ⇒ ∘ (id {Y} ⊗₁ h))) ∘ α⇒ {X} {Y} {L}
      ≈˘⟨ ρ-sweep {X} {Y} {L} {h} ⟩∘⟨refl ⟩
    (ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ h) ∘ α⇐ {X} {Y} {L})
      ∘ α⇒ {X} {Y} {L}
      ≈⟨ assoc²βε ⟩
    ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ h)
      ∘ (α⇐ {X} {Y} {L} ∘ α⇒ {X} {Y} {L})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ associator.isoˡ ⟩
    ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ h) ∘ id
      ≈⟨ refl⟩∘⟨ identityʳ ⟩
    ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ h)
      ∎

  cap-reassoc : ∀ {A P Q B} {cap : P ⊗₀ Q ⇒ unit} →
    (id {A} ⊗₁ (λ⇒ ∘ (cap ⊗₁ id {B}) ∘ α⇐))
      ∘ α⇒ {A} {P} {Q ⊗₀ B}
    ≈ ((ρ⇒ ⊗₁ id {B}) ∘ ((id {A} ⊗₁ cap) ⊗₁ id {B}))
        ∘ (α⇒ {A} {P} {Q} ⊗₁ id {B})
        ∘ α⇐ {A ⊗₀ P} {Q} {B}
  cap-reassoc {A} {P} {Q} {B} {cap} = begin
    (id {A} ⊗₁ (λ⇒ ∘ (cap ⊗₁ id {B}) ∘ α⇐))
      ∘ α⇒ {A} {P} {Q ⊗₀ B}
      ≈⟨ cap-reassoc-core ⟩
    ((ρ⇒ ⊗₁ id {B}) ∘ ((id {A} ⊗₁ cap) ⊗₁ id {B}))
      ∘ (α⇒ {A} {P} {Q} ⊗₁ id {B})
      ∘ α⇐ {A ⊗₀ P} {Q} {B}
      ∎
    where
      cap-reassoc-core :
        (id {A} ⊗₁ (λ⇒ ∘ (cap ⊗₁ id {B}) ∘ α⇐))
          ∘ α⇒ {A} {P} {Q ⊗₀ B}
        ≈ ((ρ⇒ ⊗₁ id {B}) ∘ ((id {A} ⊗₁ cap) ⊗₁ id {B}))
          ∘ (α⇒ {A} {P} {Q} ⊗₁ id {B})
          ∘ α⇐ {A ⊗₀ P} {Q} {B}
      cap-reassoc-core =
        ((split₂ˡ ○ (refl⟩∘⟨ split₂ˡ)) ⟩∘⟨refl)
        ○ (assoc ○ (refl⟩∘⟨ assoc))
        ○ refl⟩∘⟨ refl⟩∘⟨ assoc-to-coherence
        ○ (refl⟩∘⟨ (sym-assoc ○ (⟺ assoc-commute-from ⟩∘⟨refl) ○ assoc))
        ○ ⟺ assoc
        ○ triangle ⟩∘⟨refl
        ○ ⟺ assoc
