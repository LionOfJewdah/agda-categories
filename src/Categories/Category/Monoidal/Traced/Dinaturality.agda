{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Traced using (Traced)

-- Strengthened dinaturality derived from the Joyal--Street--Verity trace axioms.

module Categories.Category.Monoidal.Traced.Dinaturality
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞} (T : Traced M) where

open Category 𝒞
open Traced T

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Category.Monoidal.Braided.Properties braided
  using () renaming (module Shorthands to BraidShorthands)
open Shorthands
open BraidShorthands

private
  variable
    A B C W X Y Z : Obj

  tensor-under : A ⊗₀ B ⇒ X ⊗₀ Y → (W ⊗₀ A) ⊗₀ B ⇒ (W ⊗₀ X) ⊗₀ Y
  tensor-under f = α⇐ ∘ (id ⊗₁ f) ∘ α⇒

private abstract
  tensor-under-resp-≈ : {f g : A ⊗₀ B ⇒ X ⊗₀ Y} →
    f ≈ g → tensor-under {W = W} f ≈ tensor-under g
  tensor-under-resp-≈ f≈g = refl⟩∘⟨ (refl⟩⊗⟨ f≈g) ⟩∘⟨refl

  tensor-under-∘ : {f : X ⊗₀ Y ⇒ B ⊗₀ C} {g : A ⊗₀ Z ⇒ X ⊗₀ Y} →
    tensor-under {W = W} f ∘ tensor-under g ≈ tensor-under (f ∘ g)
  tensor-under-∘ {f = f} {g} = begin
    (α⇐ ∘ (id ⊗₁ f) ∘ α⇒) ∘ α⇐ ∘ (id ⊗₁ g) ∘ α⇒  ≈⟨ center (cancelʳ associator.isoʳ) ⟩
    α⇐ ∘ (id ⊗₁ f) ∘ (id ⊗₁ g) ∘ α⇒             ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    α⇐ ∘ (id ⊗₁ (f ∘ g)) ∘ α⇒                    ∎

  tensor-under-factor : {f : X ⊗₀ Y ⇒ B ⊗₀ C} {g : A ⊗₀ Z ⇒ X ⊗₀ Y}
    {f′ : (W ⊗₀ X) ⊗₀ Y ⇒ (W ⊗₀ B) ⊗₀ C} →
    tensor-under {W = W} f ≈ f′ → tensor-under (f ∘ g) ≈ f′ ∘ tensor-under g
  tensor-under-factor f≈f′ = ⟺ tensor-under-∘ ○ (f≈f′ ⟩∘⟨refl)

  tensor-under-eval : {f : A ⊗₀ B ⇒ X ⊗₀ Y}
    {g : (W ⊗₀ A) ⊗₀ B ⇒ (W ⊗₀ X) ⊗₀ Y} →
    (id ⊗₁ f) ∘ α⇒ ≈ α⇒ ∘ g → tensor-under f ≈ g
  tensor-under-eval f-past-α = (refl⟩∘⟨ f-past-α) ○ cancelˡ associator.isoˡ

private
  tail-swap : (A ⊗₀ X) ⊗₀ Y ⇒ (A ⊗₀ Y) ⊗₀ X
  tail-swap = α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒

private abstract
  tail-braid-collapse :
    (id {A} ⊗₁ σ⇒ {X} {Y}) ∘ α⇒ ∘ (σ⇒ {X} {A} ⊗₁ id) ∘ α⇐ ≈ α⇒ ∘ σ⇒
  tail-braid-collapse = begin
    (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐      ≈⟨ assoc²εβ ⟩
    ((id ⊗₁ σ⇒) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))) ∘ α⇐  ≈⟨ hexagon₁ ⟩∘⟨refl ⟩
    (α⇒ ∘ (σ⇒ ∘ α⇒)) ∘ α⇐                  ≈⟨ pullʳ (cancelʳ associator.isoʳ) ⟩
    α⇒ ∘ σ⇒                                ∎

  tail-swap-assoc : tail-swap {A} {X} {Y ⊗₀ Z} ∘ α⇒
                    ≈ (α⇒ ⊗₁ id) ∘ tail-swap ∘ (tail-swap ⊗₁ id)
  tail-swap-assoc = begin
    tensor-under σ⇒ ∘ α⇒
      ≈˘⟨ tensor-under-resp-≈ (cancelˡ associator.isoˡ) ⟩∘⟨refl ⟩
    tensor-under (α⇐ ∘ α⇒ ∘ σ⇒) ∘ α⇒
      ≈˘⟨ tensor-under-resp-≈ (refl⟩∘⟨ tail-braid-collapse) ⟩∘⟨refl ⟩
    tensor-under (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
      ≈⟨ pushˡ (tensor-under-factor (tensor-under-eval assoc-to-coherence)) ⟩
    ((α⇒ ⊗₁ id) ∘ α⇐) ∘ tensor-under ((id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
      ≈⟨ refl⟩∘⟨ pushˡ (tensor-under-factor (tensor-under-eval (⟺ α⇒-id⊗-commute))) ⟩
    ((α⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ σ⇒) ∘ tensor-under (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (tensor-under-factor (⟺ assoc-from-coherence)) ⟩
    ((α⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ σ⇒) ∘ (α⇒ ∘ (α⇐ ⊗₁ id))
      ∘ tensor-under ((σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
      ≈⟨ assoc ⟩
    (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ (α⇒ ∘ (α⇐ ⊗₁ id))
      ∘ tensor-under ((σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (α⇐ ⊗₁ id)
      ∘ tensor-under ((σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
      ≈˘⟨ refl⟩∘⟨ assoc²βε ⟩
    (α⇒ ⊗₁ id) ∘ tail-swap ∘ (α⇐ ⊗₁ id)
      ∘ tensor-under ((σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (tensor-under-factor (tensor-under-eval (⟺ assoc-commute-from))) ⟩
    (α⇒ ⊗₁ id) ∘ tail-swap ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ⇒) ⊗₁ id)
      ∘ tensor-under α⇐ ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ tensor-under-eval assoc-to-coherence ⟩∘⟨refl ⟩
    (α⇒ ⊗₁ id) ∘ tail-swap ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ⇒) ⊗₁ id)
      ∘ ((α⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelʳ associator.isoˡ ⟩
    (α⇒ ⊗₁ id) ∘ tail-swap ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ⇒) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁³ ⟩
    (α⇒ ⊗₁ id) ∘ tail-swap ∘ (tail-swap ⊗₁ id)  ∎

private
  parameter-exchange : (((A ⊗₀ W) ⊗₀ X) ⊗₀ W) ⇒ (((A ⊗₀ W) ⊗₀ X) ⊗₀ W)
  parameter-exchange = (tail-swap ⊗₁ id) ∘ tail-swap ∘ (tail-swap ⊗₁ id)

private abstract
  tail-swap-cancel : tail-swap {A} {X} {Y} ∘ tail-swap ≈ id
  tail-swap-cancel = begin
    (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒
      ≈⟨ pullʳ (cancelInner associator.isoʳ) ⟩
    α⇐ ∘ (id ⊗₁ σ⇒) ∘ (id ⊗₁ σ⇒) ∘ α⇒  ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    α⇐ ∘ (id ⊗₁ (σ⇒ ∘ σ⇒)) ∘ α⇒        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ commutative) ⟩∘⟨refl ⟩
    α⇐ ∘ (id ⊗₁ id) ∘ α⇒                ≈⟨ refl⟩∘⟨ ⊗.identity ⟩∘⟨refl ⟩
    α⇐ ∘ id ∘ α⇒                        ≈⟨ refl⟩∘⟨ identityˡ ⟩
    α⇐ ∘ α⇒                             ≈⟨ associator.isoˡ ⟩
    id                                  ∎

  tail-swap-natural : {f : A ⇒ B} {g : W ⇒ X} {h : Y ⇒ Z} →
    tail-swap ∘ ((f ⊗₁ g) ⊗₁ h) ≈ ((f ⊗₁ h) ⊗₁ g) ∘ tail-swap
  tail-swap-natural {f = f} {g} {h} = begin
    (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒) ∘ ((f ⊗₁ g) ⊗₁ h)
      ≈⟨ pullʳ (pullʳ assoc-commute-from) ⟩
    α⇐ ∘ (id ⊗₁ σ⇒) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ extendʳ (parallel id-comm-sym σ⇒-comm) ⟩
    α⇐ ∘ (f ⊗₁ (h ⊗₁ g)) ∘ (id ⊗₁ σ⇒) ∘ α⇒  ≈⟨ extendʳ assoc-commute-to ⟩
    ((f ⊗₁ h) ⊗₁ g) ∘ tail-swap                         ∎

  parameter-exchange-trace : trace (parameter-exchange {A} {W} {X}) ≈ id
  parameter-exchange-trace = begin
    trace ((tail-swap ⊗₁ id) ∘ tail-swap ∘ (tail-swap ⊗₁ id))  ≈⟨ tightenₗ ⟩
    tail-swap ∘ trace (tail-swap ∘ (tail-swap ⊗₁ id))           ≈⟨ refl⟩∘⟨ tightenᵣ ⟩
    tail-swap ∘ trace tail-swap ∘ tail-swap                     ≈⟨ refl⟩∘⟨ superposing ⟩∘⟨refl ⟩
    tail-swap ∘ (id ⊗₁ trace σ⇒) ∘ tail-swap                    ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ yanking) ⟩∘⟨refl ⟩
    tail-swap ∘ (id ⊗₁ id) ∘ tail-swap                          ≈⟨ refl⟩∘⟨ ⊗.identity ⟩∘⟨refl ⟩
    tail-swap ∘ id ∘ tail-swap                                  ≈⟨ refl⟩∘⟨ identityˡ ⟩
    tail-swap ∘ tail-swap                                       ≈⟨ tail-swap-cancel ⟩
    id                                                          ∎

  parameter-exchange-coherence :
    (α⇒ ⊗₁ id) ∘ parameter-exchange {A} {W} {X}
    ≈ tail-swap {A} {W} {W ⊗₀ X} ∘ (id ⊗₁ σ⇒) ∘ α⇒
  parameter-exchange-coherence = begin
    (α⇒ ⊗₁ id) ∘ (tail-swap ⊗₁ id) ∘ tail-swap ∘ (tail-swap ⊗₁ id)
      ≈⟨ pullˡ merge₁ˡ ⟩
    ((α⇒ ∘ tail-swap) ⊗₁ id) ∘ tail-swap ∘ (tail-swap ⊗₁ id)
      ≈⟨ (cancelˡ associator.isoʳ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    (((id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id) ∘ tail-swap ∘ (tail-swap ⊗₁ id)
      ≈⟨ pushˡ split₁ˡ ⟩
    ((id ⊗₁ σ⇒) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ tail-swap ∘ (tail-swap ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ tail-swap-assoc ⟩
    ((id ⊗₁ σ⇒) ⊗₁ id) ∘ tail-swap ∘ α⇒
      ≈⟨ sym-assoc ⟩
    (((id ⊗₁ σ⇒) ⊗₁ id) ∘ tail-swap) ∘ α⇒
      ≈˘⟨ tail-swap-natural ⟩∘⟨refl ⟩
    (tail-swap ∘ ((id ⊗₁ id) ⊗₁ σ⇒)) ∘ α⇒
      ≈⟨ assoc ⟩
    tail-swap ∘ ((id ⊗₁ id) ⊗₁ σ⇒) ∘ α⇒
      ≈⟨ refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    tail-swap ∘ (id ⊗₁ σ⇒) ∘ α⇒  ∎

-- A feedback map carrying a free parameter slides through a trace.
parameter-slide : {f : A ⊗₀ Y ⇒ B ⊗₀ X} {g : W ⊗₀ X ⇒ Y} →
  trace (f ∘ (id ⊗₁ g) ∘ α⇒)
  ≈ trace ((id ⊗₁ (g ∘ σ⇒ {X} {W})) ∘ (α⇒ ∘ (f ⊗₁ id))
      ∘ (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒))
parameter-slide {A} {Y} {B} {X} {W} {f = f} {g = g} = begin
  trace parameter-first
    ≈˘⟨ trace⟨ inner-exchange ⟩ ⟩
  trace (trace (α⇐ ∘ (feedback-first ∘ (id ⊗₁ parameter-feedback)) ∘ α⇒))
    ≈⟨ vanishing₂ ⟩
  trace (feedback-first ∘ (id ⊗₁ parameter-feedback))
    ≈⟨ slide ⟩
  trace ((id ⊗₁ parameter-feedback) ∘ feedback-first)
    ≈⟨ trace⟨ refl⟩∘⟨ sym-assoc ⟩ ⟩
  trace ((id ⊗₁ parameter-feedback) ∘ (α⇒ ∘ (f ⊗₁ id)) ∘ tail-swap)  ∎
  where
    parameter-first : (A ⊗₀ W) ⊗₀ X ⇒ B ⊗₀ X
    parameter-first = f ∘ (id ⊗₁ g) ∘ α⇒

    parameter-feedback : X ⊗₀ W ⇒ Y
    parameter-feedback = g ∘ σ⇒

    feedback-first : (A ⊗₀ W) ⊗₀ Y ⇒ B ⊗₀ (X ⊗₀ W)
    feedback-first = α⇒ ∘ (f ⊗₁ id) ∘ tail-swap

    open-feedback : α⇐ ∘ feedback-first ≈ (f ⊗₁ id) ∘ tail-swap
    open-feedback = cancelˡ associator.isoˡ

    parameter-swap-natural :
      tail-swap {A} {W} {Y} ∘ (id ⊗₁ g)
      ≈ ((id ⊗₁ g) ⊗₁ id) ∘ tail-swap {A} {W} {W ⊗₀ X}
    parameter-swap-natural =
      (refl⟩∘⟨ (⟺ ⊗.identity ⟩⊗⟨refl)) ○ tail-swap-natural

    parameter-past-swap :
      tail-swap {A} {W} {Y} ∘ (id ⊗₁ parameter-feedback)
      ≈ ((id ⊗₁ g) ⊗₁ id) ∘ tail-swap {A} {W} {W ⊗₀ X} ∘ (id ⊗₁ σ⇒ {X} {W})
    parameter-past-swap = begin
      tail-swap ∘ (id ⊗₁ parameter-feedback)
        ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
      tail-swap ∘ (id ⊗₁ g) ∘ (id ⊗₁ σ⇒)
        ≈⟨ extendʳ parameter-swap-natural ⟩
      ((id ⊗₁ g) ⊗₁ id) ∘ tail-swap ∘ (id ⊗₁ σ⇒)  ∎

    feedback-swap :
      tail-swap {A} {W} {Y} ∘ (id ⊗₁ parameter-feedback) ∘ α⇒
      ≈ ((id ⊗₁ g) ⊗₁ id) ∘ tail-swap {A} {W} {W ⊗₀ X}
          ∘ (id ⊗₁ σ⇒ {X} {W}) ∘ α⇒
    feedback-swap = begin
      tail-swap ∘ (id ⊗₁ parameter-feedback) ∘ α⇒
        ≈⟨ extendʳ parameter-past-swap ⟩
      ((id ⊗₁ g) ⊗₁ id) ∘ ((tail-swap ∘ (id ⊗₁ σ⇒)) ∘ α⇒)
        ≈⟨ refl⟩∘⟨ assoc ⟩
      ((id ⊗₁ g) ⊗₁ id) ∘ tail-swap ∘ (id ⊗₁ σ⇒) ∘ α⇒  ∎

    factor-exchange :
      α⇐ ∘ (feedback-first ∘ (id ⊗₁ parameter-feedback)) ∘ α⇒
      ≈ (parameter-first ⊗₁ id) ∘ parameter-exchange
    factor-exchange = begin
      α⇐ ∘ (feedback-first ∘ (id ⊗₁ parameter-feedback)) ∘ α⇒
        ≈⟨ pull-first open-feedback ⟩
      ((f ⊗₁ id) ∘ tail-swap) ∘ ((id ⊗₁ parameter-feedback) ∘ α⇒)
        ≈⟨ assoc ⟩
      (f ⊗₁ id) ∘ tail-swap ∘ (id ⊗₁ parameter-feedback) ∘ α⇒
        ≈⟨ refl⟩∘⟨ feedback-swap ⟩
      (f ⊗₁ id) ∘ ((id ⊗₁ g) ⊗₁ id) ∘ tail-swap ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ parameter-exchange-coherence ⟩
      (f ⊗₁ id) ∘ ((id ⊗₁ g) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ parameter-exchange
        ≈⟨ pullˡ merge₁ˡ ⟩
      ((f ∘ (id ⊗₁ g)) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ parameter-exchange
        ≈⟨ pullˡ merge₁ˡ ⟩
      (((f ∘ (id ⊗₁ g)) ∘ α⇒) ⊗₁ id) ∘ parameter-exchange
        ≈⟨ (assoc ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      (parameter-first ⊗₁ id) ∘ parameter-exchange  ∎

    inner-exchange :
      trace (α⇐ ∘ (feedback-first ∘ (id ⊗₁ parameter-feedback)) ∘ α⇒)
      ≈ parameter-first
    inner-exchange = begin
      trace (α⇐ ∘ (feedback-first ∘ (id ⊗₁ parameter-feedback)) ∘ α⇒)
        ≈⟨ trace⟨ factor-exchange ⟩ ⟩
      trace ((parameter-first ⊗₁ id) ∘ parameter-exchange)  ≈⟨ tightenₗ ⟩
      parameter-first ∘ trace parameter-exchange           ≈⟨ refl⟩∘⟨ parameter-exchange-trace ⟩
      parameter-first ∘ id                                 ≈⟨ identityʳ ⟩
      parameter-first                                      ∎
