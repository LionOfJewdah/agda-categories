{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Tactic.Monoidal.Symmetric.Examples
  {o ℓ e : Level}
  {C : Category o ℓ e}
  {M : Monoidal C}
  (S : Symmetric M)
  (X Y Z : Category.Obj C)
  where

open import Data.Fin.Base using (Fin)
open import Data.Fin.Patterns using (0F; 1F; 2F)

open Category C using (Obj; _≈_)
open Monoidal M using (_⊗₀_; unit)
open import Categories.Tactic.Monoidal.Symmetric using (module Finite)
import Categories.Tactic.Monoidal.Expression as Expression
open Finite S

private
  module Expr = Expression.Core M
  open Expr using ([_↑]; idₑ; _∘ₑ_; _⊗ₑ_; α⇒ₑ; λ⇒ₑ; λ⇐ₑ; ρ⇒ₑ; ρ⇐ₑ; ⟦_⟧ₑ)
  module SExpr = Expr.SymmetricExpression S
  open SExpr using
    ( σₑ; σ⇒ₑ; σ⇐ₑ
    ; σ-natural; σ⇐-natural
    ; σ⇒-hexagon₁
    ; σ⇒-unitʳ; σ⇒-unitʳ-inv; σ⇐-unitʳ-inv; σ⇐-unitˡ
    ; σ⇐∘σ⇒; σ⇐≈σ⇒; σ²
    )

  atom : Fin 3 → Category.Obj C
  atom 0F = X
  atom 1F = Y
  atom 2F = Z

  open SolverFor atom renaming (solveᶠ to solve)

  double-braid : (‹ 0F › ⊗ᵒ ‹ 1F ›) ⇒ᶠ (‹ 0F › ⊗ᵒ ‹ 1F ›)
  double-braid = σᶠ ∘ᶠ σᶠ

  block-braid : ((‹ 0F › ⊗ᵒ ‹ 1F ›) ⊗ᵒ ‹ 2F ›) ⇒ᶠ (‹ 2F › ⊗ᵒ (‹ 0F › ⊗ᵒ ‹ 1F ›))
  block-braid = σᶠ

  block-stepwise : ((‹ 0F › ⊗ᵒ ‹ 1F ›) ⊗ᵒ ‹ 2F ›) ⇒ᶠ (‹ 2F › ⊗ᵒ (‹ 0F › ⊗ᵒ ‹ 1F ›))
  block-stepwise = α⇒ᶠ ∘ᶠ (σᶠ ⊗ᶠ idₘ) ∘ᶠ α⇐ᶠ ∘ᶠ (idₘ ⊗ᶠ σᶠ) ∘ᶠ α⇒ᶠ

  unit-braid : (‹ 0F › ⊗ᵒ I) ⇒ᶠ (I ⊗ᵒ ‹ 0F ›)
  unit-braid = σᶠ

  unit-swap : (‹ 0F › ⊗ᵒ I) ⇒ᶠ (I ⊗ᵒ ‹ 0F ›)
  unit-swap = λ⇐ᶠ ∘ᶠ ρ⇒ᶠ

  braid-braid : ⟦ double-braid ⟧ᵇ ≈ ⟦ idₘ {‹ 0F › ⊗ᵒ ‹ 1F ›} ⟧ᵇ
  braid-braid = solve double-braid idₘ

  braid-block : ⟦ block-braid ⟧ᵇ ≈ ⟦ block-stepwise ⟧ᵇ
  braid-block = solve block-braid block-stepwise

  braid-unit : ⟦ unit-braid ⟧ᵇ ≈ ⟦ unit-swap ⟧ᵇ
  braid-unit = solve unit-braid unit-swap

  braiding-natural-opaque :
    ∀ {A B D E}
      {f : Category._⇒_ C A B}
      {g : Category._⇒_ C D E} →
    ⟦ σₑ ∘ₑ ([ f ↑] ⊗ₑ [ g ↑]) ⟧ₑ
    ≈ ⟦ ([ g ↑] ⊗ₑ [ f ↑]) ∘ₑ σₑ ⟧ₑ
  braiding-natural-opaque {f = f} {g = g} =
    σ-natural {f = [ f ↑]} {g = [ g ↑]}

  inverse-braiding-natural-opaque :
    ∀ {A B D E}
      {f : Category._⇒_ C A B}
      {g : Category._⇒_ C D E} →
    ⟦ σ⇐ₑ ∘ₑ ([ g ↑] ⊗ₑ [ f ↑]) ⟧ₑ
    ≈ ⟦ ([ f ↑] ⊗ₑ [ g ↑]) ∘ₑ σ⇐ₑ ⟧ₑ
  inverse-braiding-natural-opaque {f = f} {g = g} =
    σ⇐-natural {f = [ f ↑]} {g = [ g ↑]}

  braiding-right-unit-opaque :
    ∀ {A : Obj} →
    ⟦ λ⇒ₑ {A = A} ∘ₑ σ⇒ₑ {A = A} {B = unit} ⟧ₑ
    ≈ ⟦ ρ⇒ₑ {A = A} ⟧ₑ
  braiding-right-unit-opaque = σ⇒-unitʳ

  braiding-right-unit-inv-opaque :
    ∀ {A : Obj} →
    ⟦ σ⇒ₑ {A = A} {B = unit} ∘ₑ ρ⇐ₑ {A = A} ⟧ₑ
    ≈ ⟦ λ⇐ₑ {A = A} ⟧ₑ
  braiding-right-unit-inv-opaque = σ⇒-unitʳ-inv

  inverse-braiding-right-unit-inv-opaque :
    ∀ {A : Obj} →
    ⟦ σ⇐ₑ {A = A} {B = unit} ∘ₑ λ⇐ₑ {A = A} ⟧ₑ
    ≈ ⟦ ρ⇐ₑ {A = A} ⟧ₑ
  inverse-braiding-right-unit-inv-opaque = σ⇐-unitʳ-inv

  inverse-braiding-left-unit-opaque :
    ∀ {A : Obj} →
    ⟦ ρ⇒ₑ {A = A} ∘ₑ σ⇐ₑ {A = A} {B = unit} ⟧ₑ
    ≈ ⟦ λ⇒ₑ {A = A} ⟧ₑ
  inverse-braiding-left-unit-opaque = σ⇐-unitˡ

  braiding-hexagon-opaque :
    ∀ {A B D : Obj} →
    ⟦ (idₑ {A = B} ⊗ₑ σ⇒ₑ {A = A} {B = D})
        ∘ₑ α⇒ₑ {A = B} {B = A} {C′ = D}
        ∘ₑ (σ⇒ₑ {A = A} {B = B} ⊗ₑ idₑ {A = D}) ⟧ₑ
    ≈ ⟦ α⇒ₑ {A = B} {B = D} {C′ = A}
        ∘ₑ σ⇒ₑ {A = A} {B = B ⊗₀ D}
        ∘ₑ α⇒ₑ {A = A} {B = B} {C′ = D} ⟧ₑ
  braiding-hexagon-opaque = σ⇒-hexagon₁

  inverse-braid-cancel-opaque :
    ∀ {A B : Obj} →
    ⟦ σ⇐ₑ {A = A} {B = B} ∘ₑ σ⇒ₑ {A = A} {B = B} ⟧ₑ
    ≈ ⟦ idₑ {A = A ⊗₀ B} ⟧ₑ
  inverse-braid-cancel-opaque = σ⇐∘σ⇒

  inverse-braid-is-braid-opaque :
    ∀ {A B : Obj} →
    ⟦ σ⇐ₑ {A = A} {B = B} ⟧ₑ
    ≈ ⟦ σ⇒ₑ {A = B} {B = A} ⟧ₑ
  inverse-braid-is-braid-opaque = σ⇐≈σ⇒

  symmetric-braid-involutive-opaque :
    ∀ {A B : Obj} →
    ⟦ σₑ {A = B} {B = A} ∘ₑ σₑ {A = A} {B = B} ⟧ₑ
    ≈ ⟦ idₑ {A = A ⊗₀ B} ⟧ₑ
  symmetric-braid-involutive-opaque = σ²
