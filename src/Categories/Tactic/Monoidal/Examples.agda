{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Tactic.Monoidal.Examples
  {o ℓ e a : Level}
  {C : Category o ℓ e}
  (M : Monoidal C)
  {Atom : Set a}
  (⟦_⟧ₐ : Atom → Category.Obj C)
  (w x y z : Atom)
  where

open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Tactic.Monoidal.Core M ⟦_⟧ₐ
open import Categories.Tactic.Monoidal using (solve; solve₀; solveMonoidal; solveMonoidalExpr)
import Categories.Tactic.Monoidal.Expression as Expression

open import Categories.Morphism C using (_≅_)
open Category C hiding (_⇒_)
open Monoidal M hiding (⊗) renaming (_⊗₁_ to _⊗₁ᶜ_)
open Free Atom renaming (_∘_ to _∘ᶠ_)

private
  module Expr = Expression.Core M
  open Expr using
    ( [_↑]; idₑ; _∘ₑ_; _⊗ₑ_; α⇒ₑ; ρ⇒ₑ
    ; solveₑ; ⟦_⟧ₑ
    ; reflₑ; leaf-≈ₑ; _⟩∘ₑ⟨_; _⟩⊗ₑ⟨_
    ; ⊗-identityₑ; ⊗-distribₑ; split₁ʳₑ; commute₂₁ₑ
    ; α⇒-naturalₑ; ρ⇒-naturalₑ
    )

  variable
    A B D F G H : Category.Obj C
    f : Category._⇒_ C B D
    g : Category._⇒_ C A B
    h : Category._⇒_ C G H
    i : Category._⇒_ C F G

  assoc-iso : ⟦ (‹ w › ⊗ ‹ x ›) ⊗ ‹ y › ⟧₀ ≅ ⟦ ‹ w › ⊗ (‹ x › ⊗ ‹ y ›) ⟧₀
  assoc-iso = object-coherence {X = (‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›}
                               {Y = ‹ w › ⊗ (‹ x › ⊗ ‹ y ›)} refl

  assoc-iso-solved : ⟦ (‹ w › ⊗ ‹ x ›) ⊗ ‹ y › ⟧₀ ≅ ⟦ ‹ w › ⊗ (‹ x › ⊗ ‹ y ›) ⟧₀
  assoc-iso-solved = solve₀ M ⟦_⟧ₐ

  unit-iso : ⟦ (I ⊗ ‹ w ›) ⊗ (‹ x › ⊗ I) ⟧₀ ≅ ⟦ ‹ w › ⊗ ‹ x › ⟧₀
  unit-iso = object-coherence {X = (I ⊗ ‹ w ›) ⊗ (‹ x › ⊗ I)}
                              {Y = ‹ w › ⊗ ‹ x ›} refl

  unit-iso-solved : ⟦ (I ⊗ ‹ w ›) ⊗ (‹ x › ⊗ I) ⟧₀ ≅ ⟦ ‹ w › ⊗ ‹ x › ⟧₀
  unit-iso-solved = solve₀ M ⟦_⟧ₐ

  reassoc-cancel
    : ⟦ α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⟧₁
      ≈ ⟦ idₘ {(‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›} ⟧₁
  reassoc-cancel =
    coherence-from-loop {f = α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›}} {g = idₘ}
      (Equiv.trans identityˡ associator.isoˡ)

  triangle-faithful
    : ⟦ (idₘ ⊗₁ λ⇒) ∘ᶠ α⇒ {‹ w ›} {I} {‹ x ›} ⟧₁
      ≈ ⟦ ρ⇒ {‹ w ›} ⊗₁ idₘ {‹ x ›} ⟧₁
  triangle-faithful = triangle

  pentagon-faithful
    : ⟦ (idₘ ⊗₁ α⇒) ∘ᶠ
        (α⇒ ∘ᶠ (α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⊗₁ idₘ {‹ z ›})) ⟧₁
      ≈ ⟦ α⇒ ∘ᶠ α⇒ {‹ w › ⊗ ‹ x ›} {‹ y ›} {‹ z ›} ⟧₁
  pentagon-faithful = pentagon

  reassoc-cancel-goal : Set e
  reassoc-cancel-goal =
    ⟦ α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⟧₁
    ≈ ⟦ idₘ {(‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›} ⟧₁

  reassoc-cancel-solved
    : ⟦ α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⟧₁
      ≈ ⟦ idₘ {(‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›} ⟧₁
  reassoc-cancel-solved = solveMonoidal M ⟦_⟧ₐ

  reassoc-cancel-solved-via-alias : reassoc-cancel-goal
  reassoc-cancel-solved-via-alias = solve M ⟦_⟧ₐ

  ⊗-interchangeₑ :
    ⟦ ([ f ↑] ∘ₑ [ g ↑]) ⊗ₑ ([ h ↑] ∘ₑ [ i ↑]) ⟧ₑ
    ≈ ⟦ ([ f ↑] ⊗ₑ [ h ↑]) ∘ₑ ([ g ↑] ⊗ₑ [ i ↑]) ⟧ₑ
  ⊗-interchangeₑ {f = f′} {g = g′} {h = h′} {i = i′} =
    solveₑ (⊗-distribₑ {f = [ f′ ↑]} {g = [ g′ ↑]} {h = [ h′ ↑]} {i = [ i′ ↑]})

  α⇒-naturalₑ-example :
    ∀ {P Q R S T U}
      {j : Category._⇒_ C P Q}
      {k : Category._⇒_ C R S}
      {l : Category._⇒_ C T U} →
    ⟦ α⇒ₑ ∘ₑ ((([ j ↑]) ⊗ₑ ([ k ↑])) ⊗ₑ ([ l ↑])) ⟧ₑ
    ≈ ⟦ (([ j ↑]) ⊗ₑ (([ k ↑]) ⊗ₑ ([ l ↑]))) ∘ₑ α⇒ₑ ⟧ₑ
  α⇒-naturalₑ-example {j = j′} {k = k′} {l = l′} =
    solveₑ (α⇒-naturalₑ {f = [ j′ ↑]} {g = [ k′ ↑]} {h = [ l′ ↑]})

  opaque-assoc :
    ∀ {P Q R S}
      {j : Category._⇒_ C R S}
      {k : Category._⇒_ C Q R}
      {l : Category._⇒_ C P Q} →
    (j ∘ k) ∘ l ≈ j ∘ (k ∘ l)
  opaque-assoc = solveMonoidalExpr C M

  ⊗-idₑ-example :
    ∀ {P Q : Obj} →
    ⟦ idₑ {A = P} ⊗ₑ idₑ {A = Q} ⟧ₑ
    ≈ ⟦ idₑ {A = P ⊗₀ Q} ⟧ₑ
  ⊗-idₑ-example = solveₑ ⊗-identityₑ

  split₁ʳₑ-example :
    ∀ {P Q R S T}
      {j : Category._⇒_ C Q R}
      {k : Category._⇒_ C P Q}
      {l : Category._⇒_ C S T} →
    ⟦ ([ j ↑] ∘ₑ [ k ↑]) ⊗ₑ [ l ↑] ⟧ₑ
    ≈ ⟦ ([ j ↑] ⊗ₑ [ l ↑]) ∘ₑ ([ k ↑] ⊗ₑ idₑ) ⟧ₑ
  split₁ʳₑ-example {j = j′} {k = k′} {l = l′} =
    solveₑ (split₁ʳₑ {f = [ j′ ↑]} {g = [ k′ ↑]} {h = [ l′ ↑]})

  commute₂₁ₑ-example :
    ∀ {P Q R S}
      {j : Category._⇒_ C P Q}
      {k : Category._⇒_ C R S} →
    ⟦ (idₑ ⊗ₑ [ k ↑]) ∘ₑ ([ j ↑] ⊗ₑ idₑ) ⟧ₑ
    ≈ ⟦ ([ j ↑] ⊗ₑ idₑ) ∘ₑ (idₑ ⊗ₑ [ k ↑]) ⟧ₑ
  commute₂₁ₑ-example {j = j′} {k = k′} =
    solveₑ (commute₂₁ₑ {f = [ j′ ↑]} {g = [ k′ ↑]})

  ρ⇒-naturalₑ-example :
    ∀ {P Q} {j : Category._⇒_ C P Q} →
    ⟦ ρ⇒ₑ ∘ₑ ([ j ↑] ⊗ₑ idₑ) ⟧ₑ
    ≈ ⟦ [ j ↑] ∘ₑ ρ⇒ₑ ⟧ₑ
  ρ⇒-naturalₑ-example {j = j′} =
    solveₑ (ρ⇒-naturalₑ {f = [ j′ ↑]})

  leaf-≈ₑ-example :
    ∀ {P Q R S T}
      {j k : Category._⇒_ C P Q}
      {l : Category._⇒_ C Q R}
      {m : Category._⇒_ C S T} →
    j ≈ k →
    ⟦ (([ l ↑] ∘ₑ [ j ↑]) ⊗ₑ [ m ↑]) ⟧ₑ
    ≈ ⟦ (([ l ↑] ∘ₑ [ k ↑]) ⊗ₑ [ m ↑]) ⟧ₑ
  leaf-≈ₑ-example {l = l′} {m = m′} j≈k =
    solveₑ ((reflₑ {f = [ l′ ↑]} ⟩∘ₑ⟨ leaf-≈ₑ j≈k) ⟩⊗ₑ⟨ reflₑ {f = [ m′ ↑]})
