{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)

module Categories.Category.Monoidal.CompactClosed.Trace.Vanishing
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C)
    (S : Symmetric M)
    (R : LeftRigid M) where

open import Categories.Category.Monoidal.CompactClosed.Trace.Definition M S R
  using (trace; trace-expand; trace-expanded)
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided S)
  using () renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Rigid.TensorDual M R
  using (⊗-cup; ⊗-cap)
open import Categories.Category.Monoidal.CompactClosed.TensorDual M S R
  using
    ( iterated-cap; iterated-cup; ⊗-cup-context; ⊗-cap-context
    ; ⊗-cup-fusion; ⊗-cap-fusion; ⊗-cap-transport )
open import Categories.Category.Monoidal.Rigid.Properties M as RigidProps
open RigidProps.Left R
  using (⊗-dual⇒; ⊗-dual-cup⇒)

open Category C
open Monoidal M
open LeftRigid R using (_⁻¹; η; ε)

open import Categories.Category.Monoidal.Reasoning M
open TensorIdentity using (id⊗id)
open import Categories.Morphism.Reasoning C
import Categories.Category.Monoidal.Utilities M as MonUtil
open MonUtil.Shorthands
open BraidShorthands using (σ⇒)

private
  ⊗-trace : ∀ {X Y A B} → A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y) → A ⇒ B
  ⊗-trace {X} {Y} {A} {B} f =
    ρ⇒ {B} ∘ (id {B} ⊗₁ ⊗-cap {X} {Y})
      ∘ (id {B} ⊗₁ σ⇒ {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇒ {B} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
      ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐ {A} {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐ {A}

  inner-dist : ∀ {X Y A B}
    {g : (A ⊗₀ X) ⊗₀ Y ⇒ (B ⊗₀ X) ⊗₀ Y} →
    trace {X = Y} g ⊗₁ id {X ⁻¹}
    ≈ (ρ⇒ ⊗₁ id {X ⁻¹})
      ∘ ((id ⊗₁ ε {Y}) ⊗₁ id)
      ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id)
      ∘ (α⇒ ⊗₁ id)
      ∘ ((g ⊗₁ id {Y ⁻¹}) ⊗₁ id)
      ∘ (α⇐ ⊗₁ id)
      ∘ ((id ⊗₁ η {Y}) ⊗₁ id)
      ∘ (ρ⇐ ⊗₁ id)
  inner-dist {X} {Y} {A} {B} {g} = begin
    trace {X = Y} g ⊗₁ id {X ⁻¹}
      ≈⟨ trace-expand {f = g} ⟩⊗⟨refl ⟩
    (ρ⇒ ∘ (id ⊗₁ ε {Y}) ∘ (id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ∘ α⇒
      ∘ (g ⊗₁ id {Y ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {Y}) ∘ ρ⇐) ⊗₁ id {X ⁻¹}
      ≈⟨ split₁ʳ ⟩
    (ρ⇒ ⊗₁ id {X ⁻¹})
      ∘ (((id ⊗₁ ε {Y}) ∘ (id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ∘ α⇒
        ∘ (g ⊗₁ id {Y ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {Y}) ∘ ρ⇐) ⊗₁ id {X ⁻¹})
      ≈⟨ refl⟩∘⟨ split₁ʳ ⟩
    (ρ⇒ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ ε {Y}) ⊗₁ id)
      ∘ (((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ∘ α⇒ ∘ (g ⊗₁ id {Y ⁻¹})
        ∘ α⇐ ∘ (id ⊗₁ η {Y}) ∘ ρ⇐) ⊗₁ id {X ⁻¹})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
    (ρ⇒ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ ε {Y}) ⊗₁ id)
      ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id)
      ∘ ((α⇒ ∘ (g ⊗₁ id {Y ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {Y}) ∘ ρ⇐) ⊗₁ id {X ⁻¹})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
    (ρ⇒ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ ε {Y}) ⊗₁ id)
      ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ∘ (((g ⊗₁ id {Y ⁻¹}) ∘ α⇐ ∘ (id ⊗₁ η {Y}) ∘ ρ⇐) ⊗₁ id {X ⁻¹})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
    (ρ⇒ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ ε {Y}) ⊗₁ id)
      ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ∘ ((g ⊗₁ id {Y ⁻¹}) ⊗₁ id)
      ∘ ((α⇐ ∘ (id ⊗₁ η {Y}) ∘ ρ⇐) ⊗₁ id {X ⁻¹})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
    (ρ⇒ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ ε {Y}) ⊗₁ id)
      ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ∘ ((g ⊗₁ id {Y ⁻¹}) ⊗₁ id) ∘ (α⇐ ⊗₁ id)
      ∘ (((id ⊗₁ η {Y}) ∘ ρ⇐) ⊗₁ id {X ⁻¹})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
    (ρ⇒ ⊗₁ id {X ⁻¹}) ∘ ((id ⊗₁ ε {Y}) ⊗₁ id)
      ∘ ((id ⊗₁ σ⇒ {Y} {Y ⁻¹}) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ∘ ((g ⊗₁ id {Y ⁻¹}) ⊗₁ id) ∘ (α⇐ ⊗₁ id)
      ∘ ((id ⊗₁ η {Y}) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)
      ∎

  ⊗-trace-context : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    ⊗-cap-context {B} {X} {Y}
      ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹})
      ∘ ⊗-cup-context {A} {X} {Y}
    ≈ ⊗-trace f
  ⊗-trace-context =
    ⟺ (refl⟩∘⟨ refl⟩∘⟨ sym-assoc
      ○ refl⟩∘⟨ sym-assoc
      ○ sym-assoc)

  nested-core : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    (f ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹}
    ≈ α⇐ {B ⊗₀ (X ⊗₀ Y)} {Y ⁻¹} {X ⁻¹}
      ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹})
      ∘ α⇒ {A ⊗₀ (X ⊗₀ Y)} {Y ⁻¹} {X ⁻¹}
  nested-core {X} {Y} {A} {B} {f} = begin
    (f ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹}
      ≈˘⟨ cancelˡ associator.isoˡ ⟩
    α⇐ {B ⊗₀ (X ⊗₀ Y)} {Y ⁻¹} {X ⁻¹}
      ∘ (α⇒ {B ⊗₀ (X ⊗₀ Y)} {Y ⁻¹} {X ⁻¹}
      ∘ ((f ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹}))
      ≈⟨ refl⟩∘⟨ assoc-commute-from ⟩
    α⇐ {B ⊗₀ (X ⊗₀ Y)} {Y ⁻¹} {X ⁻¹}
      ∘ ((f ⊗₁ (id {Y ⁻¹} ⊗₁ id {X ⁻¹}))
      ∘ α⇒ {A ⊗₀ (X ⊗₀ Y)} {Y ⁻¹} {X ⁻¹})
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ id⊗id) ⟩∘⟨refl ⟩
    α⇐ {B ⊗₀ (X ⊗₀ Y)} {Y ⁻¹} {X ⁻¹}
      ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹})
      ∘ α⇒ {A ⊗₀ (X ⊗₀ Y)} {Y ⁻¹} {X ⁻¹}
      ∎

  nested-core-split : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    (((α⇐ {B} {X} {Y} ∘ f ∘ α⇒ {A} {X} {Y}) ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
    ≈ ((α⇐ {B} {X} {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ∘ ((f ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ∘ ((α⇒ {A} {X} {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
  nested-core-split =
    (((split₁ʳ ○ (refl⟩∘⟨ split₁ʳ)) ⟩⊗⟨refl) ○ split₁ʳ ○ (refl⟩∘⟨ split₁ʳ))

  nested-core-reshape : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    (((α⇐ {B} {X} {Y} ∘ f ∘ α⇒ {A} {X} {Y}) ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
    ≈ ((α⇐ {B} {X} {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ∘ (α⇐ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇒)
      ∘ ((α⇒ {A} {X} {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
  nested-core-reshape {X} {Y} {A} {B} {f} = begin
    (((α⇐ {B} {X} {Y} ∘ f ∘ α⇒ {A} {X} {Y}) ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ≈⟨ nested-core-split ⟩
    ((α⇐ {B} {X} {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ∘ ((f ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ∘ ((α⇒ {A} {X} {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ≈⟨ refl⟩∘⟨ nested-core ⟩∘⟨refl ⟩
    ((α⇐ {B} {X} {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ∘ (α⇐ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇒)
      ∘ ((α⇒ {A} {X} {Y} ⊗₁ id {Y ⁻¹}) ⊗₁ id {X ⁻¹})
      ∎

  nested-trace-reduced : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    trace {X = X} (trace {X = Y} (α⇐ ∘ f ∘ α⇒))
    ≈ iterated-cap {B} {X} {Y} ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ iterated-cup {A} {X} {Y}
  nested-trace-reduced =
    trace-expand
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ inner-dist ⟩∘⟨refl
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
        ⟺
          ( refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
          ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
          ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
          ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
          ○ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
          ○ refl⟩∘⟨ sym-assoc
          ○ sym-assoc )
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
        (nested-core-reshape ⟩∘⟨refl)
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
        ( assoc
        ○ refl⟩∘⟨ assoc
        ○ refl⟩∘⟨ assoc
        ○ refl⟩∘⟨ refl⟩∘⟨ assoc )
    ○ ( refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
      ○ refl⟩∘⟨ refl⟩∘⟨ sym-assoc
      ○ refl⟩∘⟨ sym-assoc
      ○ sym-assoc )

  nested-trace-fusion : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    iterated-cap {B} {X} {Y} ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ iterated-cup {A} {X} {Y}
    ≈ ⊗-trace f
  nested-trace-fusion {X} {Y} {A} {B} {f} = begin
    iterated-cap {B} {X} {Y} ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ iterated-cup {A} {X} {Y}
      ≈⟨ sym-assoc ⟩
    (iterated-cap {B} {X} {Y} ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹})) ∘ iterated-cup {A} {X} {Y}
      ≈⟨ (⊗-cap-fusion {A = B} {X = X} {Y = Y} ⟩∘⟨refl)
          ⟩∘⟨ ⊗-cup-fusion {A = A} {X = X} {Y = Y} ⟩
    (⊗-cap-context {B} {X} {Y} ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹})) ∘ ⊗-cup-context {A} {X} {Y}
      ≈⟨ assoc ⟩
    ⊗-cap-context {B} {X} {Y} ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ ⊗-cup-context {A} {X} {Y}
      ≈⟨ ⊗-trace-context ⟩
    ⊗-trace f
      ∎

nested-trace-is-⊗-trace :
  ∀ {X Y A B} {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
  trace {X = X} (trace {X = Y} (α⇐ ∘ f ∘ α⇒))
  ≈ ⊗-trace f
nested-trace-is-⊗-trace {X} {Y} {A} {B} {f} =
  begin
  trace {X = X} (trace {X = Y} (α⇐ ∘ f ∘ α⇒))
    ≈⟨ nested-trace-reduced ⟩
  iterated-cap {B} {X} {Y} ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ iterated-cup {A} {X} {Y}
    ≈⟨ nested-trace-fusion ⟩
  ⊗-trace f ∎

private
  cup-to-⊗-dual : ∀ {A X Y} →
    id {A} ⊗₁ η {X ⊗₀ Y}
    ≈ id {A} ⊗₁ ((id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}) ∘ ⊗-cup {X} {Y})
  cup-to-⊗-dual = refl⟩⊗⟨ ⟺ ⊗-dual-cup⇒

  compare-natural : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
      (f ⊗₁ id {(X ⊗₀ Y) ⁻¹})
        ∘ ((id {A} ⊗₁ id {X ⊗₀ Y}) ⊗₁ ⊗-dual⇒ {X} {Y})
    ≈ ((id {B} ⊗₁ id {X ⊗₀ Y}) ⊗₁ ⊗-dual⇒ {X} {Y})
        ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹})
  compare-natural {X} {Y} {A} {B} {f} = begin
    (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ ((id {A} ⊗₁ id {X ⊗₀ Y}) ⊗₁ ⊗-dual⇒ {X} {Y})
      ≈˘⟨ ⊗-distrib-over-∘ ⟩
    (f ∘ (id {A} ⊗₁ id {X ⊗₀ Y})) ⊗₁ (id {(X ⊗₀ Y) ⁻¹} ∘ ⊗-dual⇒ {X} {Y})
      ≈⟨ elimʳ id⊗id ⟩⊗⟨ identityˡ ⟩
    f ⊗₁ ⊗-dual⇒ {X} {Y}
      ≈˘⟨ identityˡ ⟩⊗⟨refl ⟩
    (id {B ⊗₀ (X ⊗₀ Y)} ∘ f) ⊗₁ ⊗-dual⇒ {X} {Y}
      ≈⟨ ((⟺ id⊗id) ⟩∘⟨refl) ⟩⊗⟨refl ⟩
    ((id {B} ⊗₁ id {X ⊗₀ Y}) ∘ f) ⊗₁ ⊗-dual⇒ {X} {Y}
      ≈˘⟨ Equiv.refl ⟩⊗⟨ identityʳ ⟩
    ((id {B} ⊗₁ id {X ⊗₀ Y}) ∘ f) ⊗₁ (⊗-dual⇒ {X} {Y} ∘ id {Y ⁻¹ ⊗₀ X ⁻¹})
      ≈⟨ ⊗-distrib-over-∘ ⟩
    ((id {B} ⊗₁ id {X ⊗₀ Y}) ⊗₁ ⊗-dual⇒ {X} {Y})
      ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹})
      ∎

  compare-slide-core : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
      α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ α⇐
        ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
    ≈ (id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
        ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐
  compare-slide-core {X} {Y} {A} {B} {f} = begin
    α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ α⇐
      ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-to ⟩
    α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹})
      ∘ (((id {A} ⊗₁ id {X ⊗₀ Y}) ⊗₁ ⊗-dual⇒ {X} {Y}) ∘ α⇐)
      ≈⟨ refl⟩∘⟨ pullˡ compare-natural ⟩
    α⇒ ∘ (((id {B} ⊗₁ id {X ⊗₀ Y}) ⊗₁ ⊗-dual⇒ {X} {Y})
      ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹})) ∘ α⇐
      ≈⟨ refl⟩∘⟨ assoc ⟩
    α⇒ ∘ ((id {B} ⊗₁ id {X ⊗₀ Y}) ⊗₁ ⊗-dual⇒ {X} {Y})
      ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐
      ≈⟨ pullˡ assoc-commute-from ⟩
    ((id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y})) ∘ α⇒)
      ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐
      ≈⟨ assoc ⟩
    (id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐
      ∎

  compare-slide-spine : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
      α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ α⇐
        ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
        ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
    ≈ (α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ α⇐
        ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y})))
        ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
  compare-slide-spine {X} {Y} {A} {B} {f} = begin
    α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ α⇐
      ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹})
      ∘ (α⇐ ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y})))
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    α⇒ ∘ ((f ⊗₁ id {(X ⊗₀ Y) ⁻¹})
      ∘ (α⇐ ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))))
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ≈⟨ sym-assoc ⟩
    (α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ α⇐
      ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y})))
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ∎

  compare-slide-close : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
      ((id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
        ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐)
        ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
    ≈ (id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
        ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐
        ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
  compare-slide-close {X} {Y} {A} {B} {f} = begin
    ((id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐)
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ≈˘⟨ sym-assoc ⟩
    (id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ (α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐)
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ≈˘⟨ refl⟩∘⟨ sym-assoc ⟩
    (id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ α⇒ ∘ ((f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐)
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
    (id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ∎

  compare-slide : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
      α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ α⇐
        ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
        ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
    ≈ (id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
        ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐
        ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
  compare-slide {X} {Y} {A} {B} {f} = begin
    α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ α⇐
      ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ≈⟨ compare-slide-spine ⟩
    (α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ α⇐
      ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y})))
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ≈⟨ compare-slide-core ⟩∘⟨refl ⟩
    ((id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐)
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ≈⟨ compare-slide-close ⟩
    (id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐
      ∎

  cup-transported-trace :
    ∀ {X Y A B} → A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y) → A ⇒ B
  cup-transported-trace {X} {Y} {A} {B} f =
    ρ⇒ ∘ (id {B} ⊗₁ (ε {X ⊗₀ Y} ∘ σ⇒ {X ⊗₀ Y} {(X ⊗₀ Y) ⁻¹}))
      ∘ α⇒ ∘ (f ⊗₁ id {(X ⊗₀ Y) ⁻¹}) ∘ α⇐
      ∘ (id {A} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐

  compared-trace :
    ∀ {X Y A B} → A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y) → A ⇒ B
  compared-trace {X} {Y} {A} {B} f =
    ρ⇒ ∘ (id {B} ⊗₁ (ε {X ⊗₀ Y} ∘ σ⇒ {X ⊗₀ Y} {(X ⊗₀ Y) ⁻¹}))
      ∘ (id {B} ⊗₁ (id {X ⊗₀ Y} ⊗₁ ⊗-dual⇒ {X} {Y}))
      ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐

  cap-transported-trace :
    ∀ {X Y A B} → A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y) → A ⇒ B
  cap-transported-trace {X} {Y} {A} {B} f =
    ρ⇒ ∘ (id {B} ⊗₁ (⊗-cap {X} {Y} ∘ σ⇒ {X ⊗₀ Y} {Y ⁻¹ ⊗₀ X ⁻¹}))
      ∘ α⇒ ∘ (f ⊗₁ id {Y ⁻¹ ⊗₀ X ⁻¹}) ∘ α⇐
      ∘ (id {A} ⊗₁ ⊗-cup {X} {Y}) ∘ ρ⇐

  cup-transport : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    trace-expanded f ≈ cup-transported-trace f
  cup-transport {X} {Y} {A} {B} {f} =
    (refl⟩∘⟨ (sym-assoc ○ (merge₂ˡ ⟩∘⟨refl)))
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
        (cup-to-⊗-dual {A} {X} {Y} ⟩∘⟨refl)
    ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
        (split₂ˡ ⟩∘⟨refl ○ assoc)

  compare-transport : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    cup-transported-trace f ≈ compared-trace f
  compare-transport {X} {Y} {A} {B} {f} =
    refl⟩∘⟨ refl⟩∘⟨ compare-slide {X} {Y} {A} {B} {f}

  cap-transport : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    compared-trace f ≈ cap-transported-trace f
  cap-transport {X} {Y} {A} {B} {f} =
    refl⟩∘⟨ pullˡ (merge₂ˡ ○ (refl⟩⊗⟨ ⊗-cap-transport {X} {Y}))

  cap-split : ∀ {X Y A B}
    {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    cap-transported-trace f ≈ ⊗-trace f
  cap-split =
    refl⟩∘⟨ ((split₂ˡ ⟩∘⟨refl) ○ assoc)

  trace-to-⊗-trace :
    ∀ {X Y A B} {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    trace-expanded f ≈ ⊗-trace f
  trace-to-⊗-trace {X} {Y} {A} {B} {f} = begin
    trace-expanded f
      ≈⟨ cup-transport {X} {Y} {A} {B} {f} ⟩
    cup-transported-trace f
      ≈⟨ compare-transport {X} {Y} {A} {B} {f} ⟩
    compared-trace f
      ≈⟨ cap-transport {X} {Y} {A} {B} {f} ⟩
    cap-transported-trace f
      ≈⟨ cap-split {X} {Y} {A} {B} {f} ⟩
    ⊗-trace f
      ∎

⊗-trace-expand :
  ∀ {X Y A B} {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
  ⊗-trace f ≈ trace-expanded f
⊗-trace-expand {X} {Y} {A} {B} {f} =
  begin
  ⊗-trace f
    ≈˘⟨ trace-to-⊗-trace {X} {Y} {A} {B} {f} ⟩
  trace-expanded f ∎

⊗-trace-is-trace :
  ∀ {X Y A B} {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
  ⊗-trace f
  ≈ trace {X = X ⊗₀ Y} f
⊗-trace-is-trace {X} {Y} {A} {B} {f} =
  begin
  ⊗-trace f
    ≈⟨ ⊗-trace-expand {X} {Y} {A} {B} {f} ⟩
  trace-expanded f
    ≈˘⟨ trace-expand ⟩
  trace {X = X ⊗₀ Y} f ∎

vanishing₂ :
  ∀ {X Y A B} {f : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
  trace {X = X} (trace {X = Y} (α⇐ ∘ f ∘ α⇒))
  ≈ trace {X = X ⊗₀ Y} f
vanishing₂ {X} {Y} {A} {B} {f} =
  begin
  trace {X = X} (trace {X = Y} (α⇐ ∘ f ∘ α⇒))
    ≈⟨ nested-trace-is-⊗-trace {X} {Y} {A} {B} {f} ⟩
  ⊗-trace f
    ≈⟨ ⊗-trace-is-trace {X} {Y} {A} {B} {f} ⟩
  trace {X = X ⊗₀ Y} f ∎
