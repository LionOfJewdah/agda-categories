{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)
open import Categories.Category.Monoidal.CompactClosed using (CompactClosed)
open import Data.Product using (_,_)

module Categories.Category.Monoidal.CompactClosed.Trace.Definition
    {o ℓ e} {𝒞 : Category o ℓ e}
    (M : Monoidal 𝒞)
    (K : CompactClosed M) where

-- The trace of `f : A ⊗₀ X ⇒ B ⊗₀ X` in a compact closed category, together with
-- the JSV axioms that follow directly from the snake identities: `trace-slide`,
-- the two tightenings, `yanking` and `vanishing₁`.
-- Joyal, Street & Verity, "Traced monoidal categories" (1996), §5.

open Category 𝒞
open CompactClosed K
open LeftRigid leftRigid

open Symmetric symmetric using (braiding; hexagon₁)

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided symmetric)
  using (braiding-coherence-σ; braiding-coherence-σ′) renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Rigid.Dual M leftRigid
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.Traced.PreTrace M using (PreTrace)
import Categories.Category.Monoidal.Utilities M as MonUtil
open MonUtil.Shorthands
open BraidShorthands using (σ⇒; σ⇒-comm)

private
  variable
    A B C X Y Z : Obj

-- Diagrams read bottom-to-top: a morphism's inputs are the wires entering from
-- below, its outputs the wires leaving above.  Duality bends a wire — `η` grows an
-- `X`/`X ⁻¹` pair out of nothing, `ε` swallows one back — and `capᵗʳ`, `cupᵗʳ` are
-- those two bends with a spectator wire (`B`, resp. `A`) passing alongside.
--
--                capᵗʳ                              cupᵗʳ
--
--         B                                  A      X       X ⁻¹
--         │                                  │      │        │
--         │      ╭──────────────╮            │      ╰────────╯     ← η
--         │      │              │            │
--         B      X            X ⁻¹           A
--                   ↑ ε ∘ σ⇒

capᵗʳ : (B ⊗₀ X) ⊗₀ X ⁻¹ ⇒ B
capᵗʳ = ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒

cupᵗʳ : A ⇒ (A ⊗₀ X) ⊗₀ X ⁻¹
cupᵗʳ = unit-conjʳ (id ⊗₁ η)

-- The trace closes `f`'s `X` leg into a loop: whatever leaves `f` on the right
-- comes back in on the right.
--
--         B          X ──────────╮
--         │          │           │
--      ┌──┴──────────┴──┐        │
--      │        f       │        │        f : A ⊗₀ X ⇒ B ⊗₀ X
--      └──┬──────────┬──┘        │
--         │          │           │
--         A          X ──────────╯
--
-- Compact closure builds that return path from a cup and a cap.  Read upwards,
-- `trace f = capᵗʳ ∘ (f ⊗₁ id) ∘ cupᵗʳ` stacks as below: the cup grows the pair,
-- `f` runs on the `A`/`X` wires, the cap swallows the pair again.  The `X ⁻¹` wire
-- is the loop's right-hand side, and `f` never touches it.
--
--                      B
--                      │
--          ┌───────────┴────────────┐
--          │          capᵗʳ         │       ← ε ∘ σ⇒
--          └────┬─────────┬───────┬─┘
--               B         X      X ⁻¹
--          ┌────┴─────────┴──┐    │
--          │        f        │    │
--          └────┬─────────┬──┘    │
--               A         X      X ⁻¹
--          ┌────┴─────────┴───────┴─┐
--          │          cupᵗʳ         │       ← η
--          └───────────┬────────────┘
--                      A

trace-expanded : A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
trace-expanded f =
  ρ⇒ ∘ (id ⊗₁  ε)
     ∘ (id ⊗₁ σ⇒) ∘ α⇒
     ∘ (f  ⊗₁ id) ∘ α⇐
     ∘ (id ⊗₁  η) ∘ ρ⇐

trace : A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
trace f = capᵗʳ ∘ (f ⊗₁ id) ∘ cupᵗʳ

trace-resp-≈ : {f g : A ⊗₀ X ⇒ B ⊗₀ X} → f ≈ g → trace f ≈ trace g
trace-resp-≈ f≈g = ∘-resp-≈ʳ (∘-resp-≈ˡ (f≈g ⟩⊗⟨refl))

trace-expand : {f : A ⊗₀ X ⇒ B ⊗₀ X} → trace f ≈ trace-expanded f
trace-expand = ⟺ reassoc-tail₅

trace-expanded-resp-≈ : {f g : A ⊗₀ X ⇒ B ⊗₀ X} →
  f ≈ g → trace-expanded f ≈ trace-expanded g
trace-expanded-resp-≈ f≈g = ⟺ trace-expand ○ trace-resp-≈ f≈g ○ trace-expand

capᵗʳ-natural : {f : B ⇒ C} →
  capᵗʳ ∘ ((f ⊗₁ id {X}) ⊗₁ id {X ⁻¹}) ≈ f ∘ capᵗʳ
capᵗʳ-natural {f = f} = begin
  capᵗʳ ∘ ((f ⊗₁ id) ⊗₁ id)                             ≈˘⟨ reassoc-tail₅ ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ ((f ⊗₁ id) ⊗₁ id)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-⊗id-commute ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ (f ⊗₁ id) ∘ α⇒          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (⟺ whisker-comm) ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ (f ⊗₁ id) ∘ (id ⊗₁ σ⇒) ∘ α⇒          ≈⟨ refl⟩∘⟨ extendʳ (⟺ whisker-comm) ⟩
  ρ⇒ ∘ (f ⊗₁ id) ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒          ≈⟨ extendʳ unitorʳ-commute-from ⟩
  f ∘ capᵗʳ                                             ∎

cupᵗʳ-natural : {f : A ⇒ B} → ((f ⊗₁ id {X}) ⊗₁ id {X ⁻¹}) ∘ cupᵗʳ ≈ cupᵗʳ ∘ f
cupᵗʳ-natural {f = f} = begin
  ((f ⊗₁ id) ⊗₁ id) ∘ cupᵗʳ           ≈⟨ pullˡ (⟺ α⇐-⊗id-commute) ⟩
  (α⇐ ∘ (f ⊗₁ id)) ∘ (id ⊗₁ η) ∘ ρ⇐   ≈⟨ assoc ⟩
  α⇐ ∘ (f ⊗₁ id) ∘ (id ⊗₁ η) ∘ ρ⇐     ≈⟨ refl⟩∘⟨ extendʳ whisker-comm ⟩
  α⇐ ∘ (id ⊗₁ η) ∘ (f ⊗₁ id) ∘ ρ⇐     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ unitorʳ-commute-to ⟩
  α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐ ∘ f             ≈⟨ assoc²εβ ⟩
  cupᵗʳ ∘ f                           ∎

cupᵗʳ-slide : {g : X ⇒ Y} →
  ((id {A} ⊗₁ g) ⊗₁ id) ∘ cupᵗʳ ≈ (id ⊗₁ dual₁ g) ∘ cupᵗʳ
cupᵗʳ-slide {g = g} = begin
  ((id ⊗₁ g) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐           ≈⟨ pullˡ (⟺ assoc-commute-to) ⟩
  (α⇐ ∘ (id ⊗₁ (g ⊗₁ id))) ∘ (id ⊗₁ η) ∘ ρ⇐         ≈⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ (g ⊗₁ id)) ∘ (id ⊗₁ η) ∘ ρ⇐           ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
  α⇐ ∘ (id ⊗₁ ((g ⊗₁ id) ∘ η)) ∘ ρ⇐                 ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ ⟺ dual₁-cup ⟩∘⟨refl ⟩
  α⇐ ∘ (id ⊗₁ ((id ⊗₁ dual₁ g) ∘ η)) ∘ ρ⇐           ≈⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
  α⇐ ∘ ((id ⊗₁ (id ⊗₁ dual₁ g)) ∘ (id ⊗₁ η)) ∘ ρ⇐   ≈⟨ assoc²δγ ⟩
  (α⇐ ∘ (id ⊗₁ (id ⊗₁ dual₁ g))) ∘ (id ⊗₁ η) ∘ ρ⇐   ≈˘⟨ α⇐-id⊗-commute ⟩∘⟨refl ⟩
  ((id ⊗₁ dual₁ g) ∘ α⇐) ∘ (id ⊗₁ η) ∘ ρ⇐           ≈⟨ assoc ⟩
  (id ⊗₁ dual₁ g) ∘ cupᵗʳ                           ∎

private
  -- The braiding commutes past a whiskered tensor of maps, swapping their order.
  σ⇒-slide : {f : B ⇒ C} {g : X ⇒ Y} →
    (id {A} ⊗₁ σ⇒) ∘ (id ⊗₁ (f ⊗₁ g)) ≈ (id ⊗₁ (g ⊗₁ f)) ∘ (id ⊗₁ σ⇒)
  σ⇒-slide = merge₂ˡ ○ (refl⟩⊗⟨ σ⇒-comm) ○ split₂ˡ

  -- Both slides meet here: `g` transposed to the far side of the braiding.
  capᵗʳ-slide-mid : (g : X ⇒ Y) → (B ⊗₀ X) ⊗₀ Y ⁻¹ ⇒ B
  capᵗʳ-slide-mid g = ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ (id ⊗₁ g)) ∘ (id ⊗₁ σ⇒) ∘ α⇒

  capᵗʳ-slideˡ : {g : X ⇒ Y} → capᵗʳ ∘ (id {B ⊗₀ X} ⊗₁ dual₁ g) ≈ capᵗʳ-slide-mid g
  capᵗʳ-slideˡ {g = g} = begin
    capᵗʳ ∘ (id ⊗₁ dual₁ g)                                     ≈˘⟨ reassoc-tail₅ ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (id ⊗₁ dual₁ g)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-id⊗-commute ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ (id ⊗₁ (id ⊗₁ dual₁ g)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ σ⇒-slide ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ (dual₁ g ⊗₁ id)) ∘ (id ⊗₁ σ⇒) ∘ α⇒
      ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    ρ⇒ ∘ (id ⊗₁ (ε ∘ (dual₁ g ⊗₁ id))) ∘ (id ⊗₁ σ⇒) ∘ α⇒
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ dual₁-cap) ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id ⊗₁ (ε ∘ (id ⊗₁ g))) ∘ (id ⊗₁ σ⇒) ∘ α⇒
      ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    capᵗʳ-slide-mid g                                    ∎

  capᵗʳ-slideʳ : {g : X ⇒ Y} → capᵗʳ ∘ ((id {B} ⊗₁ g) ⊗₁ id) ≈ capᵗʳ-slide-mid g
  capᵗʳ-slideʳ {g = g} = begin
    capᵗʳ ∘ ((id ⊗₁ g) ⊗₁ id)                             ≈˘⟨ reassoc-tail₅ ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ ((id ⊗₁ g) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ (id ⊗₁ (g ⊗₁ id)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ σ⇒-slide ⟩
    capᵗʳ-slide-mid g                                     ∎

capᵗʳ-slide : {g : X ⇒ Y} →
  capᵗʳ ∘ (id {B ⊗₀ X} ⊗₁ dual₁ g) ≈ capᵗʳ ∘ ((id {B} ⊗₁ g) ⊗₁ id)
capᵗʳ-slide {g = g} = begin
  capᵗʳ ∘ (id ⊗₁ dual₁ g)       ≈⟨ capᵗʳ-slideˡ ⟩
  capᵗʳ-slide-mid g             ≈˘⟨ capᵗʳ-slideʳ ⟩
  capᵗʳ ∘ ((id ⊗₁ g) ⊗₁ id)     ∎

-- All four objects are bound: the `let` block below names the whiskered maps.
trace-slide : ∀ {A Y B X} {f : A ⊗₀ Y ⇒ B ⊗₀ X} {g : X ⇒ Y} →
  trace (f ∘ id {A} ⊗₁ g) ≈ trace (id {B} ⊗₁ g ∘ f)
trace-slide {A} {Y} {B} {X} {f} {g} =
  let
    f⊗X⁻¹ = f ⊗₁ id {X ⁻¹}
    f⊗Y⁻¹ = f ⊗₁ id {Y ⁻¹}
    g⊗X⁻¹ = (id {A} ⊗₁ g) ⊗₁ id {X ⁻¹}
    g⊗Y⁻¹ = (id {B} ⊗₁ g) ⊗₁ id {Y ⁻¹}
    dualₐ = id {A ⊗₀ Y} ⊗₁ dual₁ g
    dualᵦ = id {B ⊗₀ X} ⊗₁ dual₁ g
  in begin
  trace (f ∘ id {A} ⊗₁ g)                 ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
  capᵗʳ ∘ ((f⊗X⁻¹ ∘ g⊗X⁻¹) ∘ cupᵗʳ)       ≈⟨ refl⟩∘⟨ assoc ⟩
  capᵗʳ ∘ (f⊗X⁻¹ ∘ (g⊗X⁻¹ ∘ cupᵗʳ))       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cupᵗʳ-slide ⟩
  capᵗʳ ∘ (f⊗X⁻¹ ∘ (dualₐ ∘ cupᵗʳ))       ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  capᵗʳ ∘ ((f⊗X⁻¹ ∘ dualₐ) ∘ cupᵗʳ)       ≈⟨ refl⟩∘⟨ whisker-comm ⟩∘⟨refl ⟩
  capᵗʳ ∘ ((dualᵦ ∘ f⊗Y⁻¹) ∘ cupᵗʳ)       ≈⟨ assoc²δγ ⟩
  (capᵗʳ ∘ dualᵦ) ∘ (f⊗Y⁻¹ ∘ cupᵗʳ)       ≈⟨ capᵗʳ-slide ⟩∘⟨refl ⟩
  (capᵗʳ ∘ g⊗Y⁻¹) ∘ (f⊗Y⁻¹ ∘ cupᵗʳ)       ≈⟨ assoc²γδ ⟩
  capᵗʳ ∘ ((g⊗Y⁻¹ ∘ f⊗Y⁻¹) ∘ cupᵗʳ)       ≈⟨ refl⟩∘⟨ merge₁ʳ ⟩∘⟨refl ⟩
  trace (id {B} ⊗₁ g ∘ f)                 ∎

tightenₗ : {f : B ⇒ C} {g : A ⊗₀ X ⇒ B ⊗₀ X} → trace (f ⊗₁ id ∘ g) ≈ f ∘ trace g
tightenₗ {f = f} {g} = let f-loop = (f ⊗₁ id) ⊗₁ id in begin
  trace (f ⊗₁ id ∘ g)                       ≈⟨ refl⟩∘⟨ (split₁ʳ ⟩∘⟨refl) ⟩
  capᵗʳ ∘ ((f-loop ∘ g ⊗₁ id) ∘ cupᵗʳ)      ≈⟨ assoc²δγ ⟩
  (capᵗʳ ∘ f-loop) ∘ (g ⊗₁ id ∘ cupᵗʳ)      ≈⟨ capᵗʳ-natural ⟩∘⟨refl ⟩
  (f ∘ capᵗʳ) ∘ (g ⊗₁ id ∘ cupᵗʳ)           ≈⟨ assoc ⟩
  f ∘ trace g                               ∎

tightenᵣ : {f : B ⊗₀ X ⇒ C ⊗₀ X} {g : A ⇒ B} → trace (f ∘ g ⊗₁ id) ≈ trace f ∘ g
tightenᵣ {f = f} {g} = let g-loop = (g ⊗₁ id) ⊗₁ id in begin
  trace (f ∘ g ⊗₁ id)                       ≈⟨ refl⟩∘⟨ (split₁ˡ ⟩∘⟨refl) ⟩
  capᵗʳ ∘ ((f ⊗₁ id ∘ g-loop) ∘ cupᵗʳ)      ≈⟨ refl⟩∘⟨ assoc ⟩
  capᵗʳ ∘ (f ⊗₁ id ∘ (g-loop ∘ cupᵗʳ))      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cupᵗʳ-natural ⟩
  capᵗʳ ∘ (f ⊗₁ id ∘ (cupᵗʳ ∘ g))           ≈⟨ assoc²εβ ⟩
  trace f ∘ g                               ∎

-- The yanking axiom: tracing out the braiding leaves the identity.  Close the
-- crossing's right leg into the loop and the wire pulls taut — the snake, drawn.
--
--         X       X ──────────╮                      X
--          ╲     ╱            │                      │
--           ╲   ╱             │                      │
--            ╲ ╱              │                      │
--             ╳               │           =          │
--            ╱ ╲              │                      │
--           ╱   ╲             │                      │
--          ╱     ╲            │                      │
--         X       X ──────────╯                      X
--
--                trace σ⇒                            id

private
  -- Once the cup has been braided to the far side of the loop it sits over the
  -- unit, where `σ⇒ ∘ ρ⇐` and `λ⇐` agree.
  cup-σ-unit : ((η {X} ⊗₁ id {X}) ∘ σ⇒ {X} {unit}) ∘ ρ⇐ ≈ (η {X} ⊗₁ id {X}) ∘ λ⇐
  cup-σ-unit = begin
    ((η ⊗₁ id) ∘ σ⇒) ∘ ρ⇐          ≈⟨ (refl⟩∘⟨ braiding-coherence-σ) ⟩∘⟨refl ⟩
    ((η ⊗₁ id) ∘ (λ⇐ ∘ ρ⇒)) ∘ ρ⇐   ≈⟨ pullʳ (cancelʳ unitorʳ.isoʳ) ⟩
    (η ⊗₁ id) ∘ λ⇐                 ∎

  -- The two braidings of the loop fuse into one by the hexagon.
  braid-loop-collapse :
      (id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ ∘ (σ⇒ {X} {X} ⊗₁ id) ∘ α⇐
    ≈ α⇒ ∘ σ⇒ {X} {X ⊗₀ X ⁻¹}
  braid-loop-collapse = begin
    (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐       ≈⟨ assoc²εβ ⟩
    ((id ⊗₁ σ⇒) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))) ∘ α⇐   ≈⟨ hexagon₁ ⟩∘⟨refl ⟩
    (α⇒ ∘ (σ⇒ ∘ α⇒)) ∘ α⇐                   ≈⟨ assoc²βε ⟩
    α⇒ ∘ σ⇒ ∘ α⇒ ∘ α⇐                       ≈⟨ refl⟩∘⟨ elimʳ associator.isoʳ ⟩
    α⇒ ∘ σ⇒                                 ∎

yanking : trace (σ⇒ {X} {X}) ≈ id
yanking = begin
  trace (σ⇒)                                              ≈⟨ trace-expand ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ reassoc-tail₅ ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ (((id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ η) ∘ ρ⇐)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braid-loop-collapse ⟩∘⟨refl ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ ((α⇒ ∘ σ⇒) ∘ (id ⊗₁ η) ∘ ρ⇐)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullʳ (pullˡ (braiding.⇒.commute (id , η))) ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒ ∘ ((η ⊗₁ id) ∘ σ⇒) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cup-σ-unit ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐                            ≈⟨ snake₁ ⟩
  id                                                             ∎

-- The first vanishing axiom: tracing out the unit does nothing.  The loop is made
-- of `unit` wire, and a `unit` wire is no wire at all — so there is no loop, and
-- `unit` has `dimension` `id`.
--
--         B      unit ────────╮                      B
--         │        │          │                      │
--      ┌──┴────────┴──┐       │                 ┌────┴────┐
--      │       f      │       │        =        │    f    │
--      └──┬────────┬──┘       │                 └────┬────┘
--         │        │          │                      │
--         A      unit ────────╯                      A
--
--     trace (f ⊗₁ id {unit})                         f

private
  -- The unit object has dimension `id`: its loop `ε ∘ σ⇒ ∘ η` is a snake in disguise.
  unit-dimension : ε {unit} ∘ σ⇒ ∘ η ≈ id
  unit-dimension = begin
    ε ∘ σ⇒ ∘ η                              ≈⟨ refl⟩∘⟨ braiding-coherence-σ′ ⟩∘⟨refl ⟩
    ε ∘ (ρ⇐ ∘ λ⇒) ∘ η                       ≈˘⟨ refl⟩∘⟨ λ⇒-ρ⇐-comm ⟩∘⟨refl ⟩
    ε ∘ (λ⇒ ∘ α⇒ ∘ ρ⇐) ∘ η                  ≈⟨ refl⟩∘⟨ pullʳ (pullʳ unitorʳ-commute-to) ⟩
    ε ∘ λ⇒ ∘ α⇒ ∘ (η ⊗₁ id) ∘ ρ⇐            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟩
    ε ∘ λ⇒ ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐            ≈⟨ pullˡ (⟺ unitorˡ-commute-from) ⟩
    (λ⇒ ∘ (id ⊗₁ ε)) ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐  ≈⟨ (coherence₃ ⟩∘⟨refl) ⟩∘⟨refl ⟩
    (ρ⇒ ∘ (id ⊗₁ ε)) ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐  ≈⟨ assoc ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐    ≈⟨ snake₁ ⟩
    id                                      ∎

  -- The `X = unit` trace loop, with its associators already cancelled.
  vanish₁-loop : ρ⇒ ∘ (id {A} ⊗₁ ε) ∘ (id ⊗₁ σ⇒ {unit} {unit ⁻¹}) ∘ (id ⊗₁ η) ∘ ρ⇐ ≈ id
  vanish₁-loop = begin
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ (id ⊗₁ η) ∘ ρ⇐  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ʳ ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ (σ⇒ ∘ η)) ∘ ρ⇐        ≈⟨ refl⟩∘⟨ pullˡ merge₂ʳ ⟩
    ρ⇒ ∘ (id ⊗₁ (ε ∘ σ⇒ ∘ η)) ∘ ρ⇐                ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ unit-dimension ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id ⊗₁ id) ∘ ρ⇐                          ≈⟨ refl⟩∘⟨ elimˡ ⊗.identity ⟩
    ρ⇒ ∘ ρ⇐                                       ≈⟨ unitorʳ.isoʳ ⟩
    id                                            ∎

  trace-unit-id : trace (id {A} ⊗₁ id {unit}) ≈ id
  trace-unit-id {A} = begin
    trace (id {A} ⊗₁ id {unit})        ≈⟨ trace-resp-≈ ⊗.identity ⟩
    trace id                ≈⟨ trace-expand ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (id ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ elimˡ ⊗.identity ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoʳ ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ (id ⊗₁ η) ∘ ρ⇐
      ≈⟨ vanish₁-loop ⟩
    id                                 ∎

vanishing₁ : {f : A ⇒ B} → trace (f ⊗₁ id {unit}) ≈ f
vanishing₁ {f = f} = begin
  trace (f ⊗₁ id {unit})                        ≈˘⟨ trace-resp-≈ (elimʳ ⊗.identity) ⟩
  trace ((f ⊗₁ id {unit}) ∘ (id ⊗₁ id {unit}))  ≈⟨ tightenₗ ⟩
  f ∘ trace (id ⊗₁ id {unit})                   ≈⟨ refl⟩∘⟨ trace-unit-id ⟩
  f ∘ id                                        ≈⟨ identityʳ ⟩
  f                                             ∎

------------------------------------------------------------------------
-- Bending a wire.  Every trace here opens a cup on the right of `A` with
-- `cup-openʳ`, runs the map along the resulting loop, and closes a cap with
-- `cap-closeʳ`; only the cup/cap pair changes.

⇒⦑_⦒⇐ : A ⊗₀ X ⇒ B ⊗₀ X → A ⊗₀ (X ⊗₀ Z) ⇒ B ⊗₀ (X ⊗₀ Z)
⇒⦑ f ⦒⇐ = α⇒ ∘ (f ⊗₁ id) ∘ α⇐

-- The trace's own cup and cap.  `cupᵗʳ` is already `α⇐ ∘ cup-openʳ η`; `capᵗʳ`
-- closes `ε` after the braiding, so name that cap and fold `capᵗʳ` onto it.
capʳ : X ⊗₀ X ⁻¹ ⇒ unit
capʳ = ε ∘ σ⇒

-- `ε` and the braiding fuse into `capʳ`, leaving the cap's own associator.
capᵗʳ-fold : capᵗʳ {A} {X} ≈ cap-closeʳ capʳ ∘ α⇒
capᵗʳ-fold = (refl⟩∘⟨ pullˡ merge₂ˡ) ○ sym-assoc

-- ... and that associator joins `f`'s whisker to make the loop `⇒⦑ f ⦒⇐`.
trace-fold : {f : A ⊗₀ X ⇒ B ⊗₀ X} →
  trace f ≈ cap-closeʳ capʳ ∘ ⇒⦑ f ⦒⇐ ∘ cup-openʳ η
trace-fold = (capᵗʳ-fold ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ ⟺ assoc²βε)

------------------------------------------------------------------------
-- Superposing.  A wire `Y` running beside the loop never meets it, so it slides
-- out of the trace: tracing `f` with `Y` alongside is `Y` alongside the trace of
-- `f`.  The associators of `capᵗʳ`/`cupᵗʳ` whisker `Y` off, and `α-conj-slide`
-- pushes the whisker through the loop.
--
--     Y      B         X ────────╮            Y          B
--     │      │         │         │            │          │
--     │   ┌──┴─────────┴──┐      │            │       ╭──┴───────────╮
--     │   │       f       │      │      =     │       │   trace f    │
--     │   └──┬─────────┬──┘      │            │       ╰──┬───────────╯
--     │      │         │         │            │          │
--     Y      A         X ────────╯            Y          A
--
--     trace (α⇐ ∘ (id ⊗₁ f) ∘ α⇒)                 id ⊗₁ trace f

superposing : {f : A ⊗₀ X ⇒ B ⊗₀ X} →
  trace (α⇐ ∘ (id {Y} ⊗₁ f) ∘ α⇒) ≈ id ⊗₁ trace f
superposing {f = f} = begin
  capᵗʳ ∘ (superposed ⊗₁ id) ∘ α⇐ ∘ cup-openʳ η
    ≈⟨ capᵗʳ-fold ⟩∘⟨refl ⟩
  (cap-closeʳ capʳ ∘ α⇒) ∘ (superposed ⊗₁ id) ∘ α⇐ ∘ cup-openʳ η
    ≈⟨ cap-closeʳ-assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
  (((id ⊗₁ cap-closeʳ capʳ) ∘ α⇒) ∘ α⇒) ∘ (superposed ⊗₁ id) ∘ α⇐ ∘ cup-openʳ η
    ≈⟨ assoc²αε ⟩
  (id ⊗₁ cap-closeʳ capʳ) ∘ α⇒ ∘ α⇒ ∘ (superposed ⊗₁ id) ∘ α⇐ ∘ cup-openʳ η
    ≈⟨ refl⟩∘⟨ reassoc-tail₅ ⟩
  (id ⊗₁ cap-closeʳ capʳ) ∘ (α⇒ ∘ α⇒ ∘ (superposed ⊗₁ id) ∘ α⇐) ∘ cup-openʳ η
    ≈⟨ refl⟩∘⟨ α-conj-slide ⟩∘⟨refl ⟩
  (id ⊗₁ cap-closeʳ capʳ) ∘ ((id ⊗₁ ⇒⦑ f ⦒⇐) ∘ α⇒) ∘ cup-openʳ η
    ≈⟨ refl⟩∘⟨ pullʳ cup-openʳ-natural ⟩
  (id ⊗₁ cap-closeʳ capʳ) ∘ (id ⊗₁ ⇒⦑ f ⦒⇐) ∘ (id ⊗₁ cup-openʳ η)
    ≈⟨ refl⟩∘⟨ merge₂ˡ ⟩
  (id ⊗₁ cap-closeʳ capʳ) ∘ (id ⊗₁ (⇒⦑ f ⦒⇐ ∘ cup-openʳ η))
    ≈⟨ merge₂ˡ ⟩
  id ⊗₁ (cap-closeʳ capʳ ∘ ⇒⦑ f ⦒⇐ ∘ cup-openʳ η)
    ≈˘⟨ refl⟩⊗⟨ trace-fold ⟩
  id ⊗₁ trace f                                                              ∎
  where
    superposed = α⇐ ∘ (id ⊗₁ f) ∘ α⇒

------------------------------------------------------------------------
-- The canonical trace, packaged.  It is a full trace but for `vanishing₂`
-- (`Trace.Construction`); the axioms above already make it a `PreTrace`, which is
-- all `Trace.Uniqueness` needs to pin it down as the *only* trace here.

preTrace : PreTrace symmetric
preTrace = record
  { trace        = trace
  ; trace-resp-≈ = trace-resp-≈
  ; tightenₗ     = tightenₗ
  ; tightenᵣ     = tightenᵣ
  ; superposing  = superposing
  ; yanking      = yanking
  }
