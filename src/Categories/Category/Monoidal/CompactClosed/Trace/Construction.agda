{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)
open import Categories.Category.Monoidal.CompactClosed using (CompactClosed)

-- The two structural JSV trace axioms for a compact closed category: `superposing`
-- (the trace commutes with whiskering) and `vanishing₂` (a trace over `X ⊗₀ Y`
-- is a trace over `X` of a trace over `Y`).  The remaining axioms — `yanking`,
-- `vanishing₁`, `trace-slide` and the two tightenings — live in `Trace.Definition`.
-- Joyal, Street & Verity, "Traced monoidal categories" (1996), §5.

module Categories.Category.Monoidal.CompactClosed.Trace.Construction
    {o ℓ e} {𝒞 : Category o ℓ e}
    (M : Monoidal 𝒞)
    (K : CompactClosed M) where

open Category 𝒞
open CompactClosed K
open LeftRigid leftRigid

open import Categories.Category.Monoidal.CompactClosed.Trace.Definition M K
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided symmetric)
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided symmetric)
open import Categories.Category.Monoidal.Interchange.Symmetric symmetric
open import Categories.Category.Monoidal.Symmetric.Properties symmetric
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.Rigid.Dual M leftRigid
open import Categories.Category.Monoidal.Rigid.Properties M as RigidProps
open RigidProps.Left leftRigid
  renaming (⁻¹-flip-⊗ to ξ ; ⁻¹-flip-⊗-cup to ξ-cup ; ⁻¹-flip-⊗-cap to ξ-cap)
import Categories.Category.Monoidal.Utilities M as MonUtil
open MonUtil.Shorthands
open BraidShorthands

private
  variable
    A B X Y Z : Obj

  i⇒ : (A ⊗₀ X) ⊗₀ (Y ⊗₀ B) ⇒ (A ⊗₀ Y) ⊗₀ (X ⊗₀ B)
  i⇒ = swapInner.from

  -- At the unit both unitors agree, so the braiding is invisible to `ρ⇒`.
  braiding-coherence-unit : ρ⇒ {unit} ∘ σ⇒ {unit} {unit} ≈ ρ⇒
  braiding-coherence-unit = braiding-coherence′ ○ coherence₃

------------------------------------------------------------------------
-- Vanishing₂: two loops, taken one at a time, are one loop around both wires.
-- Tracing out `Y` and then `X` closes the legs one inside the other; tracing out
-- the pair `X ⊗₀ Y` closes them together.  Same picture, different bookkeeping —
-- and the bookkeeping is the entire proof below.
--
--     B      X ───────────────╮              B      X ──────────╮
--     │      │    Y ──────╮   │              │      │    Y ─────┼──╮
--     │      │    │       │   │              │      │    │      │  │
--   ┌─┴──────┴────┴──┐    │   │            ┌─┴──────┴────┴──┐   │  │
--   │        f       │    │   │      =     │        f       │   │  │
--   └─┬──────┬────┬──┘    │   │            └─┬──────┬────┬──┘   │  │
--     │      │    │       │   │              │      │    │      │  │
--     A      X    Y ──────╯   │              A      X    Y ─────┼──╯
--            ╰───────────────╯                      ╰──────────╯
--
--       trace (trace ⇐[ f ]⇒)                  trace f   (one loop, of `X ⊗₀ Y`)
--
-- The trace over `X ⊗₀ Y` bends its wire through the genuine dual
-- `(X ⊗₀ Y) ⁻¹`, while the double trace bends it through `Y ⁻¹` and then `X ⁻¹`,
-- i.e. through the tensor dual `[ X ⊗ Y ]⁻¹`.  Transport the trace along the flip
-- iso `⁻¹-flip-⊗`, then match the double trace's cup and cap against `⊗-cup`
-- and `⊗-cap`.

private
  TraceMap : Obj → Obj → Obj → Obj → Set _
  TraceMap A B X Y = A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)

  ⇐[_]⇒ : TraceMap A B X Y → (A ⊗₀ X) ⊗₀ Y ⇒ (B ⊗₀ X) ⊗₀ Y
  ⇐[ f ]⇒ = α⇐ ∘ f ∘ α⇒

  ----------------------------------------------------------------------
  -- Step 1: `trace f` is the trace of `f` through the tensor dual.
  --
  -- `flip-dual` is the flip iso `ξ`, applied on the dual wire alone.  It carries
  -- each of the trace's three parts to the tensor dual's: the cup (`flip-cup`), the
  -- cap (`flip-cap`, past the braiding), and `f`'s loop (`flip-natural`), which
  -- never touches the dual wire at all.

  flip-dual : A ⊗₀ ((X ⊗₀ Y) ⊗₀ [ X ⊗ Y ]⁻¹) ⇒ A ⊗₀ ((X ⊗₀ Y) ⊗₀ (X ⊗₀ Y) ⁻¹)
  flip-dual = id ⊗₁ (id ⊗₁ ξ)

  trace-⊗dual : TraceMap A B X Y → A ⇒ B
  trace-⊗dual f = cap-closeʳ (⊗-cap ∘ σ⇒) ∘ ⇒⦑ f ⦒⇐ ∘ cup-openʳ ⊗-cup

  flip-cup : cup-openʳ {A = A} (η {X ⊗₀ Y}) ≈ flip-dual ∘ cup-openʳ ⊗-cup
  flip-cup = ⟺ ((refl⟩⊗⟨ ξ-cup) ⟩∘⟨refl) ○ pushˡ split₂ˡ

  flip-cap : cap-closeʳ {A = B} (capʳ {X ⊗₀ Y}) ∘ flip-dual ≈ cap-closeʳ (⊗-cap ∘ σ⇒)
  flip-cap = pullʳ merge₂ˡ ○ (refl⟩∘⟨ refl⟩⊗⟨ (pullʳ σ⇒-comm ○ pullˡ ξ-cap))

  flip-natural : {f : TraceMap A B X Y} →
    ⇒⦑ f ⦒⇐ ∘ flip-dual ≈ flip-dual ∘ ⇒⦑ f ⦒⇐
  flip-natural {f = f} = begin
    ⇒⦑ f ⦒⇐ ∘ flip-dual                   ≈⟨ assoc²βε ⟩
    α⇒ ∘ (f ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ ξ))  ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ α⇐-id⊗-commute ⟩
    α⇒ ∘ (f ⊗₁ id) ∘ (id ⊗₁ ξ) ∘ α⇐          ≈⟨ refl⟩∘⟨ extendʳ whisker-comm ⟩
    α⇒ ∘ (id ⊗₁ ξ) ∘ (f ⊗₁ id) ∘ α⇐          ≈⟨ extendʳ α⇒-id⊗-commute ⟩
    flip-dual ∘ ⇒⦑ f ⦒⇐                   ∎

  trace≈⊗dual : {f : TraceMap A B X Y} → trace f ≈ trace-⊗dual f
  trace≈⊗dual {f = f} = begin
    trace f                                    ≈⟨ trace-fold ⟩
    cap-closeʳ capʳ ∘ ⇒⦑ f ⦒⇐ ∘ cup-openʳ η    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ flip-cup ⟩
    cap-closeʳ capʳ ∘ ⇒⦑ f ⦒⇐ ∘ flip-dual ∘ cup-openʳ ⊗-cup
      ≈⟨ refl⟩∘⟨ extendʳ flip-natural ⟩
    cap-closeʳ capʳ ∘ flip-dual ∘ ⇒⦑ f ⦒⇐ ∘ cup-openʳ ⊗-cup
      ≈⟨ pullˡ flip-cap ⟩
    trace-⊗dual f                              ∎

  ----------------------------------------------------------------------
  -- Step 2: the double trace, and `pairing`, which reassociates its carrier
  -- into `A`, the traced object `X ⊗₀ Y`, and the tensor dual.

  DoubleTrace : Obj → Obj → Obj → Obj
  DoubleTrace A X Y = (((A ⊗₀ X) ⊗₀ Y) ⊗₀ Y ⁻¹) ⊗₀ X ⁻¹

  double-cup : A ⇒ DoubleTrace A X Y
  double-cup = (cupᵗʳ ⊗₁ id) ∘ cupᵗʳ

  double-map : TraceMap A B X Y → DoubleTrace A X Y ⇒ DoubleTrace B X Y
  double-map f = (⇐[ f ]⇒ ⊗₁ id) ⊗₁ id

  double-cap : DoubleTrace B X Y ⇒ B
  double-cap = capᵗʳ ∘ (capᵗʳ ⊗₁ id)

  -- Three carries: two to slide the traced pair `X ⊗₀ Y` out of the double trace's
  -- left-nested carrier, one more to split it from the tensor dual.  The first two
  -- get their own name because `pairing-natural` factors through exactly them — and
  -- it uses them at *two* object instances, so they cannot be a local abbreviation.
  pairingₗ : DoubleTrace A X Y ⇒ (A ⊗₀ (X ⊗₀ Y)) ⊗₀ [ X ⊗ Y ]⁻¹
  pairingₗ = α⇒ ∘ ((α⇒ ⊗₁ id) ⊗₁ id)

  pairing : DoubleTrace A X Y ⇒ A ⊗₀ ((X ⊗₀ Y) ⊗₀ [ X ⊗ Y ]⁻¹)
  pairing = α⇒ ∘ pairingₗ

  -- `pairing` is natural: the double map is `f` twice whiskered, and the carries
  -- walk it out to the front.  Under `pairingₗ` `f` comes out bare; the last carry
  -- then re-grows the `α⇐` that `⇒⦑_⦒⇐` wants.
  pairing-natural : (f : TraceMap A B X Y) →
    pairing ∘ double-map f ≈ ⇒⦑ f ⦒⇐ ∘ pairing
  pairing-natural f = begin
    pairing ∘ double-map f                            ≈⟨ assoc ⟩
    α⇒ ∘ pairingₗ ∘ double-map f                      ≈⟨ refl⟩∘⟨ pullʳ merge₁ˡ ⟩
    α⇒ ∘ α⇒ ∘ (((α⇒ ⊗₁ id) ∘ (⇐[ f ]⇒ ⊗₁ id)) ⊗₁ id)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ˡ ⟩⊗⟨refl ⟩
    α⇒ ∘ α⇒ ∘ (((α⇒ ∘ ⇐[ f ]⇒) ⊗₁ id) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoʳ ⟩⊗⟨refl ⟩⊗⟨refl ⟩
    α⇒ ∘ α⇒ ∘ (((f ∘ α⇒) ⊗₁ id) ⊗₁ id)                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩⊗⟨refl ⟩
    α⇒ ∘ α⇒ ∘ (((f ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ⊗₁ id)        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
    α⇒ ∘ α⇒ ∘ ((f ⊗₁ id) ⊗₁ id) ∘ ((α⇒ ⊗₁ id) ⊗₁ id)  ≈⟨ refl⟩∘⟨ extendʳ α⇒-⊗id-commute ⟩
    α⇒ ∘ (f ⊗₁ id) ∘ pairingₗ                          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoˡ ⟩
    α⇒ ∘ (f ⊗₁ id) ∘ α⇐ ∘ α⇒ ∘ pairingₗ                ≈⟨ assoc²εβ ⟩
    ⇒⦑ f ⦒⇐ ∘ pairing                              ∎

  ----------------------------------------------------------------------
  -- Step 3: the cup boundary.  Both cups are associator-only, so `pairing`
  -- carries the two nested trace-cups to `⊗-cup` by pentagon bookkeeping.

  -- Coherence: `(α⇒ ⊗₁ id) ∘ α⇐` re-brackets into an `α⇐`-headed form.
  assoc-rebracket : (α⇒ {A} {B} {X} ⊗₁ id {Y}) ∘ α⇐ ≈ α⇐ ∘ (id ⊗₁ α⇐) ∘ α⇒
  assoc-rebracket = ⟺ (cancelˡ associator.isoˡ) ○ (refl⟩∘⟨ ⟺ assoc-to-coherence)

  -- The two associators `pairing` leaves on the far side of the dual, and the two
  -- carries it makes on the near side.  Both boundaries are stated in terms of them.
  regroup : (X ⊗₀ (Y ⊗₀ Y ⁻¹)) ⊗₀ X ⁻¹ ⇒ (X ⊗₀ Y) ⊗₀ [ X ⊗ Y ]⁻¹
  regroup = α⇒ ∘ (α⇐ ⊗₁ id)

  pairing-core : DoubleTrace A X Y ⇒ A ⊗₀ ((X ⊗₀ (Y ⊗₀ Y ⁻¹)) ⊗₀ X ⁻¹)
  pairing-core = α⇒ ∘ (α⇒ ⊗₁ id) ∘ (α⇒ ⊗₁ id)

  -- `pairing` met by the inner cup's associator: its two outer associators
  -- collapse against it by the pentagon, whiskering `A` off and leaving `regroup`.
  pairing-cup-head :
    pairing {A} {X} {Y} ∘ (α⇐ ⊗₁ id) ≈ (id ⊗₁ regroup) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
  pairing-cup-head = begin
    pairing ∘ (α⇐ ⊗₁ id)                             ≈⟨ assoc²βε ⟩
    α⇒ ∘ α⇒ ∘ ((α⇒ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id)        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ˡ ⟩
    α⇒ ∘ α⇒ ∘ (((α⇒ ⊗₁ id) ∘ α⇐) ⊗₁ id)              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-rebracket ⟩⊗⟨refl ⟩
    α⇒ ∘ α⇒ ∘ ((α⇐ ∘ (id ⊗₁ α⇐) ∘ α⇒) ⊗₁ id)         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
    α⇒ ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ (((id ⊗₁ α⇐) ∘ α⇒) ⊗₁ id) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
    α⇒ ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ α⇐) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈⟨ assoc²εα ⟩
    ((α⇒ ∘ α⇒) ∘ (α⇐ ⊗₁ id)) ∘ ((id ⊗₁ α⇐) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈⟨ pentagon-collapse ⟩∘⟨refl ⟩
    ((id ⊗₁ α⇒) ∘ α⇒) ∘ ((id ⊗₁ α⇐) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈⟨ assoc ⟩
    (id ⊗₁ α⇒) ∘ α⇒ ∘ ((id ⊗₁ α⇐) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
    (id ⊗₁ α⇒) ∘ (id ⊗₁ (α⇐ ⊗₁ id)) ∘ α⇒ ∘ (α⇒ ⊗₁ id)  ≈⟨ pullˡ merge₂ˡ ⟩
    (id ⊗₁ regroup) ∘ α⇒ ∘ (α⇒ ⊗₁ id)                  ∎

  -- What is left of the double cup after that fusion sits entirely on `X`.
  cup-tail : α⇒ {A} {X ⊗₀ (Y ⊗₀ Y ⁻¹)} {X ⁻¹}
               ∘ (α⇒ ⊗₁ id) ∘ (cup-openʳ η ⊗₁ id) ∘ α⇐
             ≈ id ⊗₁ (cup-openʳ η ⊗₁ id)
  cup-tail = begin
    α⇒ ∘ (α⇒ ⊗₁ id) ∘ (cup-openʳ η ⊗₁ id) ∘ α⇐  ≈⟨ refl⟩∘⟨ pullˡ merge₁ˡ ⟩
    α⇒ ∘ ((α⇒ ∘ cup-openʳ η) ⊗₁ id) ∘ α⇐        ≈⟨ refl⟩∘⟨ cup-openʳ-natural ⟩⊗⟨refl ⟩∘⟨refl ⟩
    α⇒ ∘ ((id ⊗₁ cup-openʳ η) ⊗₁ id) ∘ α⇐       ≈⟨ pullˡ assoc-commute-from ⟩
    ((id ⊗₁ (cup-openʳ η ⊗₁ id)) ∘ α⇒) ∘ α⇐     ≈⟨ cancelʳ associator.isoʳ ⟩
    id ⊗₁ (cup-openʳ η ⊗₁ id)                   ∎

  -- The two nested trace-cups, reassociated, are `⊗-cup` with `A` whiskered on.
  cup-boundary : pairing {A} {X} {Y} ∘ (cupᵗʳ ⊗₁ id) ∘ α⇐
                 ≈ id ⊗₁ (α⇐ ∘ (id ⊗₁ cupˡ))
  cup-boundary = begin
    pairing ∘ ((α⇐ ∘ cup-openʳ η) ⊗₁ id) ∘ α⇐
      ≈⟨ (refl⟩∘⟨ split₁ˡ ⟩∘⟨refl) ○ assoc²δγ ⟩
    (pairing ∘ (α⇐ ⊗₁ id)) ∘ (cup-openʳ η ⊗₁ id) ∘ α⇐    ≈⟨ pairing-cup-head ⟩∘⟨refl ⟩
    ((id ⊗₁ regroup) ∘ α⇒ ∘ (α⇒ ⊗₁ id)) ∘ (cup-openʳ η ⊗₁ id) ∘ α⇐
      ≈⟨ assoc²βε ⟩
    (id ⊗₁ regroup) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ (cup-openʳ η ⊗₁ id) ∘ α⇐
      ≈⟨ refl⟩∘⟨ cup-tail ⟩
    (id ⊗₁ regroup) ∘ (id ⊗₁ (cup-openʳ η ⊗₁ id))       ≈⟨ merge₂ˡ ⟩
    id ⊗₁ (regroup ∘ (cup-openʳ η ⊗₁ id))
      ≈⟨ refl⟩⊗⟨ (assoc ○ (refl⟩∘⟨ refl⟩∘⟨ split₁ˡ)) ⟩
    id ⊗₁ (α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ η) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id))
      ≈˘⟨ refl⟩⊗⟨ cupˡ-expand ⟩
    id ⊗₁ (α⇐ ∘ (id ⊗₁ cupˡ))                                                ∎

  pairing-cup : pairing {A} {X} {Y} ∘ double-cup ≈ cup-openʳ ⊗-cup
  pairing-cup = begin
    pairing ∘ (cupᵗʳ ⊗₁ id) ∘ (α⇐ ∘ cup-openʳ η)  ≈⟨ assoc²εβ ⟩
    (pairing ∘ (cupᵗʳ ⊗₁ id) ∘ α⇐) ∘ cup-openʳ η  ≈⟨ cup-boundary ⟩∘⟨refl ⟩
    (id ⊗₁ (α⇐ ∘ (id ⊗₁ cupˡ))) ∘ (id ⊗₁ η) ∘ ρ⇐  ≈⟨ pullˡ merge₂ˡ ⟩
    (id ⊗₁ ((α⇐ ∘ (id ⊗₁ cupˡ)) ∘ η)) ∘ ρ⇐        ≈⟨ (refl⟩⊗⟨ assoc) ⟩∘⟨refl ⟩
    cup-openʳ ⊗-cup                               ∎

  ----------------------------------------------------------------------
  -- Step 4: the cap boundary.  Two nested caps are two parallel caps, once the
  -- four-middle interchange has put each cap's own two wires side by side.
  -- `⊗-cap` is `nest ε ε` and the two nested trace-caps are `nest capʳ capʳ`, so
  -- one lemma does both.
  --
  --     A     X     Y     B              A     X     Y     B
  --     │     │     │     │              │      ╲   ╱      │
  --     │     ╰──d──╯     │              │       ╲ ╱       │      `i⇒` crosses the
  --     │                 │       =      │        ╳        │      middle pair and
  --     ╰────────c────────╯              │       ╱ ╲       │      `σ⇒` brings `B`
  --                                      ╰──c───╯   ╰───d──╯      across, so `c`
  --                                                               and `d` end up
  --          nest c d              ρ⇒ ∘ (c ⊗₁ d) ∘ i⇒ ∘ (id ⊗₁ σ⇒)   side by side

  nest : (A ⊗₀ B ⇒ unit) → (X ⊗₀ Y ⇒ unit) → (A ⊗₀ X) ⊗₀ (Y ⊗₀ B) ⇒ unit
  nest c d = c ∘ ((cap-closeʳ d ∘ α⇒) ⊗₁ id) ∘ α⇐

  -- Sliding `B` leftwards past the `d`-cap to meet `c` is braiding naturality.
  cap-slide : {d : X ⊗₀ Y ⇒ unit} →
    cap-closeʳ d ∘ swapˡ ∘ (id ⊗₁ σ⇒ {Y} {B}) ≈ λ⇒ ∘ (d ⊗₁ id) ∘ α⇐
  cap-slide {d = d} = begin
    cap-closeʳ d ∘ swapˡ ∘ (id ⊗₁ σ⇒) ≈˘⟨ refl⟩∘⟨ swapˡ-hexagon ⟩
    cap-closeʳ d ∘ σ⇒ ∘ α⇐            ≈⟨ assoc ⟩
    ρ⇒ ∘ (id ⊗₁ d) ∘ σ⇒ ∘ α⇐          ≈˘⟨ refl⟩∘⟨ extendʳ σ⇒-comm ⟩
    ρ⇒ ∘ σ⇒ ∘ (d ⊗₁ id) ∘ α⇐          ≈⟨ pullˡ braiding-coherence′ ⟩
    λ⇒ ∘ (d ⊗₁ id) ∘ α⇐               ∎

  nest-swap : {c : A ⊗₀ B ⇒ unit} {d : X ⊗₀ Y ⇒ unit} →
    nest c d ≈ ρ⇒ ∘ (c ⊗₁ d) ∘ i⇒ ∘ (id ⊗₁ σ⇒)
  nest-swap {c = c} {d} = ⟺ (begin
    ρ⇒ ∘ (c ⊗₁ d) ∘ i⇒ ∘ (id ⊗₁ σ⇒)                          ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩∘⟨refl ⟩
    ρ⇒ ∘ ((c ⊗₁ id) ∘ (id ⊗₁ d)) ∘ i⇒ ∘ (id ⊗₁ σ⇒)           ≈⟨ pullˡ (pullˡ unitorʳ-commute-from) ⟩
    ((c ∘ ρ⇒) ∘ (id ⊗₁ d)) ∘ i⇒ ∘ (id ⊗₁ σ⇒)                 ≈⟨ assoc ⟩∘⟨refl ⟩
    (c ∘ cap-closeʳ d) ∘ i⇒ ∘ (id ⊗₁ σ⇒)                     ≈⟨ assoc²γδ ⟩
    c ∘ (cap-closeʳ d ∘ i⇒) ∘ (id ⊗₁ σ⇒)                     ≈⟨ refl⟩∘⟨ cap-close-i⇒ ⟩∘⟨refl ⟩
    c ∘ ((id ⊗₁ (cap-closeʳ d ∘ swapˡ)) ∘ α⇒) ∘ (id ⊗₁ σ⇒)   ≈⟨ refl⟩∘⟨ pullʳ α⇒-id⊗-commute ⟩
    c ∘ (id ⊗₁ (cap-closeʳ d ∘ swapˡ)) ∘ (id ⊗₁ (id ⊗₁ σ⇒)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    c ∘ (id ⊗₁ ((cap-closeʳ d ∘ swapˡ) ∘ (id ⊗₁ σ⇒))) ∘ α⇒   ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ assoc) ⟩∘⟨refl ⟩
    c ∘ (id ⊗₁ (cap-closeʳ d ∘ swapˡ ∘ (id ⊗₁ σ⇒))) ∘ α⇒     ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ cap-slide) ⟩∘⟨refl ⟩
    c ∘ (id ⊗₁ (λ⇒ ∘ (d ⊗₁ id) ∘ α⇐)) ∘ α⇒                   ≈⟨ refl⟩∘⟨ cap-reassoc ⟩
    nest c d                                                 ∎)
    where
      -- The interchange moves the `c`-pair out of the `d`-cap's way.
      cap-close-i⇒ : cap-closeʳ d ∘ i⇒ ≈ (id ⊗₁ (cap-closeʳ d ∘ swapˡ)) ∘ α⇒
      cap-close-i⇒ = pullˡ cap-closeʳ-natural ○ pullˡ merge₂ˡ

  -- Braiding each pair after the interchange is braiding the whole block.
  braid-core :
    (σ⇒ {A} {B} ⊗₁ σ⇒ {X} {Y}) ∘ i⇒ ∘ (id ⊗₁ σ⇒ {Y} {B})
    ≈ σ⇒ {Y ⊗₀ X} {B ⊗₀ A} ∘ i⇒ ∘ (id ⊗₁ σ⇒ {A} {X}) ∘ σ⇒ {A ⊗₀ X} {Y ⊗₀ B}
  braid-core = begin
    (σ⇒ ⊗₁ σ⇒) ∘ i⇒ ∘ (id ⊗₁ σ⇒)              ≈⟨ sym-assoc ⟩
    ((σ⇒ ⊗₁ σ⇒) ∘ i⇒) ∘ (id ⊗₁ σ⇒)            ≈˘⟨ cancelˡ swapInner-commutative ⟩∘⟨refl ⟩
    (i⇒ ∘ i⇒ ∘ (σ⇒ ⊗₁ σ⇒) ∘ i⇒) ∘ (id ⊗₁ σ⇒)  ≈⟨ (refl⟩∘⟨ swapInner-braiding) ⟩∘⟨refl ⟩
    (i⇒ ∘ σ⇒) ∘ (id ⊗₁ σ⇒)                    ≈⟨ pullʳ σ⇒-comm ⟩
    i⇒ ∘ (σ⇒ ⊗₁ id) ∘ σ⇒                      ≈⟨ pullˡ swapInner-braidˡ ⟩
    (σ⇒ ∘ i⇒ ∘ (id ⊗₁ σ⇒)) ∘ σ⇒               ≈⟨ assoc²βε ⟩
    σ⇒ ∘ i⇒ ∘ (id ⊗₁ σ⇒) ∘ σ⇒                 ∎

  cap-nest : (X ⊗₀ Y) ⊗₀ [ X ⊗ Y ]⁻¹ ⇒ X ⊗₀ X ⁻¹
  cap-nest = (capᵗʳ ⊗₁ id) ∘ α⇐

  cap-boundary : capʳ ∘ cap-nest {X} {Y} ≈ ⊗-cap ∘ σ⇒
  cap-boundary = begin
    capʳ ∘ (capᵗʳ ⊗₁ id) ∘ α⇐                      ≈⟨ refl⟩∘⟨ capᵗʳ-fold ⟩⊗⟨refl ⟩∘⟨refl ⟩
    nest capʳ capʳ                                 ≈⟨ nest-swap ⟩
    ρ⇒ ∘ (capʳ ⊗₁ capʳ) ∘ i⇒ ∘ (id ⊗₁ σ⇒)
      ≈⟨ refl⟩∘⟨ ((⊗-distrib-over-∘ ⟩∘⟨refl) ○ assoc) ⟩
    ρ⇒ ∘ (ε ⊗₁ ε) ∘ (σ⇒ ⊗₁ σ⇒) ∘ i⇒ ∘ (id ⊗₁ σ⇒)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braid-core ⟩
    ρ⇒ ∘ (ε ⊗₁ ε) ∘ σ⇒ ∘ i⇒ ∘ (id ⊗₁ σ⇒) ∘ σ⇒      ≈˘⟨ refl⟩∘⟨ extendʳ σ⇒-comm ⟩
    ρ⇒ ∘ σ⇒ ∘ (ε ⊗₁ ε) ∘ i⇒ ∘ (id ⊗₁ σ⇒) ∘ σ⇒      ≈⟨ pullˡ braiding-coherence-unit ⟩
    ρ⇒ ∘ (ε ⊗₁ ε) ∘ i⇒ ∘ (id ⊗₁ σ⇒) ∘ σ⇒           ≈⟨ reassoc-tail₅ ⟩
    (ρ⇒ ∘ (ε ⊗₁ ε) ∘ i⇒ ∘ (id ⊗₁ σ⇒)) ∘ σ⇒         ≈˘⟨ nest-swap ⟩∘⟨refl ⟩
    nest ε ε ∘ σ⇒                                  ≈˘⟨ (refl⟩∘⟨ cap-reassoc) ⟩∘⟨refl ⟩
    ⊗-cap ∘ σ⇒                                     ∎

  ----------------------------------------------------------------------
  -- Step 5: `pairing` conjugates the double cap into the tensor-dual cap.

  -- `pairing` is `pairing-core` once `regroup` is peeled off the far side: insert
  -- the inner cup's associator and its inverse, then apply `pairing-cup-head`.
  pairing-expand : pairing {A} {X} {Y} ≈ (id ⊗₁ regroup) ∘ pairing-core
  pairing-expand = ⟺ (cancelʳ (⊗-cancel associator.isoˡ identity²))
                 ○ (pairing-cup-head ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ assoc)

  cap-nest-regroup : cap-nest {X} {Y} ∘ regroup ≈ cap-closeʳ capʳ ⊗₁ id
  cap-nest-regroup = begin
    ((capᵗʳ ⊗₁ id) ∘ α⇐) ∘ α⇒ ∘ (α⇐ ⊗₁ id)  ≈⟨ assoc ⟩
    (capᵗʳ ⊗₁ id) ∘ α⇐ ∘ α⇒ ∘ (α⇐ ⊗₁ id)    ≈⟨ refl⟩∘⟨ cancelˡ associator.isoˡ ⟩
    (capᵗʳ ⊗₁ id) ∘ (α⇐ ⊗₁ id)              ≈⟨ merge₁ˡ ⟩
    (capᵗʳ ∘ α⇐) ⊗₁ id                      ≈⟨ (capᵗʳ-fold ⟩∘⟨refl) ⟩⊗⟨refl ⟩
    ((cap-closeʳ capʳ ∘ α⇒) ∘ α⇐) ⊗₁ id     ≈⟨ cancelʳ associator.isoʳ ⟩⊗⟨refl ⟩
    cap-closeʳ capʳ ⊗₁ id                   ∎

  -- With the inner cap closed, `α⇒` in front of the outer one *is* `pairing`: the
  -- outer cap's own associator, plus the two `pairing-core` carries, and `regroup`
  -- absorbs what is left of `cap-nest`.
  double-cap-head : α⇒ {A} {X} {X ⁻¹} ∘ (capᵗʳ {A ⊗₀ X} {Y} ⊗₁ id)
                    ≈ (id ⊗₁ cap-nest) ∘ pairing
  double-cap-head = begin
    α⇒ ∘ (capᵗʳ ⊗₁ id)                                  ≈⟨ refl⟩∘⟨ capᵗʳ-fold ⟩⊗⟨refl ⟩
    α⇒ ∘ ((cap-closeʳ capʳ ∘ α⇒) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ ((cap-closeʳ-assoc ⟩∘⟨refl) ⟩⊗⟨refl) ⟩
    α⇒ ∘ ((((id ⊗₁ cap-closeʳ capʳ) ∘ α⇒) ∘ α⇒) ⊗₁ id)   ≈⟨ refl⟩∘⟨ (assoc ⟩⊗⟨refl) ⟩
    α⇒ ∘ (((id ⊗₁ cap-closeʳ capʳ) ∘ α⇒ ∘ α⇒) ⊗₁ id)     ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    α⇒ ∘ ((id ⊗₁ cap-closeʳ capʳ) ⊗₁ id) ∘ ((α⇒ ∘ α⇒) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
    α⇒ ∘ ((id ⊗₁ cap-closeʳ capʳ) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈⟨ extendʳ assoc-commute-from ⟩
    (id ⊗₁ (cap-closeʳ capʳ ⊗₁ id)) ∘ pairing-core
      ≈˘⟨ (refl⟩⊗⟨ cap-nest-regroup) ⟩∘⟨refl ⟩
    (id ⊗₁ (cap-nest ∘ regroup)) ∘ pairing-core          ≈⟨ split₂ˡ ⟩∘⟨refl ⟩
    ((id ⊗₁ cap-nest) ∘ (id ⊗₁ regroup)) ∘ pairing-core  ≈⟨ assoc ⟩
    (id ⊗₁ cap-nest) ∘ (id ⊗₁ regroup) ∘ pairing-core    ≈˘⟨ refl⟩∘⟨ pairing-expand ⟩
    (id ⊗₁ cap-nest) ∘ pairing                           ∎

  pairing-cap : double-cap {B} {X} {Y} ≈ cap-closeʳ (⊗-cap ∘ σ⇒) ∘ pairing
  pairing-cap = begin
    capᵗʳ ∘ (capᵗʳ ⊗₁ id)                             ≈⟨ pushˡ capᵗʳ-fold ⟩
    cap-closeʳ capʳ ∘ α⇒ ∘ (capᵗʳ ⊗₁ id)              ≈⟨ refl⟩∘⟨ double-cap-head ⟩
    cap-closeʳ capʳ ∘ (id ⊗₁ cap-nest) ∘ pairing      ≈⟨ pullˡ (pullʳ merge₂ˡ) ⟩
    (ρ⇒ ∘ (id ⊗₁ (capʳ ∘ cap-nest))) ∘ pairing        ≈⟨ (refl⟩∘⟨ refl⟩⊗⟨ cap-boundary) ⟩∘⟨refl ⟩
    cap-closeʳ (⊗-cap ∘ σ⇒) ∘ pairing                 ∎

-- Vanishing₂: a trace over `X ⊗₀ Y` is a trace over `X` of a trace over `Y`.
vanishing₂ : {f : TraceMap A B X Y} → trace (trace (α⇐ ∘ f ∘ α⇒)) ≈ trace f
vanishing₂ {f = f} = begin
  -- The inner trace is a three-fold composite, so one `split₁³` distributes the
  -- outer cup's whisker over all of it at once, exposing the three factors.
  trace (trace (⇐[ f ]⇒))                                        ≈⟨ refl⟩∘⟨ split₁³ ⟩∘⟨refl ⟩
  capᵗʳ ∘ ((capᵗʳ ⊗₁ id) ∘ double-map f ∘ (cupᵗʳ ⊗₁ id)) ∘ cupᵗʳ  ≈⟨ refl⟩∘⟨ assoc²βε ⟩
  capᵗʳ ∘ (capᵗʳ ⊗₁ id) ∘ double-map f ∘ double-cup               ≈⟨ sym-assoc ⟩
  double-cap ∘ double-map f ∘ double-cup                          ≈⟨ pairing-cap ⟩∘⟨refl ⟩
  (cap-closeʳ (⊗-cap ∘ σ⇒) ∘ pairing) ∘ double-map f ∘ double-cup
    ≈⟨ assoc ⟩
  cap-closeʳ (⊗-cap ∘ σ⇒) ∘ pairing ∘ double-map f ∘ double-cup
    ≈⟨ refl⟩∘⟨ pullˡ (pairing-natural f) ⟩
  cap-closeʳ (⊗-cap ∘ σ⇒) ∘ (⇒⦑ f ⦒⇐ ∘ pairing) ∘ double-cup
    ≈⟨ refl⟩∘⟨ pullʳ pairing-cup ⟩
  trace-⊗dual f                                                  ≈˘⟨ trace≈⊗dual ⟩
  trace f                                                        ∎
