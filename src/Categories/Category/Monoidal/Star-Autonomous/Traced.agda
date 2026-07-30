{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Traced using (Traced)

-- Traced ∗-autonomous categories are compact closed (Hajgató & Hasegawa, TAC
-- 28(7), 2013).  A traced ∗-autonomous category is a symmetric monoidal closed
-- category with a trace on its symmetric monoidal structure and a dualizing
-- object `⊥`.  Its unit map `t : unit ⇒ X ⊗₀ X *` is produced from the trace of
-- evaluation, and — after correcting by `t {unit} ⁻¹` — satisfies the two snake
-- equations, so the category is compact closed (`Closed/CompactClosed.agda`).
--
-- This is the paper's §3, split across:
--   * `Traced/Base.agda`    — `τ` and its dinaturality (Lemma 3.1), the
--                             symmetric-closed isos, `δ`, `IsDualizing`;
--   * `Traced/Duality.agda` — the dualizing object, `φ` (Lemma 3.2), the unit
--                             `t` (Corollary 3.4), Lemma 3.5, the hexagon.
-- This file assembles them and hands `t` to `Closed/CompactClosed.agda`
-- (their Prop 2.1) to produce compact closure.

module Categories.Category.Monoidal.Star-Autonomous.Traced
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (Cl : Closed M) (T : Traced M) where

open Category 𝒞 using (Obj)
open Traced T using (symmetric)

open import Categories.Category.Monoidal.CompactClosed M using (CompactClosed)
open import Categories.Category.Monoidal.Star-Autonomous.Traced.Base Cl T public
  using (IsDualizing)

import Categories.Category.Monoidal.Closed.CompactClosed as ClosedCompactClosed
import Categories.Category.Monoidal.Star-Autonomous.Traced.Duality as Duality

module Dualized (⊥ : Obj) (dualizing : IsDualizing ⊥) where

  open Duality.Dualized Cl T ⊥ dualizing public

  compactClosed : CompactClosed
  compactClosed =
    ClosedCompactClosed.compactClosed Cl t t-extranatural t-unit symmetric
