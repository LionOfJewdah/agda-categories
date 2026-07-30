{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Traced using (Traced)

-- The dualizing object construction for a traced star-autonomous category.
-- `Construction` builds the comparison isomorphism and its unit; `Extranaturality`
-- proves the enriched hexagon consumed by the compact-closure construction.

module Categories.Category.Monoidal.Star-Autonomous.Traced.Duality
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (Cl : Closed M) (T : Traced M) where

open Category 𝒞 using (Obj)

open import Categories.Category.Monoidal.Star-Autonomous.Traced.Base Cl T public

import Categories.Category.Monoidal.Star-Autonomous.Traced.Duality.Construction as Construction
import Categories.Category.Monoidal.Star-Autonomous.Traced.Duality.Extranaturality as Extranaturality

module Dualized (⊥ : Obj) (dualizing : IsDualizing ⊥) where

  open Construction.Dualized Cl T ⊥ dualizing public
    using (_*; **-≅; ⊥*-≅; dualᵒ; **⁻¹-natural
          ; L₁; L₂; L₃; L₄; L₅; φ-NI; φ-≅
          ; t; t-unit)

  open Extranaturality.Dualized Cl T ⊥ dualizing public
    using (Extra-H; t-extranatural)
