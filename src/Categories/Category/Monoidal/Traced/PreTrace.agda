{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Category.Monoidal.Traced.PreTrace
  {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open Category C

open import Level

open import Data.Product using (_,_)

open import Categories.Category.Monoidal.Symmetric M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Traced M using (Traced)

private
  variable
    A B X Y : Obj
    f g : A ⇒ B

------------------------------------------------------------------------------
-- A pre-trace is a trace stripped of its three "structural" axioms: dinaturality
-- (`slide`) and the two vanishings.  What is left — the two tightenings,
-- `superposing` and `yanking` — is exactly what makes a trace unique on a compact
-- closed category (Hasegawa, "On traced monoidal closed categories", MSCS 19(2),
-- 2009, Appendix B, Proposition B.1).
--
-- It is *indexed* by the symmetric structure it braids over rather than carrying
-- its own, so a pre-trace over `S` and `S`'s own braiding are the same `σ⇒` by
-- construction: uniqueness over `S` needs no hypothesis relating the two braidings.

record PreTrace (S : Symmetric) : Set (levelOfTerm M) where
  open Symmetric S

  field
    trace : ∀ {X A B} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
    trace-resp-≈ : f ≈ g → trace f ≈ trace g

    -- naturality in A and B
    tightenₗ : trace (f ⊗₁ id ∘ g) ≈ f ∘ trace g
    tightenᵣ : trace (f ∘ g ⊗₁ id) ≈ trace f ∘ g

    superposing : trace {X = X} (associator.to ∘ id {Y} ⊗₁ f ∘ associator.from)
                ≈ id {Y} ⊗₁ trace {X = X} f
    yanking     : trace (braiding.⇒.η (X , X)) ≈ id

-- Every traced category is a pre-trace over its own braiding, forgetting `slide`,
-- `vanishing₁` and `vanishing₂`.
fromTraced : (T : Traced) → PreTrace (Traced.symmetric T)
fromTraced T = record
  { trace        = trace
  ; trace-resp-≈ = trace-resp-≈
  ; tightenₗ     = tightenₗ
  ; tightenᵣ     = tightenᵣ
  ; superposing  = superposing
  ; yanking      = yanking
  }
  where open Traced T
