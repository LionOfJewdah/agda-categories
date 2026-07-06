{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Monoidal coherence tactic.
--
-- `Core` exposes a free structural language for monoidal categories and its
-- interpretation in an arbitrary monoidal category.  `solve₀` proves
-- object-level canonical isomorphism goals, and `solve` proves equality of
-- interpreted structural paths whose normal-form loop computes to `refl`.
--------------------------------------------------------------------------------

module Categories.Tactic.Monoidal where

open import Function using (_⟨_⟩_)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.List using (List; []; _∷_)
open import Data.List.Properties using () renaming (≡-dec to ≡-dec-list)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Agda.Builtin.Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term using (_⋯⟅∷⟆_)
open import Reflection.TCM.Syntax

open import Categories.Tactic.Monoidal.Core public
open import Categories.Tactic.Monoidal.Coherence public
open import Categories.Tactic.Monoidal.Expression public
  using (solveMonoidalExpr)

import Categories.Tactic.Monoidal.Core as Core
open import Categories.Tactic.Monoidal.Free using (module Free)
import Categories.Tactic.Monoidal.Coherence as Coherence

module Finite
  {o ℓ e}
  {C : Category o ℓ e}
  (M : Monoidal C)
  where

  open Category C

  module SolverFor {n} (atom : Fin n → Obj) where
    module Sem = Core M atom
    open Sem public using (⟦_⟧₀; ⟦_⟧₁)
    open Free (Fin n) public
      renaming
        ( _⇒_  to _⇒ᶠ_
        ; _∘_  to _∘ᶠ_
        ; _⊗₁_ to _⊗ᶠ_
        ; _⊗_  to _⊗ᵒ_
        ; α⇒   to α⇒ᶠ
        ; α⇐   to α⇐ᶠ
        ; λ⇒   to λ⇒ᶠ
        ; λ⇐   to λ⇐ᶠ
        ; ρ⇒   to ρ⇒ᶠ
        ; ρ⇐   to ρ⇐ᶠ
        )

    private
      module Coherence′ = Coherence.WithUIP M atom
        (Decidable⇒UIP.≡-irrelevant (≡-dec-list _≟Fin_))

    solveᶠ : ∀ {X Y} (f g : X ⇒ᶠ Y) → Sem.⟦_⟧₁ f ≈ Sem.⟦_⟧₁ g
    solveᶠ = Coherence′.coherence-UIP

private
  getArgs : Term → Maybe (Term × Term)
  getArgs (def _ xs) = go xs
    where
    go : List (Arg Term) → Maybe (Term × Term)
    go (vArg x ∷ vArg y ∷ []) = just (x , y)
    go (x ∷ xs)               = go xs
    go _                      = nothing
  getArgs _ = nothing

  lastVisible : List (Arg Term) → Maybe Term
  lastVisible []              = nothing
  lastVisible (vArg x ∷ [])   = just x
  lastVisible (vArg x ∷ args) = maybe just (just x) (lastVisible args)
  lastVisible (_ ∷ args)      = lastVisible args

  getPath : Term → Maybe Term
  getPath (def _ args) = lastVisible args
  getPath (con _ args) = lastVisible args
  getPath _            = nothing

  getPaths : Term → Maybe (Term × Term)
  getPaths goal = maybe paths nothing (getArgs goal)
    where
    paths : Term × Term → Maybe (Term × Term)
    paths (lhs , rhs) =
      maybe
        (λ lhs′ → maybe (λ rhs′ → just (lhs′ , rhs′)) nothing (getPath rhs))
        nothing
        (getPath lhs)

  parseGoal : Term → TC (Term × Term)
  parseGoal goal = maybe returnTC fallback (getPaths goal)
    where
    -- Full normalisation unfolds `⟦_⟧₁` and loses the free structural path.
    -- Weak reduction is enough to expose simple goal aliases.
    fallback : TC (Term × Term)
    fallback = do
      goal′ ← reduce goal
      maybe returnTC
        (typeError
          ( strErr "Categories.Tactic.Monoidal: expected a goal of the form "
          ∷ strErr "⟦ f ⟧₁ ≈ ⟦ g ⟧₁ or ⟦ X ⟧₀ ≅ ⟦ Y ⟧₀; got "
          ∷ termErr goal ∷ []))
        (getPaths goal′)

  constructSoln : Term → Term → Term → Term → Term
  constructSoln M ⟦_⟧ₐ lhs rhs =
    quote Categories.Tactic.Monoidal.Coherence.coherence ⟨ def ⟩
      5 ⋯⟅∷⟆
      M ⟨∷⟩
      unknown ⟅∷⟆
      ⟦_⟧ₐ ⟨∷⟩
      unknown ⟅∷⟆
      unknown ⟅∷⟆
      lhs ⟨∷⟩
      rhs ⟨∷⟩
      (quote refl ⟨ con ⟩ []) ⟨∷⟩
      []

  constructObjectSoln : Term → Term → Term → Term → Term
  constructObjectSoln M ⟦_⟧ₐ lhs rhs =
    quote Categories.Tactic.Monoidal.Core.object-coherence ⟨ def ⟩
      5 ⋯⟅∷⟆
      M ⟨∷⟩
      unknown ⟅∷⟆
      ⟦_⟧ₐ ⟨∷⟩
      lhs ⟅∷⟆
      rhs ⟅∷⟆
      (quote refl ⟨ con ⟩ []) ⟨∷⟩
      []

  solve-macro : Term → Term → Term → TC _
  solve-macro M ⟦_⟧ₐ hole = do
    goal ← inferType hole
    (lhs , rhs) ← parseGoal goal
    unify hole (constructSoln M ⟦_⟧ₐ lhs rhs)

  solve₀-macro : Term → Term → Term → TC _
  solve₀-macro M ⟦_⟧ₐ hole = do
    goal ← inferType hole
    (lhs , rhs) ← parseGoal goal
    unify hole (constructObjectSoln M ⟦_⟧ₐ lhs rhs)

macro
  solve₀ : Term → Term → Term → TC _
  solve₀ = solve₀-macro

  solve : Term → Term → Term → TC _
  solve = solve-macro

  solveMonoidal : Term → Term → Term → TC _
  solveMonoidal = solve-macro
