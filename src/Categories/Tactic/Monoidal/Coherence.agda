{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Mac Lane coherence for the free structural syntax.
--
-- The proof strictifies through the free-monoid homomorphism of
-- `Core`.  Writing `κ⁻¹ X = strictify X .to : eval (nf X) ⇒ ⟦ X ⟧₀`:
--
--   * `μ-assoc` proves the associativity coherence of the homomorphism.
--   * `κ⁻¹-natural` — `κ⁻¹` is natural: `⟦ f ⟧₁ ∘ κ⁻¹ X ≈ κ⁻¹ Y ∘ substₑ (⇒⇒nf f)`
--     for every structural `f`. The associator case is exactly `μ-assoc`
--     and the right-unit case is `μ-unitʳ`.
--   * `coherence` — the reflection-facing theorem: if the normal-form
--     equality of the induced loop computes to `refl`, the loop is trivial.
--   * `WithUIP.loop-trivial-UIP` / `WithUIP.coherence-UIP` — the full theorem for
--     arbitrary structural paths when the caller wants to assume UIP for normal
--     forms explicitly.
--
-- The reflection macro uses `coherence`, so concrete goals do not need any UIP
-- or decidable equality argument.
--------------------------------------------------------------------------------

open import Level
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Tactic.Monoidal.Coherence
  {o ℓ e aℓ}
  {C : Category o ℓ e}
  (M : Monoidal C)
  {Atom : Set aℓ}
  (⟦_⟧ₐ : Atom → Category.Obj C)
  where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Categories.Tactic.Monoidal.Core M ⟦_⟧ₐ

open import Categories.Morphism C using (_≅_)
open import Categories.Category.Monoidal.Properties M
  using (assoc-shuffle; module Kelly's)
  renaming (unitorˡ-assoc-absorb to absorb-λ; unitorʳ-assoc-absorb to absorb-ρ)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
open import Categories.Morphism.Reasoning C using (module Cancellers; module Switch; pullˡ; pullʳ)
open Category C
open Monoidal M using (associator; unitorˡ; unitorʳ;
  unitorˡ-commute-from; unitorˡ-commute-to; unitorʳ-commute-from;
  assoc-commute-from; assoc-commute-to; _⊗₀_; _⊗₁_; unit; module ⊗)
open Shorthands using (α⇒; α⇐; λ⇒; λ⇐; ρ⇒; ρ⇐)
open Free Atom using (Ob; ‹_›; I; _⊗_; nf; ⇒⇒nf; invert; idₘ; module NormalForm)
  renaming
    ( _⇒_ to _⊸_ ; _∘_ to _⊚_ ; _⊗₁_ to _⊗ˢ_
    ; α⇒  to α⇒ᶠ ; α⇐  to α⇐ᶠ ;  λ⇒  to λ⇒ᶠ ; λ⇐ to λ⇐ᶠ ; ρ⇒ to ρ⇒ᶠ ; ρ⇐ to ρ⇐ᶠ
    )
open NormalForm using (assocₙ; assocₙ⁻¹; unitʳₙ; unitʳₙ⁻¹)
open Kelly's using (coherence₃)

private
  -- Merge two identity-on-the-left tensors.
  ⊗id-∘ : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C}
    → (id {A} ⊗₁ f) ∘ (id ⊗₁ g) ≈ id ⊗₁ (f ∘ g)
  ⊗id-∘ {f = f} {g} = begin
    (id ⊗₁ f) ∘ (id ⊗₁ g)  ≈˘⟨ ⊗-distrib-over-∘ ⟩
    (id ∘ id) ⊗₁ (f ∘ g)   ≈⟨ identity² ⟩⊗⟨ Equiv.refl ⟩
    id ⊗₁ (f ∘ g)          ∎

  ⊗idˡ-∘ : ∀ {A B C D E} {f : A ⇒ B} {g : D ⇒ E} {h : C ⇒ D}
    → (f ⊗₁ g) ∘ (id ⊗₁ h) ≈ f ⊗₁ (g ∘ h)
  ⊗idˡ-∘ {f = f} {g} {h} = begin
    (f ⊗₁ g) ∘ (id ⊗₁ h)  ≈˘⟨ ⊗-distrib-over-∘ ⟩
    (f ∘ id) ⊗₁ (g ∘ h)   ≈⟨ identityʳ ⟩⊗⟨ Equiv.refl ⟩
    f ⊗₁ (g ∘ h)          ∎

-- `μ⇒ x y` is the forward direction of the homomorphism's multiplicativity
-- witness: it merges two normalized products.
μ⇒ : (x y : List Atom) → eval (x ++ y) ⇒ (eval x ⊗₀ eval y)
μ⇒ x y = _≅_.from (eval-homo x y)

private
  μₙ : (A B : Ob) → eval (nf (A ⊗ B)) ⇒ (eval (nf A) ⊗₀ eval (nf B))
  μₙ A B = μ⇒ (nf A) (nf B)

-- Coercion of interpretations along an equality of words.
substₑ : {x y : List Atom} → x ≡ y → eval x ⇒ eval y
substₑ refl = id

private
  module EvalCoercion where
    assocₑ : (A B C : Ob) → eval (nf ((A ⊗ B) ⊗ C)) ⇒ eval (nf (A ⊗ (B ⊗ C)))
    assocₑ A B C = substₑ (assocₙ A B C)

    assocₑ⁻¹ : (A B C : Ob) → eval (nf (A ⊗ (B ⊗ C))) ⇒ eval (nf ((A ⊗ B) ⊗ C))
    assocₑ⁻¹ A B C = substₑ (assocₙ⁻¹ A B C)

    unitʳₑ : (A : Ob) → eval (nf (A ⊗ I)) ⇒ eval (nf A)
    unitʳₑ A = substₑ (unitʳₙ A)

    unitʳₑ⁻¹ : (A : Ob) → eval (nf A) ⇒ eval (nf (A ⊗ I))
    unitʳₑ⁻¹ A = substₑ (unitʳₙ⁻¹ A)

  open EvalCoercion

substₑ-cons : {b : Atom} {x y : List Atom} (p : x ≡ y)
  → substₑ (cong (b ∷_) p) ≈ id {⟦ b ⟧ₐ} ⊗₁ substₑ p
substₑ-cons refl = Equiv.sym ⊗.identity

-- Associativity coherence of the homomorphism.  This is the specialized
-- pentagon needed by strictifier naturality at the associator.
μ-assoc : (u v w : List Atom)
  → α⇒ ∘ (μ⇒ u v ⊗₁ id) ∘ μ⇒ (u ++ v) w
    ≈ (id ⊗₁ μ⇒ v w) ∘ μ⇒ u (v ++ w) ∘ substₑ (++-assoc u v w)
μ-assoc [] v w = begin
  α⇒ ∘ (λ⇐ ⊗₁ id) ∘ μ⇒ v w      ≈⟨ sym-assoc ⟩
  (α⇒ ∘ (λ⇐ ⊗₁ id)) ∘ μ⇒ v w    ≈⟨ absorb-λ ⟩∘⟨refl ⟩
  λ⇐ ∘ μ⇒ v w                    ≈⟨ unitorˡ-commute-to ⟩
  (id ⊗₁ μ⇒ v w) ∘ λ⇐            ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
  (id ⊗₁ μ⇒ v w) ∘ λ⇐ ∘ id       ∎

μ-assoc (b ∷ bs) v w = begin
    α⇒ ∘ (μ⇒ (b ∷ bs) v ⊗₁ id) ∘ μ⇒ (b ∷ (bs ++ v)) w
      ≈⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ⟩
    α⇒ ∘ ((α⇐ ⊗₁ id) ∘ ((id ⊗₁ μ⇒ bs v) ⊗₁ id)) ∘ (α⇐ ∘ (id ⊗₁ μ⇒ (bs ++ v) w))
      ≈⟨ refl⟩∘⟨ pullʳ (pullˡ (Equiv.sym assoc-commute-to)) ⟩
    α⇒ ∘ (α⇐ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (μ⇒ bs v ⊗₁ id))) ∘ (id ⊗₁ μ⇒ (bs ++ v) w)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    α⇒ ∘ (α⇐ ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ (μ⇒ bs v ⊗₁ id)) ∘ (id ⊗₁ μ⇒ (bs ++ v) w)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗id-∘ ⟩
    α⇒ ∘ (α⇐ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ ((μ⇒ bs v ⊗₁ id) ∘ μ⇒ (bs ++ v) w)))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    α⇒ ∘ ((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ ((μ⇒ bs v ⊗₁ id) ∘ μ⇒ (bs ++ v) w))
      ≈⟨ sym-assoc ⟩
    (α⇒ ∘ (α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ ((μ⇒ bs v ⊗₁ id) ∘ μ⇒ (bs ++ v) w))
      ≈⟨ assoc-shuffle ⟩∘⟨refl ⟩
    (α⇐ ∘ (id ⊗₁ α⇒)) ∘ (id ⊗₁ ((μ⇒ bs v ⊗₁ id) ∘ μ⇒ (bs ++ v) w))
      ≈⟨ assoc ⟩
    α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ ((μ⇒ bs v ⊗₁ id) ∘ μ⇒ (bs ++ v) w))
      ≈⟨ refl⟩∘⟨ ⊗id-∘ ⟩
    α⇐ ∘ (id ⊗₁ (α⇒ ∘ (μ⇒ bs v ⊗₁ id) ∘ μ⇒ (bs ++ v) w))
      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ μ-assoc bs v w ⟩
    α⇐ ∘ (id ⊗₁ ((id ⊗₁ μ⇒ v w) ∘ μ⇒ bs (v ++ w) ∘ substₑ p))
      ≈⟨ refl⟩∘⟨ Equiv.sym ⊗id-∘ ⟩
    α⇐ ∘ ((id ⊗₁ (id ⊗₁ μ⇒ v w)) ∘ (id ⊗₁ (μ⇒ bs (v ++ w) ∘ substₑ p)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Equiv.sym ⊗id-∘ ⟩
    α⇐ ∘ ((id ⊗₁ (id ⊗₁ μ⇒ v w)) ∘ ((id ⊗₁ μ⇒ bs (v ++ w)) ∘ (id ⊗₁ substₑ p)))
      ≈⟨ sym-assoc ⟩
    (α⇐ ∘ (id ⊗₁ (id ⊗₁ μ⇒ v w))) ∘ ((id ⊗₁ μ⇒ bs (v ++ w)) ∘ (id ⊗₁ substₑ p))
      ≈⟨ assoc-commute-to ⟩∘⟨refl ⟩
    (((id ⊗₁ id) ⊗₁ μ⇒ v w) ∘ α⇐) ∘ ((id ⊗₁ μ⇒ bs (v ++ w)) ∘ (id ⊗₁ substₑ p))
      ≈⟨ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩∘⟨refl ⟩
    ((id ⊗₁ μ⇒ v w) ∘ α⇐) ∘ ((id ⊗₁ μ⇒ bs (v ++ w)) ∘ (id ⊗₁ substₑ p))
      ≈⟨ assoc ⟩
    (id ⊗₁ μ⇒ v w) ∘ (α⇐ ∘ ((id ⊗₁ μ⇒ bs (v ++ w)) ∘ (id ⊗₁ substₑ p)))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    (id ⊗₁ μ⇒ v w) ∘ ((α⇐ ∘ (id ⊗₁ μ⇒ bs (v ++ w))) ∘ (id ⊗₁ substₑ p))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Equiv.sym (substₑ-cons p) ⟩
    (id ⊗₁ μ⇒ v w) ∘ μ⇒ (b ∷ bs) (v ++ w) ∘ substₑ p⁺
      ∎
  where
    p  = ++-assoc bs v w
    p⁺ = ++-assoc (b ∷ bs) v w

private
  μ-assocₙ : (A B C : Ob)
    → α⇒ ∘ (μₙ A B ⊗₁ id) ∘ μₙ (A ⊗ B) C
      ≈ (id ⊗₁ μₙ B C) ∘ μₙ A (B ⊗ C) ∘ assocₑ A B C
  μ-assocₙ A B C = μ-assoc (nf A) (nf B) (nf C)

-- The co-strictifier: eval (nf X) ⇒ ⟦ X ⟧₀ (the `.to` of `strictify`). Its tensor
-- case exposes `μ⇒`, so the associator coherence lands on `μ-assoc`.
κ⁻¹ : (X : Ob) → eval (nf X) ⇒ ⟦ X ⟧₀
κ⁻¹ X = _≅_.to (strictify X)

-- coercions compose
substₑ-∘ : {x y z : List Atom} (p : x ≡ y) (q : y ≡ z)
  → substₑ (Relation.Binary.PropositionalEquality.trans p q) ≈ substₑ q ∘ substₑ p
substₑ-∘ refl q = Equiv.sym identityʳ

-- naturality of `μ⇒` along coercions
μ-natural : {x x' y y' : List Atom} (p : x ≡ x') (q : y ≡ y')
  → (substₑ p ⊗₁ substₑ q) ∘ μ⇒ x y ≈ μ⇒ x' y' ∘ substₑ (cong₂ _++_ p q)
μ-natural {x = x} {y = y} refl refl = begin
  (id ⊗₁ id) ∘ μ⇒ x y  ≈⟨ ⊗.identity ⟩∘⟨refl ⟩
  id ∘ μ⇒ x y           ≈⟨ identityˡ ⟩
  μ⇒ x y                ≈˘⟨ identityʳ ⟩
  μ⇒ x y ∘ id           ∎

-- right-unit coherence of the homomorphism (the ρ analogue of `μ-assoc`)
μ-unitʳ : (x : List Atom)
  → ρ⇒ ∘ μ⇒ x [] ≈ substₑ (++-identityʳ x)
μ-unitʳ [] = begin
  ρ⇒ ∘ λ⇐  ≈˘⟨ coherence₃ ⟩∘⟨refl ⟩
  λ⇒ ∘ λ⇐  ≈⟨ unitorˡ.isoʳ ⟩
  id       ∎
μ-unitʳ (b ∷ bs) = begin
  ρ⇒ ∘ (α⇐ ∘ (id ⊗₁ μ⇒ bs []))
    ≈⟨ sym-assoc ⟩
  (ρ⇒ ∘ α⇐) ∘ (id ⊗₁ μ⇒ bs [])
    ≈⟨ absorb-ρ ⟩∘⟨refl ⟩
  (id ⊗₁ ρ⇒) ∘ (id ⊗₁ μ⇒ bs [])
    ≈˘⟨ ⊗-distrib-over-∘ ⟩
  (id ∘ id) ⊗₁ (ρ⇒ ∘ μ⇒ bs [])
    ≈⟨ identity² ⟩⊗⟨ μ-unitʳ bs ⟩
  id ⊗₁ substₑ p
    ≈˘⟨ substₑ-cons p ⟩
  substₑ p⁺
    ∎
  where
    p  = ++-identityʳ bs
    p⁺ = ++-identityʳ (b ∷ bs)

private
  μ-unitʳₙ : (A : Ob) → ρ⇒ ∘ μₙ A I ≈ unitʳₑ A
  μ-unitʳₙ A = μ-unitʳ (nf A)

private
  -- Naturality of the strictifier at the right unitor (forward direction).
  κ⁻¹-ρ⇒ : ∀ {X} → ρ⇒ ∘ κ⁻¹ (X ⊗ I) ≈ κ⁻¹ X ∘ unitʳₑ X
  κ⁻¹-ρ⇒ {X} = begin
    ρ⇒ ∘ ((κ⁻¹ X ⊗₁ id) ∘ μₙ X I)  ≈⟨ pullˡ unitorʳ-commute-from ⟩
    (κ⁻¹ X ∘ ρ⇒) ∘ μₙ X I          ≈⟨ assoc ⟩
    κ⁻¹ X ∘ (ρ⇒ ∘ μₙ X I)          ≈⟨ refl⟩∘⟨ μ-unitʳₙ X ⟩
    κ⁻¹ X ∘ unitʳₑ X               ∎

  -- Naturality of the strictifier at the associator (forward direction); this is
  -- where `μ-assoc` discharges the work.
  κ⁻¹-α⇒ : ∀ {A B C}
    → α⇒ ∘ κ⁻¹ ((A ⊗ B) ⊗ C) ≈ κ⁻¹ (A ⊗ (B ⊗ C)) ∘ assocₑ A B C
  κ⁻¹-α⇒ {A} {B} {C} = begin
    α⇒ ∘ ((((κ⁻¹ A ⊗₁ κ⁻¹ B) ∘ μₙ A B) ⊗₁ κ⁻¹ C) ∘ μₙ (A ⊗ B) C)
      ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
    α⇒ ∘ (((κ⁻¹ A ⊗₁ κ⁻¹ B) ⊗₁ κ⁻¹ C) ∘ (μₙ A B ⊗₁ id)) ∘ μₙ (A ⊗ B) C
      ≈⟨ refl⟩∘⟨ assoc ⟩
    α⇒ ∘ ((κ⁻¹ A ⊗₁ κ⁻¹ B) ⊗₁ κ⁻¹ C) ∘ ((μₙ A B ⊗₁ id) ∘ μₙ (A ⊗ B) C)
      ≈⟨ sym-assoc ⟩
    (α⇒ ∘ ((κ⁻¹ A ⊗₁ κ⁻¹ B) ⊗₁ κ⁻¹ C)) ∘ ((μₙ A B ⊗₁ id) ∘ μₙ (A ⊗ B) C)
      ≈⟨ assoc-commute-from ⟩∘⟨refl ⟩
    ((κ⁻¹ A ⊗₁ (κ⁻¹ B ⊗₁ κ⁻¹ C)) ∘ α⇒) ∘ ((μₙ A B ⊗₁ id) ∘ μₙ (A ⊗ B) C)
      ≈⟨ assoc ⟩
    (κ⁻¹ A ⊗₁ (κ⁻¹ B ⊗₁ κ⁻¹ C)) ∘ (α⇒ ∘ ((μₙ A B ⊗₁ id) ∘ μₙ (A ⊗ B) C))
      ≈⟨ refl⟩∘⟨ μ-assocₙ A B C ⟩
    (κ⁻¹ A ⊗₁ (κ⁻¹ B ⊗₁ κ⁻¹ C)) ∘ ((id ⊗₁ μₙ B C) ∘ μₙ A (B ⊗ C) ∘ assocₑ A B C)
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    (κ⁻¹ A ⊗₁ (κ⁻¹ B ⊗₁ κ⁻¹ C)) ∘ ((id ⊗₁ μₙ B C) ∘ μₙ A (B ⊗ C)) ∘ assocₑ A B C
      ≈⟨ sym-assoc ⟩
    ((κ⁻¹ A ⊗₁ (κ⁻¹ B ⊗₁ κ⁻¹ C)) ∘ ((id ⊗₁ μₙ B C) ∘ μₙ A (B ⊗ C))) ∘ assocₑ A B C
      ≈⟨ sym-assoc ⟩∘⟨refl ⟩
    (((κ⁻¹ A ⊗₁ (κ⁻¹ B ⊗₁ κ⁻¹ C)) ∘ (id ⊗₁ μₙ B C)) ∘ μₙ A (B ⊗ C)) ∘ assocₑ A B C
      ≈⟨ ⊗idˡ-∘ ⟩∘⟨refl ⟩∘⟨refl ⟩
    ((κ⁻¹ A ⊗₁ ((κ⁻¹ B ⊗₁ κ⁻¹ C) ∘ μₙ B C)) ∘ μₙ A (B ⊗ C)) ∘ assocₑ A B C
      ∎

-- `substₑ p` is an isomorphism with inverse `substₑ (sym p)`.
substₑ-isoˡ : {x y : List Atom} (p : x ≡ y) → substₑ (sym p) ∘ substₑ p ≈ id
substₑ-isoˡ refl = identity²

substₑ-isoʳ : {x y : List Atom} (p : x ≡ y) → substₑ p ∘ substₑ (sym p) ≈ id
substₑ-isoʳ refl = identity²

private
  assocₑ-isoʳ : (A B C : Ob) → assocₑ A B C ∘ assocₑ⁻¹ A B C ≈ id
  assocₑ-isoʳ A B C = substₑ-isoʳ (assocₙ A B C)

  unitʳₑ-isoʳ : (A : Ob) → unitʳₑ A ∘ unitʳₑ⁻¹ A ≈ id
  unitʳₑ-isoʳ A = substₑ-isoʳ (unitʳₙ A)

-- The strictifier is natural: interpreting a structural morphism and then
-- co-strictifying equals co-strictifying and then coercing along the (equal)
-- object normal forms.
κ⁻¹-natural : ∀ {X Y} (f : X ⊸ Y) → ⟦ f ⟧₁ ∘ κ⁻¹ X ≈ κ⁻¹ Y ∘ substₑ (⇒⇒nf f)
κ⁻¹-natural {X} idₘ = begin
  id ∘ κ⁻¹ X  ≈⟨ identityˡ ⟩
  κ⁻¹ X       ≈˘⟨ identityʳ ⟩
  κ⁻¹ X ∘ id  ∎
κ⁻¹-natural (_⊚_ {X} {Y} {Z} g f) = begin
  (⟦ g ⟧₁ ∘ ⟦ f ⟧₁) ∘ κ⁻¹ X              ≈⟨ assoc ⟩
  ⟦ g ⟧₁ ∘ (⟦ f ⟧₁ ∘ κ⁻¹ X)              ≈⟨ refl⟩∘⟨ κ⁻¹-natural f ⟩
  ⟦ g ⟧₁ ∘ (κ⁻¹ Y ∘ substₑ p)             ≈⟨ sym-assoc ⟩
  (⟦ g ⟧₁ ∘ κ⁻¹ Y) ∘ substₑ p             ≈⟨ κ⁻¹-natural g ⟩∘⟨refl ⟩
  (κ⁻¹ Z ∘ substₑ q) ∘ substₑ p           ≈⟨ assoc ⟩
  κ⁻¹ Z ∘ (substₑ q ∘ substₑ p)           ≈˘⟨ refl⟩∘⟨ substₑ-∘ p q ⟩
  κ⁻¹ Z ∘ substₑ (trans p q)              ∎
  where
    p = ⇒⇒nf f
    q = ⇒⇒nf g
κ⁻¹-natural (_⊗ˢ_ {X} {Y} {Z} {W} f g) = begin
  (⟦ f ⟧₁ ⊗₁ ⟦ g ⟧₁) ∘ ((κ⁻¹ X ⊗₁ κ⁻¹ Z) ∘ μₙ X Z)          ≈⟨ sym-assoc ⟩
  ((⟦ f ⟧₁ ⊗₁ ⟦ g ⟧₁) ∘ (κ⁻¹ X ⊗₁ κ⁻¹ Z)) ∘ μₙ X Z          ≈˘⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
  ((⟦ f ⟧₁ ∘ κ⁻¹ X) ⊗₁ (⟦ g ⟧₁ ∘ κ⁻¹ Z)) ∘ μₙ X Z           ≈⟨ (κ⁻¹-natural f ⟩⊗⟨ κ⁻¹-natural g) ⟩∘⟨refl ⟩
  ((κ⁻¹ Y ∘ substₑ p) ⊗₁ (κ⁻¹ W ∘ substₑ q)) ∘ μₙ X Z ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
  ((κ⁻¹ Y ⊗₁ κ⁻¹ W) ∘ (substₑ p ⊗₁ substₑ q)) ∘ μₙ X Z ≈⟨ assoc ⟩
  (κ⁻¹ Y ⊗₁ κ⁻¹ W) ∘ ((substₑ p ⊗₁ substₑ q) ∘ μₙ X Z) ≈⟨ refl⟩∘⟨ μ-natural p q ⟩
  (κ⁻¹ Y ⊗₁ κ⁻¹ W) ∘ (μₙ Y W ∘ substₑ (cong₂ _++_ p q)) ≈⟨ sym-assoc ⟩
  ((κ⁻¹ Y ⊗₁ κ⁻¹ W) ∘ μₙ Y W) ∘ substₑ (cong₂ _++_ p q) ∎
  where
    p = ⇒⇒nf f
    q = ⇒⇒nf g
κ⁻¹-natural (λ⇒ᶠ {X}) = begin
  λ⇒ ∘ ((id ⊗₁ κ⁻¹ X) ∘ λ⇐)   ≈⟨ pullˡ unitorˡ-commute-from ⟩
  (κ⁻¹ X ∘ λ⇒) ∘ λ⇐           ≈⟨ assoc ⟩
  κ⁻¹ X ∘ (λ⇒ ∘ λ⇐)           ≈⟨ refl⟩∘⟨ unitorˡ.isoʳ ⟩
  κ⁻¹ X ∘ id                  ∎
κ⁻¹-natural (λ⇐ᶠ {X}) = begin
  λ⇐ ∘ κ⁻¹ X                  ≈⟨ unitorˡ-commute-to ⟩
  (id ⊗₁ κ⁻¹ X) ∘ λ⇐          ≈˘⟨ identityʳ ⟩
  ((id ⊗₁ κ⁻¹ X) ∘ λ⇐) ∘ id   ∎
κ⁻¹-natural (ρ⇒ᶠ {X})         = κ⁻¹-ρ⇒ {X}
κ⁻¹-natural (α⇒ᶠ {A} {B} {C}) = κ⁻¹-α⇒ {A} {B} {C}
κ⁻¹-natural (α⇐ᶠ {A} {B} {C}) = Equiv.sym (begin
  κ⁻¹ ((A ⊗ B) ⊗ C) ∘ assocₑ⁻¹ A B C
    ≈⟨ Switch.switch-fromtoˡ associator (κ⁻¹-α⇒ {A} {B} {C}) ⟩∘⟨refl ⟩
  (α⇐ ∘ (κ⁻¹ (A ⊗ (B ⊗ C)) ∘ assocₑ A B C)) ∘ assocₑ⁻¹ A B C
    ≈⟨ assoc ⟩
  α⇐ ∘ ((κ⁻¹ (A ⊗ (B ⊗ C)) ∘ assocₑ A B C) ∘ assocₑ⁻¹ A B C)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (κ⁻¹ (A ⊗ (B ⊗ C)) ∘ (assocₑ A B C ∘ assocₑ⁻¹ A B C))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assocₑ-isoʳ A B C ⟩
  α⇐ ∘ (κ⁻¹ (A ⊗ (B ⊗ C)) ∘ id)
    ≈⟨ refl⟩∘⟨ identityʳ ⟩
  α⇐ ∘ κ⁻¹ (A ⊗ (B ⊗ C))
    ∎)
κ⁻¹-natural (ρ⇐ᶠ {X}) = Equiv.sym (begin
  κ⁻¹ (X ⊗ I) ∘ unitʳₑ⁻¹ X
    ≈⟨ Switch.switch-fromtoˡ unitorʳ (κ⁻¹-ρ⇒ {X}) ⟩∘⟨refl ⟩
  (ρ⇐ ∘ (κ⁻¹ X ∘ unitʳₑ X)) ∘ unitʳₑ⁻¹ X
    ≈⟨ assoc ⟩
  ρ⇐ ∘ ((κ⁻¹ X ∘ unitʳₑ X) ∘ unitʳₑ⁻¹ X)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇐ ∘ (κ⁻¹ X ∘ (unitʳₑ X ∘ unitʳₑ⁻¹ X))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitʳₑ-isoʳ X ⟩
  ρ⇐ ∘ (κ⁻¹ X ∘ id)
    ≈⟨ refl⟩∘⟨ identityʳ ⟩
  ρ⇐ ∘ κ⁻¹ X
    ∎)

substₑ-loop-refl : {w : List Atom} {p : w ≡ w} → p ≡ refl → substₑ p ≈ id
substₑ-loop-refl p≡refl = Equiv.reflexive (cong substₑ p≡refl)

loop-trivial-from : ∀ {X} (h : X ⊸ X) → substₑ (⇒⇒nf h) ≈ id → ⟦ h ⟧₁ ≈ id
loop-trivial-from {X} h loop = begin
  ⟦ h ⟧₁                          ≈˘⟨ identityʳ ⟩
  ⟦ h ⟧₁ ∘ id                     ≈˘⟨ refl⟩∘⟨ _≅_.isoˡ (strictify X) ⟩
  ⟦ h ⟧₁ ∘ (κ⁻¹ X ∘ _≅_.from (strictify X))  ≈⟨ sym-assoc ⟩
  (⟦ h ⟧₁ ∘ κ⁻¹ X) ∘ _≅_.from (strictify X)
    ≈⟨ κ⁻¹-natural h ⟩∘⟨refl ⟩
  (κ⁻¹ X ∘ substₑ (⇒⇒nf h)) ∘ _≅_.from (strictify X)
    ≈⟨ (refl⟩∘⟨ loop) ⟩∘⟨refl ⟩
  (κ⁻¹ X ∘ id) ∘ _≅_.from (strictify X)
    ≈⟨ identityʳ ⟩∘⟨refl ⟩
  κ⁻¹ X ∘ _≅_.from (strictify X)      ≈⟨ _≅_.isoˡ (strictify X) ⟩
  id                              ∎

-- Coherence for loops whose induced normal-form equality computes to `refl`.
-- This is the entry point used by the reflection macro.
loop-trivial : ∀ {X} (h : X ⊸ X) → ⇒⇒nf h ≡ refl → ⟦ h ⟧₁ ≈ id
loop-trivial h h-refl = loop-trivial-from h (substₑ-loop-refl h-refl)

coherence : ∀ {X Y} (f g : X ⊸ Y) → ⇒⇒nf (invert g ⊚ f) ≡ refl → ⟦ f ⟧₁ ≈ ⟦ g ⟧₁
coherence f g loop-refl =
  coherence-from-loop {f = f} {g = g} (loop-trivial (invert g ⊚ f) loop-refl)

open import Axiom.UniquenessOfIdentityProofs using (UIP)

-- With UIP on normal forms, every loop-shaped coercion is the identity, and
-- full Mac Lane coherence follows.
module WithUIP (≡-irrelevant : UIP (List Atom)) where

  private
    substₑ-loop : {w : List Atom} (p : w ≡ w) → substₑ p ≈ id
    substₑ-loop p = Equiv.reflexive (cong substₑ (≡-irrelevant p refl))

  -- loop-triviality: a structural endomorphism interprets as the identity.
  loop-trivial-UIP : ∀ {X} (h : X ⊸ X) → ⟦ h ⟧₁ ≈ id
  loop-trivial-UIP h = loop-trivial-from h (substₑ-loop (⇒⇒nf h))

  -- Mac Lane coherence: any two parallel structural morphisms agree.
  coherence-UIP : ∀ {X Y} (f g : X ⊸ Y) → ⟦ f ⟧₁ ≈ ⟦ g ⟧₁
  coherence-UIP f g = coherence-from-loops loop-trivial-UIP {f} {g}
