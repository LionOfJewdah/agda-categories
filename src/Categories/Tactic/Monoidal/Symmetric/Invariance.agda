{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Tactic.Monoidal.Symmetric.Invariance
  {o ℓ e a : Level}
  {𝒞 : Category o ℓ e}
  {V : Monoidal 𝒞}
  (S : Symmetric V)
  {Atom : Set a}
  (⟦_⟧ₐ : Atom → Category.Obj 𝒞)
  (uipₐ : UIP Atom)
  where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ; ≡-dec)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
  renaming (_≟_ to _≟ℕ_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong) renaming (refl to ≡refl; sym to ≡sym)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-reflexive; ↭-sym; refl; prep; swap; trans)

open Symmetric S using (braided; commutative)

open import Categories.Tactic.Monoidal.Core V ⟦_⟧ₐ
  using () renaming (eval to ⟦_⟧ᴹ)
open import Categories.Tactic.Monoidal.Coherence V ⟦_⟧ₐ
  using (substₑ)
open import Categories.Tactic.Monoidal.Braided
  using (module Evaluation)
open Evaluation braided ⟦_⟧ₐ
  using (σ⇒)
open import Categories.Tactic.Monoidal.Braided.AdjacentSwaps braided ⟦_⟧ₐ
  using (swap₁; swap₁-naturalʳ; swap₁-yang-baxter)
open import Categories.Tactic.Monoidal.Braided.Soundness braided ⟦_⟧ₐ
  using (realize↭)

open Category 𝒞
open Monoidal V using (_⊗₀_; _⊗₁_; associator; module ⊗)
open import Categories.Category.Monoidal.Reasoning V
open import Categories.Category.Monoidal.Utilities V using (module Shorthands)
open Shorthands
open import Categories.Morphism.Reasoning 𝒞
  using (assoc²βε; pullˡ; pullʳ; elimˡ; elimʳ; module Cancellers)

private
  variable
    x y z : Atom
    xs ys zs : List Atom

  -- A fully whiskered identity collapses.
  id₃ : ∀ {P Q R} → (id {P} ⊗₁ (id {Q} ⊗₁ id {R})) ≈ id
  id₃ {P} {Q} {R} = begin
    id {P} ⊗₁ (id {Q} ⊗₁ id {R})
      ≈⟨ refl⟩⊗⟨ ⊗.identity ⟩
    id {P} ⊗₁ id {Q ⊗₀ R}
      ≈⟨ ⊗.identity ⟩
    id {P ⊗₀ (Q ⊗₀ R)}
      ∎

pos : x ∈ xs → ℕ
pos (here _)  = zero
pos (there i) = suc (pos i)

-- Memberships are determined by positions under UIP.
∈-pos-injective : {x : Atom} {xs : List Atom}
  → (i j : x ∈ xs) → pos i ≡ pos j → i ≡ j
∈-pos-injective (here px)  (here py)  _  = cong here (uipₐ px py)
∈-pos-injective (there i)  (there j)  pe =
  cong there (∈-pos-injective i j (suc-injective pe))

infixl 6 _─_

-- Delete the element at a membership.
_─_ : (xs : List Atom) → x ∈ xs → List Atom
(_ ∷ xs) ─ here _  = xs
(y ∷ xs) ─ there i = y ∷ (xs ─ i)

-- Transport membership along a permutation witness.
transport∈ : xs ↭ ys → x ∈ xs → x ∈ ys
transport∈ refl         i                    = i
transport∈ (prep y p)   (here px)            = here px
transport∈ (prep y p)   (there i)            = there (transport∈ p i)
transport∈ (swap y z p) (here px)            = there (here px)
transport∈ (swap y z p) (there (here px))    = here px
transport∈ (swap y z p) (there (there i))    = there (there (transport∈ p i))
transport∈ (trans p q)  i                    = transport∈ q (transport∈ p i)

-- Extract a member to the front.
shift-in : (i : x ∈ xs) → xs ↭ (x ∷ (xs ─ i))
shift-in         (here {_} {t} px) = ↭-reflexive (cong (_∷ t) (≡sym px))
shift-in {x = x} (there {y}    i)  = trans (prep y (shift-in i)) (swap y x refl)

-- Residual witness after extraction.
extract : (p : xs ↭ ys) (i : x ∈ xs) → (xs ─ i) ↭ (ys ─ transport∈ p i)
extract refl         i                 = refl
extract (prep y p)   (here px)         = p
extract (prep y p)   (there i)         = prep y (extract p i)
extract (swap y z p) (here px)         = prep z p
extract (swap y z p) (there (here px)) = prep y p
extract (swap y z p) (there (there i)) = swap y z (extract p i)
extract (trans p q)  i                 = trans (extract p i) (extract q (transport∈ p i))

-- Positions visited by a permutation witness.
positions-from : (xs : List Atom) → xs ↭ ys → List ℕ
positions-from []       p = []
positions-from (x ∷ xs) p =
  pos (transport∈ p (here ≡refl)) ∷ positions-from xs (extract p (here ≡refl))

positions : xs ↭ ys → List ℕ
positions {xs = xs} = positions-from xs

_≟positions_ : DecidableEquality (List ℕ)
_≟positions_ = ≡-dec _≟ℕ_

-- A witness out of the empty list forces the target empty.
nil-eq   : ([] {A = Atom}) ↭ ys → ([] {A = Atom}) ≡ ys
nil-eq-∘ : ([] {A = Atom}) ≡ zs → zs ↭ ys → ([] {A = Atom}) ≡ ys

nil-eq refl        = ≡refl
nil-eq (trans p q) = nil-eq-∘ (nil-eq p) q

nil-eq-∘ ≡refl q = nil-eq q

-- Adjacent swaps are involutive in a symmetric monoidal category.
swap₁-inv : ∀ {P Q R} → swap₁ Q P R ∘ swap₁ P Q R ≈ id
swap₁-inv {P} {Q} {R} = begin
  (α⇒ ∘ (σ⇒ {Q} {P} ⊗₁ id) ∘ α⇐)
    ∘ (α⇒ ∘ (σ⇒ {P} {Q} ⊗₁ id) ∘ α⇐)
    ≈⟨ assoc²βε ⟩
  α⇒ ∘ (σ⇒ {Q} {P} ⊗₁ id)
    ∘ (α⇐ ∘ (α⇒ ∘ (σ⇒ {P} {Q} ⊗₁ id) ∘ α⇐))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Cancellers.cancelˡ associator.isoˡ ⟩
  α⇒ ∘ (σ⇒ {Q} {P} ⊗₁ id) ∘ ((σ⇒ {P} {Q} ⊗₁ id) ∘ α⇐)
    ≈⟨ refl⟩∘⟨ Cancellers.cancelˡ (⊗-cancel commutative identity²) ⟩
  α⇒ ∘ α⇐
    ≈⟨ associator.isoʳ ⟩
  id ∎

-- Realizations are invertible along `↭-sym` (needs σ² at the swaps).
realize-sym-cancelˡ : {xs ys : List Atom} (p : xs ↭ ys)
  → realize↭ (↭-sym p) ∘ realize↭ p ≈ id
realize-sym-cancelˡ refl       = identity²
realize-sym-cancelˡ (prep x p) = ⊗-cancel identity² (realize-sym-cancelˡ p)
realize-sym-cancelˡ (swap {xs = xs₀} {ys = ys₀} x y p) = begin
  ((id ⊗₁ (id ⊗₁ realize↭ (↭-sym p))) ∘ swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ⟧ᴹ)
    ∘ ((id ⊗₁ (id ⊗₁ realize↭ p)) ∘ swap₁ ⟦ x ⟧ₐ ⟦ y ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ assoc ⟩
  (id ⊗₁ (id ⊗₁ realize↭ (↭-sym p)))
    ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ⟧ᴹ ∘ ((id ⊗₁ (id ⊗₁ realize↭ p)) ∘ swap₁ ⟦ x ⟧ₐ ⟦ y ⟧ₐ ⟦ xs₀ ⟧ᴹ))
    ≈⟨ refl⟩∘⟨ pullˡ (swap₁-naturalʳ (realize↭ p)) ⟩
  (id ⊗₁ (id ⊗₁ realize↭ (↭-sym p)))
    ∘ (((id ⊗₁ (id ⊗₁ realize↭ p)) ∘ swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ⟧ᴹ) ∘ swap₁ ⟦ x ⟧ₐ ⟦ y ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  (id ⊗₁ (id ⊗₁ realize↭ (↭-sym p)))
    ∘ ((id ⊗₁ (id ⊗₁ realize↭ p)) ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ⟧ᴹ ∘ swap₁ ⟦ x ⟧ₐ ⟦ y ⟧ₐ ⟦ xs₀ ⟧ᴹ))
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ swap₁-inv) ⟩
  (id ⊗₁ (id ⊗₁ realize↭ (↭-sym p))) ∘ ((id ⊗₁ (id ⊗₁ realize↭ p)) ∘ id)
    ≈⟨ refl⟩∘⟨ identityʳ ⟩
  (id ⊗₁ (id ⊗₁ realize↭ (↭-sym p))) ∘ (id ⊗₁ (id ⊗₁ realize↭ p))
    ≈⟨ ⊗-cancel identity² (⊗-cancel identity² (realize-sym-cancelˡ p)) ⟩
  id ∎
realize-sym-cancelˡ (trans p q) = begin
  (realize↭ (↭-sym p) ∘ realize↭ (↭-sym q)) ∘ (realize↭ q ∘ realize↭ p)
    ≈⟨ assoc ⟩
  realize↭ (↭-sym p) ∘ (realize↭ (↭-sym q) ∘ (realize↭ q ∘ realize↭ p))
    ≈⟨ refl⟩∘⟨ Cancellers.cancelˡ (realize-sym-cancelˡ q) ⟩
  realize↭ (↭-sym p) ∘ realize↭ p
    ≈⟨ realize-sym-cancelˡ p ⟩
  id ∎

realize-nil-eq   : ∀ {ys} (p : ([] {A = Atom}) ↭ ys) → realize↭ p ≈ substₑ (nil-eq p)
realize-nil-eq-∘ : ∀ {zs ys} (e : ([] {A = Atom}) ≡ zs) (q : zs ↭ ys)
  → realize↭ q ∘ substₑ e ≈ substₑ (nil-eq-∘ e q)

realize-nil-eq refl        = Equiv.refl
realize-nil-eq (trans p q) = begin
  realize↭ q ∘ realize↭ p             ≈⟨ refl⟩∘⟨ realize-nil-eq p ⟩
  realize↭ q ∘ substₑ (nil-eq p)      ≈⟨ realize-nil-eq-∘ (nil-eq p) q ⟩
  substₑ (nil-eq-∘ (nil-eq p) q)      ∎

realize-nil-eq-∘ ≡refl q = begin
  realize↭ q ∘ id       ≈⟨ identityʳ ⟩
  realize↭ q            ≈⟨ realize-nil-eq q ⟩
  substₑ (nil-eq q)     ∎

-- Coercions out of the empty list are unique. (`[] ≡ []` is contractible by
-- constructor injectivity; no axiom K is involved.)
substₑ-nil-irrelevant : ∀ {ys : List Atom} (e₁ e₂ : ([] {A = Atom}) ≡ ys) → substₑ e₁ ≈ substₑ e₂
substₑ-nil-irrelevant ≡refl ≡refl = Equiv.refl

-- Bubble one leading element past the extracted element.
bubble-strip : {x u : Atom} {ls : List Atom} (k : x ∈ ls)
  → realize↭ (shift-in (there {x = u} k))
    ≈ swap₁ ⟦ u ⟧ₐ ⟦ x ⟧ₐ ⟦ ls ─ k ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in k))
bubble-strip k = elimˡ id₃ ⟩∘⟨refl

-- Extracting an element commutes with realization.
extract-sound : {xs ys : List Atom} {x : Atom} (p : xs ↭ ys) (i : x ∈ xs)
  → realize↭ (shift-in (transport∈ p i)) ∘ realize↭ p
    ≈ (id ⊗₁ realize↭ (extract p i)) ∘ realize↭ (shift-in i)
extract-sound refl i = begin
  realize↭ (shift-in i) ∘ id
    ≈⟨ identityʳ ⟩
  realize↭ (shift-in i)
    ≈˘⟨ identityˡ ⟩
  id ∘ realize↭ (shift-in i)
    ≈˘⟨ ⊗.identity ⟩∘⟨refl ⟩
  (id ⊗₁ id) ∘ realize↭ (shift-in i) ∎
extract-sound (prep y p₀) (here ≡refl) = begin
  id ∘ (id ⊗₁ realize↭ p₀)
    ≈⟨ identityˡ ⟩
  id ⊗₁ realize↭ p₀
    ≈˘⟨ identityʳ ⟩
  (id ⊗₁ realize↭ p₀) ∘ id ∎
extract-sound {x = x} (prep {xs = xs₀} {ys = ys₀} y p₀) (there i₀) = begin
  realize↭ (shift-in (there {x = y} (transport∈ p₀ i₀))) ∘ (id ⊗₁ realize↭ p₀)
    ≈⟨ bubble-strip (transport∈ p₀ i₀) ⟩∘⟨refl ⟩
  (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
    ∘ (id ⊗₁ realize↭ (shift-in (transport∈ p₀ i₀)))) ∘ (id ⊗₁ realize↭ p₀)
    ≈⟨ assoc ⟩
  swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
    ∘ ((id ⊗₁ realize↭ (shift-in (transport∈ p₀ i₀))) ∘ (id ⊗₁ realize↭ p₀))
    ≈˘⟨ refl⟩∘⟨ split₂ˡ ⟩
  swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
    ∘ (id ⊗₁ (realize↭ (shift-in (transport∈ p₀ i₀)) ∘ realize↭ p₀))
    ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ extract-sound p₀ i₀) ⟩
  swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
    ∘ (id ⊗₁ ((id ⊗₁ realize↭ (extract p₀ i₀)) ∘ realize↭ (shift-in i₀)))
    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
  swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
    ∘ ((id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))) ∘ (id ⊗₁ realize↭ (shift-in i₀)))
    ≈⟨ pullˡ (swap₁-naturalʳ (realize↭ (extract p₀ i₀))) ⟩
  ((id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))) ∘ swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)
    ∘ (id ⊗₁ realize↭ (shift-in i₀))
    ≈⟨ assoc ⟩
  (id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀)))
    ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀)))
    ≈˘⟨ refl⟩∘⟨ bubble-strip i₀ ⟩
  (id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))) ∘ realize↭ (shift-in (there {x = y} i₀)) ∎
extract-sound (swap {xs = xs₀} {ys = ys₀} y z p₀) (here ≡refl) = begin
  realize↭ (shift-in (there {x = z} (here {xs = ys₀} ≡refl))) ∘ ((id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ bubble-strip (here {xs = ys₀} ≡refl) ⟩∘⟨refl ⟩
  (swap₁ ⟦ z ⟧ₐ ⟦ y ⟧ₐ ⟦ ys₀ ⟧ᴹ ∘ (id ⊗₁ id))
    ∘ ((id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ elimʳ ⊗.identity ⟩∘⟨refl ⟩
  swap₁ ⟦ z ⟧ₐ ⟦ y ⟧ₐ ⟦ ys₀ ⟧ᴹ ∘ ((id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ pullˡ (swap₁-naturalʳ (realize↭ p₀)) ⟩
  ((id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ swap₁ ⟦ z ⟧ₐ ⟦ y ⟧ₐ ⟦ xs₀ ⟧ᴹ) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ
    ≈⟨ assoc ⟩
  (id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ (swap₁ ⟦ z ⟧ₐ ⟦ y ⟧ₐ ⟦ xs₀ ⟧ᴹ ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ refl⟩∘⟨ swap₁-inv ⟩
  (id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ id ∎
extract-sound (swap {xs = xs₀} {ys = ys₀} y z p₀) (there (here ≡refl)) = begin
  id ∘ ((id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ identityˡ ⟩
  (id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ
    ≈˘⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
  (id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ (swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ ∘ (id ⊗₁ id))
    ≈˘⟨ refl⟩∘⟨ bubble-strip (here {xs = xs₀} ≡refl) ⟩
  (id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ realize↭ (shift-in (there {x = y} (here {xs = xs₀} ≡refl))) ∎
extract-sound {x = x} (swap {xs = xs₀} {ys = ys₀} y z p₀) (there (there i₀)) = begin
  realize↭ (shift-in (there {x = z} (there {x = y} (transport∈ p₀ i₀))))
    ∘ ((id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ bubble-strip (there {x = y} (transport∈ p₀ i₀)) ⟩∘⟨refl ⟩
  (swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ y ∷ (ys₀ ─ transport∈ p₀ i₀) ⟧ᴹ
    ∘ (id ⊗₁ realize↭ (shift-in (there {x = y} (transport∈ p₀ i₀)))))
    ∘ ((id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ (refl⟩∘⟨ (refl⟩⊗⟨ bubble-strip (transport∈ p₀ i₀))) ⟩∘⟨refl ⟩
  (swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ y ∷ (ys₀ ─ transport∈ p₀ i₀) ⟧ᴹ
    ∘ (id ⊗₁ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
        ∘ (id ⊗₁ realize↭ (shift-in (transport∈ p₀ i₀))))))
    ∘ ((id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ assoc ⟩
  swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ y ∷ (ys₀ ─ transport∈ p₀ i₀) ⟧ᴹ
    ∘ ((id ⊗₁ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
        ∘ (id ⊗₁ realize↭ (shift-in (transport∈ p₀ i₀)))))
      ∘ ((id ⊗₁ (id ⊗₁ realize↭ p₀)) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ))
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ split₂ˡ) ⟩
  swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ y ∷ (ys₀ ─ transport∈ p₀ i₀) ⟧ᴹ
    ∘ ((id ⊗₁ ((swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
        ∘ (id ⊗₁ realize↭ (shift-in (transport∈ p₀ i₀)))) ∘ (id ⊗₁ realize↭ p₀)))
      ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ refl⟩∘⟨ ((refl⟩⊗⟨ inner) ⟩∘⟨refl) ⟩
  swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ y ∷ (ys₀ ─ transport∈ p₀ i₀) ⟧ᴹ
    ∘ ((id ⊗₁ ((id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀)))
        ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀)))))
      ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ refl⟩∘⟨ (split₂ˡ ⟩∘⟨refl) ⟩
  swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ y ∷ (ys₀ ─ transport∈ p₀ i₀) ⟧ᴹ
    ∘ (((id ⊗₁ (id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))))
        ∘ (id ⊗₁ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀)))))
      ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ y ∷ (ys₀ ─ transport∈ p₀ i₀) ⟧ᴹ
    ∘ ((id ⊗₁ (id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))))
      ∘ ((id ⊗₁ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀))))
        ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ))
    ≈⟨ pullˡ (swap₁-naturalʳ (id ⊗₁ realize↭ (extract p₀ i₀))) ⟩
  ((id ⊗₁ (id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))))
    ∘ swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ (⟦ y ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ))
    ∘ ((id ⊗₁ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀))))
      ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
    ≈⟨ assoc ⟩
  (id ⊗₁ (id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))))
    ∘ (swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ (⟦ y ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
      ∘ ((id ⊗₁ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀))))
        ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ))
    ≈⟨ refl⟩∘⟨ core ⟩
  (id ⊗₁ (id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))))
    ∘ ((id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)
      ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ (⟦ z ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ (id ⊗₁ (swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀))))))
    ≈⟨ pullˡ (⟺ split₂ˡ) ⟩
  (id ⊗₁ ((id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ))
    ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ (⟦ z ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
      ∘ (id ⊗₁ (swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀)))))
    ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ (refl⟩⊗⟨ bubble-strip i₀)) ⟩
  (id ⊗₁ ((id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ))
    ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ (⟦ z ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
      ∘ (id ⊗₁ realize↭ (shift-in (there {x = z} i₀))))
    ≈˘⟨ refl⟩∘⟨ bubble-strip (there {x = z} i₀) ⟩
  (id ⊗₁ ((id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ))
    ∘ realize↭ (shift-in (there {x = y} (there {x = z} i₀))) ∎
  where
    -- Slide the residual action of `p₀` through the inner bubble, then apply the
    -- induction hypothesis and re-slide the residual.
    inner : (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
              ∘ (id ⊗₁ realize↭ (shift-in (transport∈ p₀ i₀)))) ∘ (id ⊗₁ realize↭ p₀)
          ≈ (id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀)))
              ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀)))
    inner = begin
      (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
        ∘ (id ⊗₁ realize↭ (shift-in (transport∈ p₀ i₀)))) ∘ (id ⊗₁ realize↭ p₀)
        ≈⟨ assoc ⟩
      swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
        ∘ ((id ⊗₁ realize↭ (shift-in (transport∈ p₀ i₀))) ∘ (id ⊗₁ realize↭ p₀))
        ≈˘⟨ refl⟩∘⟨ split₂ˡ ⟩
      swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
        ∘ (id ⊗₁ (realize↭ (shift-in (transport∈ p₀ i₀)) ∘ realize↭ p₀))
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ extract-sound p₀ i₀) ⟩
      swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
        ∘ (id ⊗₁ ((id ⊗₁ realize↭ (extract p₀ i₀)) ∘ realize↭ (shift-in i₀)))
        ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
      swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ ys₀ ─ transport∈ p₀ i₀ ⟧ᴹ
        ∘ ((id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))) ∘ (id ⊗₁ realize↭ (shift-in i₀)))
        ≈⟨ pullˡ (swap₁-naturalʳ (realize↭ (extract p₀ i₀))) ⟩
      ((id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀))) ∘ swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ (id ⊗₁ realize↭ (shift-in i₀))
        ≈⟨ assoc ⟩
      (id ⊗₁ (id ⊗₁ realize↭ (extract p₀ i₀)))
        ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀))) ∎

    -- The Yang–Baxter core: extracting through both leading elements and
    -- then swapping them equals swapping first and extracting through the
    -- swapped pair.
    core : swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ (⟦ y ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
             ∘ ((id ⊗₁ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀))))
               ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
         ≈ (id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)
             ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ (⟦ z ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
               ∘ (id ⊗₁ (swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀)))))
    core = begin
      swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ (⟦ y ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ ((id ⊗₁ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀))))
          ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
        ≈⟨ refl⟩∘⟨ (split₂ˡ ⟩∘⟨refl) ⟩
      swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ (⟦ y ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ (((id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ) ∘ (id ⊗₁ (id ⊗₁ realize↭ (shift-in i₀))))
          ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ)
        ≈⟨ refl⟩∘⟨ assoc ⟩
      swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ (⟦ y ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ ((id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)
          ∘ ((id ⊗₁ (id ⊗₁ realize↭ (shift-in i₀))) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ⟧ᴹ))
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ swap₁-naturalʳ (realize↭ (shift-in i₀)) ⟩
      swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ (⟦ y ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ ((id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)
          ∘ (swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ x ∷ (xs₀ ─ i₀) ⟧ᴹ ∘ (id ⊗₁ (id ⊗₁ realize↭ (shift-in i₀)))))
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ (⟦ y ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ (((id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ x ∷ (xs₀ ─ i₀) ⟧ᴹ)
          ∘ (id ⊗₁ (id ⊗₁ realize↭ (shift-in i₀))))
        ≈⟨ sym-assoc ⟩
      (swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ (⟦ y ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ ((id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ) ∘ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ x ∷ (xs₀ ─ i₀) ⟧ᴹ))
        ∘ (id ⊗₁ (id ⊗₁ realize↭ (shift-in i₀)))
        ≈⟨ swap₁-yang-baxter ⟩∘⟨refl ⟩
      ((id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ (⟦ z ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ) ∘ (id ⊗₁ swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)))
        ∘ (id ⊗₁ (id ⊗₁ realize↭ (shift-in i₀)))
        ≈⟨ assoc ⟩
      (id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ ((swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ (⟦ z ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ) ∘ (id ⊗₁ swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ))
          ∘ (id ⊗₁ (id ⊗₁ realize↭ (shift-in i₀))))
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ (⟦ z ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
          ∘ ((id ⊗₁ swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ) ∘ (id ⊗₁ (id ⊗₁ realize↭ (shift-in i₀)))))
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩
      (id ⊗₁ swap₁ ⟦ y ⟧ₐ ⟦ z ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ)
        ∘ (swap₁ ⟦ y ⟧ₐ ⟦ x ⟧ₐ (⟦ z ⟧ₐ ⊗₀ ⟦ xs₀ ─ i₀ ⟧ᴹ)
          ∘ (id ⊗₁ (swap₁ ⟦ z ⟧ₐ ⟦ x ⟧ₐ ⟦ xs₀ ─ i₀ ⟧ᴹ ∘ (id ⊗₁ realize↭ (shift-in i₀))))) ∎
extract-sound (trans p₀ q₀) i = begin
  realize↭ (shift-in (transport∈ q₀ (transport∈ p₀ i))) ∘ (realize↭ q₀ ∘ realize↭ p₀)
    ≈⟨ pullˡ (extract-sound q₀ (transport∈ p₀ i)) ⟩
  ((id ⊗₁ realize↭ (extract q₀ (transport∈ p₀ i))) ∘ realize↭ (shift-in (transport∈ p₀ i)))
    ∘ realize↭ p₀
    ≈⟨ assoc ⟩
  (id ⊗₁ realize↭ (extract q₀ (transport∈ p₀ i)))
    ∘ (realize↭ (shift-in (transport∈ p₀ i)) ∘ realize↭ p₀)
    ≈⟨ refl⟩∘⟨ extract-sound p₀ i ⟩
  (id ⊗₁ realize↭ (extract q₀ (transport∈ p₀ i)))
    ∘ ((id ⊗₁ realize↭ (extract p₀ i)) ∘ realize↭ (shift-in i))
    ≈⟨ pullˡ (⟺ split₂ˡ) ⟩
  (id ⊗₁ (realize↭ (extract q₀ (transport∈ p₀ i)) ∘ realize↭ (extract p₀ i)))
    ∘ realize↭ (shift-in i) ∎

-- Witness invariance (Sₙ coherence)

-- Two witnesses with the same position list realize equally. The list is
-- first-order, computable data, so closed instances discharge by `refl`.
realize-positions : {xs ys : List Atom} (p q : xs ↭ ys)
  → positions p ≡ positions q → realize↭ p ≈ realize↭ q
realize-positions {[]} p q _ = begin
  realize↭ p            ≈⟨ realize-nil-eq p ⟩
  substₑ (nil-eq p)     ≈⟨ substₑ-nil-irrelevant (nil-eq p) (nil-eq q) ⟩
  substₑ (nil-eq q)     ≈˘⟨ realize-nil-eq q ⟩
  realize↭ q            ∎
realize-positions {x ∷ xs} {ys} p q eq =
  step (transport∈ p (here ≡refl)) (transport∈ q (here ≡refl))
       (extract p (here ≡refl)) (extract q (here ≡refl))
       (extract-sound p (here ≡refl)) (extract-sound q (here ≡refl))
       (∷-injectiveˡ eq) (∷-injectiveʳ eq)
  where
    step : (ip iq : x ∈ ys) (ep : xs ↭ (ys ─ ip)) (eq' : xs ↭ (ys ─ iq))
      → realize↭ (shift-in ip) ∘ realize↭ p
          ≈ (id {⟦ x ⟧ₐ} ⊗₁ realize↭ ep) ∘ realize↭ (shift-in (here {xs = xs} ≡refl))
      → realize↭ (shift-in iq) ∘ realize↭ q
          ≈ (id {⟦ x ⟧ₐ} ⊗₁ realize↭ eq') ∘ realize↭ (shift-in (here {xs = xs} ≡refl))
      → pos ip ≡ pos iq → positions ep ≡ positions eq'
      → realize↭ p ≈ realize↭ q
    step ip iq ep eq' Sp Sq peq teq with ∈-pos-injective ip iq peq
    ... | ≡refl = begin
      realize↭ p
        ≈˘⟨ Cancellers.cancelˡ (realize-sym-cancelˡ (shift-in ip)) ⟩
      realize↭ (↭-sym (shift-in ip)) ∘ (realize↭ (shift-in ip) ∘ realize↭ p)
        ≈⟨ refl⟩∘⟨ Sp ⟩
      realize↭ (↭-sym (shift-in ip)) ∘ ((id {⟦ x ⟧ₐ} ⊗₁ realize↭ ep) ∘ realize↭ (shift-in (here {xs = xs} ≡refl)))
        ≈⟨ refl⟩∘⟨ identityʳ ⟩
      realize↭ (↭-sym (shift-in ip)) ∘ (id {⟦ x ⟧ₐ} ⊗₁ realize↭ ep)
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ realize-positions ep eq' teq) ⟩
      realize↭ (↭-sym (shift-in ip)) ∘ (id {⟦ x ⟧ₐ} ⊗₁ realize↭ eq')
        ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
      realize↭ (↭-sym (shift-in ip)) ∘ ((id {⟦ x ⟧ₐ} ⊗₁ realize↭ eq') ∘ realize↭ (shift-in (here {xs = xs} ≡refl)))
        ≈˘⟨ refl⟩∘⟨ Sq ⟩
      realize↭ (↭-sym (shift-in ip)) ∘ (realize↭ (shift-in ip) ∘ realize↭ q)
        ≈⟨ Cancellers.cancelˡ (realize-sym-cancelˡ (shift-in ip)) ⟩
      realize↭ q ∎
