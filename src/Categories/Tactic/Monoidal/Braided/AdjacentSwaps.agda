{-# OPTIONS --safe --without-K #-}


open import Level using (Level)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)

module Categories.Tactic.Monoidal.Braided.AdjacentSwaps
  {o ℓ e a : Level}
  {𝒞 : Category o ℓ e}
  {V : Monoidal 𝒞}
  (B : Braided V)
  {Atom : Set a}
  (⟦_⟧ₐ : Atom → Category.Obj 𝒞)
  where

open import Data.Product using (_,_)
open import Data.List.Base using (List; _∷_; _++_)
open import Categories.Tactic.Monoidal.Braided
  using (module Evaluation)

open import Categories.Tactic.Monoidal.Core V ⟦_⟧ₐ
  using () renaming (eval to ⟦_⟧ᴹ)
open import Categories.Tactic.Monoidal.Coherence V ⟦_⟧ₐ
  using () renaming (μ⇒ to μ)
open Evaluation B ⟦_⟧ₐ using (σ⇒)

open Category 𝒞
open Monoidal V using (_⊗₀_; _⊗₁_; associator; assoc-commute-to; assoc-commute-from; module ⊗)
open Braided B using (braiding; hexagon₁)
open import Categories.Category.Monoidal.Reasoning V
open import Categories.Category.Monoidal.Utilities V using (module Shorthands; pentagon-inv)
open Shorthands
open import Categories.Morphism.Reasoning 𝒞
  using (assoc²βε; pullˡ; elimˡ; elimʳ; module Cancellers)

-- The braiding that swaps the first two factors of a right-nested triple.
swap₁ : (P Q R : Obj) → (P ⊗₀ (Q ⊗₀ R)) ⇒ (Q ⊗₀ (P ⊗₀ R))
swap₁ P Q R = α⇒ ∘ (σ⇒ {P} {Q} ⊗₁ id) ∘ α⇐

private
  pentaR-cancel : ∀ {P Q R S} →
    (α⇒ {P} {Q} {R} ⊗₁ id {S}) ∘ (α⇐ ⊗₁ id) ≈ id
  pentaR-cancel = ⊗-cancel associator.isoʳ identity²

-- Pure-associator pentagon rearrangement used to slide adjacent swaps through
-- the homomorphism merge.
pentaR-swap : ∀ {P Q R S}
  → (α⇒ {P} {Q} {R} ⊗₁ id {S}) ∘ α⇐
  ≈ (α⇐ ∘ (id ⊗₁ α⇐)) ∘ α⇒
pentaR-swap {P} {Q} {R} {S} = begin
  (α⇒ ⊗₁ id) ∘ α⇐
    ≈˘⟨ refl⟩∘⟨ Cancellers.cancelʳ (associator.isoˡ {P} {Q} {R ⊗₀ S}) ⟩
  (α⇒ ⊗₁ id) ∘ ((α⇐ ∘ α⇐) ∘ α⇒)
    ≈˘⟨ refl⟩∘⟨ (pentagon-inv {X = P} {Y = Q} {Z = R} {W = S} ⟩∘⟨refl) ⟩
  (α⇒ ⊗₁ id)
    ∘ ((((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ (assoc ⟩∘⟨refl) ⟩
  (α⇒ ⊗₁ id)
    ∘ (((α⇐ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ α⇐))) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  (α⇒ ⊗₁ id)
    ∘ ((α⇐ ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ α⇐)) ∘ α⇒))
    ≈⟨ Cancellers.cancelˡ pentaR-cancel ⟩
  (α⇐ ∘ (id ⊗₁ α⇐)) ∘ α⇒ ∎

-- `swap₁` is natural in the third factor: the braiding touches only P and Q.
swap₁-naturalʳ : ∀ {P Q R R'} (h : R ⇒ R')
  → swap₁ P Q R' ∘ (id {P} ⊗₁ (id {Q} ⊗₁ h))
    ≈ (id {Q} ⊗₁ (id {P} ⊗₁ h)) ∘ swap₁ P Q R
swap₁-naturalʳ {P} {Q} {R} {R'} h = begin
  (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ h))
    ≈⟨ assoc²βε ⟩
  α⇒ ∘ (σ⇒ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (id ⊗₁ h)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-to ⟩
  α⇒ ∘ (σ⇒ ⊗₁ id) ∘ (((id ⊗₁ id) ⊗₁ h) ∘ α⇐)
    ≈⟨ refl⟩∘⟨ pullˡ mid ⟩
  α⇒ ∘ (((id ⊗₁ id) ⊗₁ h) ∘ (σ⇒ ⊗₁ id)) ∘ α⇐
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ ((id ⊗₁ id) ⊗₁ h) ∘ (σ⇒ ⊗₁ id) ∘ α⇐
    ≈⟨ pullˡ assoc-commute-from ⟩
  ((id ⊗₁ (id ⊗₁ h)) ∘ α⇒) ∘ (σ⇒ ⊗₁ id) ∘ α⇐
    ≈⟨ assoc ⟩
  (id ⊗₁ (id ⊗₁ h)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∎
  where
    mid : (σ⇒ {P} {Q} ⊗₁ id {R'}) ∘ ((id {P} ⊗₁ id {Q}) ⊗₁ h)
        ≈ ((id {Q} ⊗₁ id {P}) ⊗₁ h) ∘ (σ⇒ {P} {Q} ⊗₁ id {R})
    mid = begin
      (σ⇒ {P} {Q} ⊗₁ id {R'}) ∘ ((id {P} ⊗₁ id {Q}) ⊗₁ h)
        ≈˘⟨ ⊗-distrib-over-∘ ⟩
      (σ⇒ {P} {Q} ∘ (id {P} ⊗₁ id {Q})) ⊗₁ (id {R'} ∘ h)
        ≈⟨ elimʳ ⊗.identity ⟩⊗⟨ identityˡ ⟩
      σ⇒ {P} {Q} ⊗₁ h
        ≈⟨ (⟺ (elimˡ ⊗.identity)) ⟩⊗⟨ (⟺ identityʳ) ⟩
      ((id {Q} ⊗₁ id {P}) ∘ σ⇒ {P} {Q}) ⊗₁ (h ∘ id {R})
        ≈⟨ ⊗-distrib-over-∘ ⟩
      ((id {Q} ⊗₁ id {P}) ⊗₁ h) ∘ (σ⇒ {P} {Q} ⊗₁ id {R}) ∎

-- `swap₁` is natural in the middle factor (braiding naturality whiskered by
-- the associators).
swap₁-naturalᵐ : ∀ {P Q Q' R} (g : Q ⇒ Q')
  → swap₁ P Q' R ∘ (id {P} ⊗₁ (g ⊗₁ id {R}))
    ≈ (g ⊗₁ id {P ⊗₀ R}) ∘ swap₁ P Q R
swap₁-naturalᵐ {P} {Q} {Q'} {R} g = begin
  (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (g ⊗₁ id))
    ≈⟨ assoc²βε ⟩
  α⇒ ∘ (σ⇒ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (g ⊗₁ id)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-to ⟩
  α⇒ ∘ (σ⇒ ⊗₁ id) ∘ (((id ⊗₁ g) ⊗₁ id) ∘ α⇐)
    ≈⟨ refl⟩∘⟨ pullˡ mid ⟩
  α⇒ ∘ (((g ⊗₁ id) ⊗₁ id) ∘ (σ⇒ ⊗₁ id)) ∘ α⇐
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (σ⇒ ⊗₁ id) ∘ α⇐
    ≈⟨ pullˡ assoc-commute-from ⟩
  ((g ⊗₁ (id ⊗₁ id)) ∘ α⇒) ∘ (σ⇒ ⊗₁ id) ∘ α⇐
    ≈⟨ ((refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl) ⟩∘⟨refl ⟩
  ((g ⊗₁ id) ∘ α⇒) ∘ (σ⇒ ⊗₁ id) ∘ α⇐
    ≈⟨ assoc ⟩
  (g ⊗₁ id) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∎
  where
    mid : (σ⇒ {P} {Q'} ⊗₁ id {R}) ∘ ((id {P} ⊗₁ g) ⊗₁ id {R})
        ≈ ((g ⊗₁ id {P}) ⊗₁ id {R}) ∘ (σ⇒ {P} {Q} ⊗₁ id {R})
    mid = begin
      (σ⇒ ⊗₁ id) ∘ ((id ⊗₁ g) ⊗₁ id)
        ≈˘⟨ ⊗-distrib-over-∘ ⟩
      (σ⇒ ∘ (id ⊗₁ g)) ⊗₁ (id ∘ id)
        ≈⟨ braiding.⇒.commute (id , g) ⟩⊗⟨ identity² ⟩
      ((g ⊗₁ id) ∘ σ⇒) ⊗₁ id
        ≈⟨ split₁ˡ ⟩
      ((g ⊗₁ id) ⊗₁ id) ∘ (σ⇒ ⊗₁ id) ∎

-- The whiskered braiding `σ ⊗ id` is `swap₁` conjugated by the associator.
swap₁-σ : ∀ {Q R X}
  → (σ⇒ {Q} {R} ⊗₁ id {X}) ≈ α⇐ ∘ swap₁ Q R X ∘ α⇒
swap₁-σ {Q} {R} {X} = ⟺ (begin
  α⇐ ∘ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (α⇒ ∘ (((σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (α⇒ ∘ ((σ⇒ ⊗₁ id) ∘ (α⇐ ∘ α⇒)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimʳ associator.isoˡ ⟩
  α⇐ ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))
    ≈⟨ Cancellers.cancelˡ associator.isoˡ ⟩
  σ⇒ ⊗₁ id ∎)

-- Braiding past a two-block factors into two adjacent swaps across the
-- regrouping associator: `hexagon₁` for `swap₁`, object-general (hoisted
-- from the `braid-atom` step).
swap₁-hexagon : ∀ {P Q R T}
  → swap₁ P (Q ⊗₀ R) T ∘ (id ⊗₁ α⇐)
    ≈ α⇐ ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T)
swap₁-hexagon {P} {Q} {R} {T} = begin
  swap₁ P (Q ⊗₀ R) T ∘ (id ⊗₁ α⇐)
    ≈⟨ assoc²βε ⟩
  α⇒ ∘ ((σ⇒ {P} {Q ⊗₀ R} ⊗₁ id)
    ∘ (α⇐ {P} {Q ⊗₀ R} {T} ∘ (id ⊗₁ α⇐)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ suffix-pentagon ⟩
  α⇒ ∘ ((σ⇒ {P} {Q ⊗₀ R} ⊗₁ id)
    ∘ ((α⇒ {P} {Q} {R} ⊗₁ id)
        ∘ (α⇐ {P ⊗₀ Q} {R} {T}
            ∘ α⇐ {P} {Q} {R ⊗₀ T})))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  α⇒ ∘ (((σ⇒ {P} {Q ⊗₀ R} ⊗₁ id)
    ∘ (α⇒ {P} {Q} {R} ⊗₁ id))
    ∘ (α⇐ {P ⊗₀ Q} {R} {T}
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))
    ≈⟨ refl⟩∘⟨ ((⟺ split₁ˡ) ⟩∘⟨refl) ⟩
  α⇒ ∘ (((σ⇒ {P} {Q ⊗₀ R} ∘ α⇒ {P} {Q} {R}) ⊗₁ id)
    ∘ (α⇐ {P ⊗₀ Q} {R} {T}
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))
    ≈⟨ refl⟩∘⟨ ((hex₁' ⟩⊗⟨refl) ⟩∘⟨refl) ⟩
  α⇒ ∘ (((α⇐ {Q} {R} {P}
    ∘ ((id ⊗₁ σ⇒ {P} {R})
        ∘ (α⇒ {Q} {P} {R} ∘ (σ⇒ {P} {Q} ⊗₁ id)))) ⊗₁ id)
    ∘ (α⇐ {P ⊗₀ Q} {R} {T}
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))
    ≈⟨ refl⟩∘⟨ (split₁ˡ ⟩∘⟨refl) ⟩
  α⇒ ∘ (((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ (((id ⊗₁ σ⇒ {P} {R})
        ∘ (α⇒ {Q} {P} {R} ∘ (σ⇒ {P} {Q} ⊗₁ id))) ⊗₁ id))
    ∘ (α⇐ {P ⊗₀ Q} {R} {T}
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ ((((id ⊗₁ σ⇒ {P} {R})
        ∘ (α⇒ {Q} {P} {R} ∘ (σ⇒ {P} {Q} ⊗₁ id))) ⊗₁ id)
    ∘ (α⇐ {P ⊗₀ Q} {R} {T}
        ∘ α⇐ {P} {Q} {R ⊗₀ T})))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ⟩
  α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ ((((id ⊗₁ σ⇒ {P} {R}) ⊗₁ id)
    ∘ (((α⇒ {Q} {P} {R} ∘ (σ⇒ {P} {Q} ⊗₁ id)) ⊗₁ id)))
    ∘ (α⇐ {P ⊗₀ Q} {R} {T}
        ∘ α⇐ {P} {Q} {R ⊗₀ T})))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ split₁ˡ) ⟩∘⟨refl ⟩
  α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ ((((id ⊗₁ σ⇒ {P} {R}) ⊗₁ id)
    ∘ ((α⇒ {Q} {P} {R} ⊗₁ id)
    ∘ ((σ⇒ {P} {Q} ⊗₁ id) ⊗₁ id)))
    ∘ (α⇐ {P ⊗₀ Q} {R} {T}
        ∘ α⇐ {P} {Q} {R ⊗₀ T})))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc²βε ⟩
  α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ (((id ⊗₁ σ⇒ {P} {R}) ⊗₁ id)
    ∘ ((α⇒ {Q} {P} {R} ⊗₁ id)
    ∘ (((σ⇒ {P} {Q} ⊗₁ id) ⊗₁ id)
    ∘ (α⇐ {P ⊗₀ Q} {R} {T}
        ∘ α⇐ {P} {Q} {R ⊗₀ T})))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ move-i ⟩
  α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ (((id ⊗₁ σ⇒ {P} {R}) ⊗₁ id)
    ∘ ((α⇒ {Q} {P} {R} ⊗₁ id)
    ∘ ((α⇐ {Q ⊗₀ P} {R} {T}
          ∘ (σ⇒ {P} {Q} ⊗₁ id))
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ (((id ⊗₁ σ⇒ {P} {R}) ⊗₁ id)
    ∘ ((α⇒ {Q} {P} {R} ⊗₁ id)
    ∘ (α⇐ {Q ⊗₀ P} {R} {T}
    ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T})))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (pentaR-swap {Q} {P} {R} {T}) ⟩
  α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ (((id ⊗₁ σ⇒ {P} {R}) ⊗₁ id)
    ∘ (((α⇐ {Q} {P ⊗₀ R} {T}
      ∘ id ⊗₁ α⇐ {P} {R} {T})
      ∘ α⇒ {Q} {P} {R ⊗₀ T})
      ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ (((id ⊗₁ σ⇒ {P} {R}) ⊗₁ id)
    ∘ ((α⇐ {Q} {P ⊗₀ R} {T}
      ∘ id ⊗₁ α⇐ {P} {R} {T})
      ∘ (α⇒ {Q} {P} {R ⊗₀ T}
      ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T})))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ (((id ⊗₁ σ⇒ {P} {R}) ⊗₁ id)
    ∘ (α⇐ {Q} {P ⊗₀ R} {T}
    ∘ ((id ⊗₁ α⇐ {P} {R} {T})
    ∘ (α⇒ {Q} {P} {R ⊗₀ T}
    ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ move-iii ○ assoc) ⟩
  α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ (α⇐ {Q} {R ⊗₀ P} {T}
    ∘ ((id ⊗₁ (σ⇒ {P} {R} ⊗₁ id))
    ∘ ((id ⊗₁ α⇐ {P} {R} {T})
    ∘ (α⇒ {Q} {P} {R ⊗₀ T}
    ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))))))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  α⇒ ∘ (((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ α⇐ {Q} {R ⊗₀ P} {T})
    ∘ ((id ⊗₁ (σ⇒ {P} {R} ⊗₁ id))
    ∘ ((id ⊗₁ α⇐ {P} {R} {T})
    ∘ (α⇒ {Q} {P} {R ⊗₀ T}
    ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T})))))
    ≈⟨ sym-assoc ⟩
  (α⇒ ∘ ((α⇐ {Q} {R} {P} ⊗₁ id)
    ∘ α⇐ {Q} {R ⊗₀ P} {T}))
    ∘ ((id ⊗₁ (σ⇒ {P} {R} ⊗₁ id))
    ∘ ((id ⊗₁ α⇐ {P} {R} {T})
    ∘ (α⇒ {Q} {P} {R ⊗₀ T}
    ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))))
    ≈⟨ front-penta ⟩∘⟨refl ⟩
  (α⇐ {Q} {R} {P ⊗₀ T} ∘ id ⊗₁ α⇒ {R} {P} {T})
    ∘ ((id ⊗₁ (σ⇒ {P} {R} ⊗₁ id))
    ∘ ((id ⊗₁ α⇐ {P} {R} {T})
    ∘ (α⇒ {Q} {P} {R ⊗₀ T}
    ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))))
    ≈⟨ assoc ⟩
  α⇐ {Q} {R} {P ⊗₀ T}
    ∘ ((id ⊗₁ α⇒ {R} {P} {T})
    ∘ ((id ⊗₁ (σ⇒ {P} {R} ⊗₁ id))
    ∘ ((id ⊗₁ α⇐ {P} {R} {T})
    ∘ (α⇒ {Q} {P} {R ⊗₀ T}
    ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T})))))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  α⇐ {Q} {R} {P ⊗₀ T}
    ∘ ((id ⊗₁ α⇒ {R} {P} {T})
    ∘ (((id ⊗₁ (σ⇒ {P} {R} ⊗₁ id))
        ∘ (id ⊗₁ α⇐ {P} {R} {T}))
    ∘ (α⇒ {Q} {P} {R ⊗₀ T}
    ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T}))))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  α⇐ {Q} {R} {P ⊗₀ T}
    ∘ (((id ⊗₁ α⇒ {R} {P} {T})
    ∘ ((id ⊗₁ (σ⇒ {P} {R} ⊗₁ id))
        ∘ (id ⊗₁ α⇐ {P} {R} {T})))
    ∘ (α⇒ {Q} {P} {R ⊗₀ T}
    ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T})))
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (⟺ split₂ˡ)) ⟩∘⟨refl ⟩
  α⇐ {Q} {R} {P ⊗₀ T}
    ∘ (((id ⊗₁ α⇒ {R} {P} {T})
    ∘ (id ⊗₁ ((σ⇒ {P} {R} ⊗₁ id) ∘ α⇐ {P} {R} {T})))
    ∘ (α⇒ {Q} {P} {R ⊗₀ T}
    ∘ ((σ⇒ {P} {Q} ⊗₁ id)
        ∘ α⇐ {P} {Q} {R ⊗₀ T})))
    ≈⟨ refl⟩∘⟨ (⟺ split₂ˡ) ⟩∘⟨refl ⟩
  α⇐ ∘ (id ⊗₁ swap₁ P R T)
    ∘ swap₁ P Q (R ⊗₀ T) ∎

  where
    -- `hexagon₁` as a plain `_≈_` (its `Commutation` type unfolds to this),
    -- composite side left; atomic side right.
    hex₁ : α⇒ ∘ (σ⇒ {P} {Q ⊗₀ R} ∘ α⇒)
         ≈ (id ⊗₁ σ⇒ {P} {R}) ∘ (α⇒ ∘ (σ⇒ {P} {Q} ⊗₁ id))
    hex₁ = ⟺ (hexagon₁ {X = P} {Y = Q} {Z = R})

    -- Rearranged hexagon: the composite braiding `σ⇒{A}{B⊗S}` (pre-associated)
    -- equals the atomic-braiding side transported by a single leading associator.
    hex₁' : σ⇒ {P} {Q ⊗₀ R} ∘ α⇒ {P} {Q} {R}
          ≈ α⇐ {Q} {R} {P}
              ∘ ((id ⊗₁ σ⇒ {P} {R})
                  ∘ (α⇒ {Q} {P} {R} ∘ (σ⇒ {P} {Q} ⊗₁ id)))
    hex₁' = begin
      σ⇒ ∘ α⇒
        ≈˘⟨ Cancellers.cancelˡ (associator.isoˡ {Q} {R} {P}) ⟩
      α⇐ ∘ (α⇒ ∘ (σ⇒ ∘ α⇒))
        ≈⟨ refl⟩∘⟨ hex₁ ⟩
      α⇐ ∘ ((id ⊗₁ σ⇒ {P} {R})
        ∘ (α⇒ ∘ (σ⇒ {P} {Q} ⊗₁ id))) ∎

    -- `(α⇒ ⊗ id)` and `(α⇐ ⊗ id)` cancel (whiskered associator iso).
    ⊗iso : (α⇒ {P} {Q} {R} ⊗₁ id {T})
             ∘ (α⇐ {P} {Q} {R} ⊗₁ id {T}) ≈ id
    ⊗iso = ⊗-cancel associator.isoʳ identity²

    -- Pentagon repackaging of the suffix associators (from `pentagon-inv`).
    suffix-pentagon : α⇐ {P} {Q ⊗₀ R} {T}
                   ∘ (id ⊗₁ α⇐ {Q} {R} {T})
               ≈ (α⇒ {P} {Q} {R} ⊗₁ id {T})
                   ∘ (α⇐ {P ⊗₀ Q} {R} {T}
                       ∘ α⇐ {P} {Q} {R ⊗₀ T})
    suffix-pentagon = begin
      α⇐ ∘ (id ⊗₁ α⇐)
        ≈˘⟨ Cancellers.cancelˡ ⊗iso ⟩
      (α⇒ ⊗₁ id) ∘ ((α⇐ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ α⇐)))
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      (α⇒ ⊗₁ id) ∘ (((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐))
        ≈⟨ refl⟩∘⟨ pentagon-inv ⟩
      (α⇒ ⊗₁ id) ∘ (α⇐ ∘ α⇐) ∎

    -- Slide the leading-pair braiding past the outer suffix associator.
    move-i : ((σ⇒ {P} {Q} ⊗₁ id {R}) ⊗₁ id {T})
               ∘ α⇐ {P ⊗₀ Q} {R} {T}
           ≈ α⇐ {Q ⊗₀ P} {R} {T}
               ∘ (σ⇒ {P} {Q} ⊗₁ id {R ⊗₀ T})
    move-i = begin
      ((σ⇒ ⊗₁ id) ⊗₁ id) ∘ α⇐
        ≈˘⟨ assoc-commute-to ⟩
      α⇐ ∘ (σ⇒ ⊗₁ (id ⊗₁ id))
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩
      α⇐ ∘ (σ⇒ ⊗₁ id) ∎

    -- Slide the suffix-atom braiding past the inner suffix associator.
    move-iii : ((id {Q} ⊗₁ σ⇒ {P} {R}) ⊗₁ id {T})
                 ∘ α⇐ {Q} {P ⊗₀ R} {T}
             ≈ α⇐ {Q} {R ⊗₀ P} {T}
                 ∘ (id {Q} ⊗₁ (σ⇒ {P} {R} ⊗₁ id {T}))
    move-iii = Equiv.sym assoc-commute-to

    -- `(id ⊗ α⇐) ∘ (id ⊗ α⇒)` cancels.
    id⊗iso : (id {Q} ⊗₁ α⇐ {R} {P} {T})
               ∘ (id {Q} ⊗₁ α⇒ {R} {P} {T}) ≈ id
    id⊗iso = ⊗-cancel identity² associator.isoˡ

    -- Front pentagon: collapse the leading three associators into `α⇐ ∘ (id ⊗ α⇒)`.
    front-penta : α⇒ {Q ⊗₀ R} {P} {T}
                    ∘ ((α⇐ {Q} {R} {P} ⊗₁ id {T})
                        ∘ α⇐ {Q} {R ⊗₀ P} {T})
                ≈ α⇐ {Q} {R} {P ⊗₀ T}
                    ∘ (id {Q} ⊗₁ α⇒ {R} {P} {T})
    front-penta = begin
      α⇒ ∘ ((α⇐ ⊗₁ id) ∘ α⇐)
        ≈˘⟨ refl⟩∘⟨ Cancellers.cancelʳ id⊗iso ⟩
      α⇒
        ∘ ((((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ α⇒))
        ≈⟨ refl⟩∘⟨ (pentagon-inv {X = Q} {Y = R} {Z = P} {W = T} ⟩∘⟨refl) ⟩
      α⇒ ∘ ((α⇐ ∘ α⇐) ∘ (id ⊗₁ α⇒))
        ≈⟨ refl⟩∘⟨ assoc ⟩
      α⇒ ∘ (α⇐ ∘ (α⇐ ∘ (id ⊗₁ α⇒)))
        ≈⟨ Cancellers.cancelˡ associator.isoʳ ⟩
      α⇐ ∘ (id ⊗₁ α⇒) ∎


-- The hexagon, conjugated: `swap₁` at a two-block is the composite of two
-- adjacent swaps, transported between the regrouping associators.
swap₁-hexagon-conj : ∀ {P Q R T}
  → swap₁ P (Q ⊗₀ R) T
    ≈ (α⇐ ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T)) ∘ (id ⊗₁ α⇒)
swap₁-hexagon-conj {P} {Q} {R} {T} = begin
  swap₁ P (Q ⊗₀ R) T
    ≈˘⟨ elimʳ (⊗-cancel identity² associator.isoˡ) ⟩
  swap₁ P (Q ⊗₀ R) T ∘ ((id ⊗₁ α⇐) ∘ (id ⊗₁ α⇒))
    ≈⟨ sym-assoc ⟩
  (swap₁ P (Q ⊗₀ R) T ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ α⇒)
    ≈⟨ swap₁-hexagon ⟩∘⟨refl ⟩
  (α⇐ ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T)) ∘ (id ⊗₁ α⇒) ∎

-- Yang–Baxter (the braid relation) for the adjacent swap: derived from the
-- hexagon (`swap₁-hexagon-conj`) and naturality of the block braiding in its
-- block argument at the braiding itself (`swap₁-naturalᵐ σ⇒`). Braided suffices —
-- no symmetry axiom is used.
swap₁-yang-baxter : ∀ {P Q R T}
  → swap₁ Q R (P ⊗₀ T) ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T)
    ≈ (id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T) ∘ (id ⊗₁ swap₁ Q R T)
swap₁-yang-baxter {P} {Q} {R} {T} = begin
  swap₁ Q R (P ⊗₀ T) ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T)
    ≈˘⟨ Cancellers.cancelˡ associator.isoʳ ⟩
  α⇒ ∘ (α⇐
    ∘ (swap₁ Q R (P ⊗₀ T) ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T)))
    ≈˘⟨ refl⟩∘⟨ Cancellers.cancelʳ (⊗-cancel identity² associator.isoʳ) ⟩
  α⇒
    ∘ (((α⇐
        ∘ (swap₁ Q R (P ⊗₀ T) ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T)))
      ∘ (id ⊗₁ α⇒)) ∘ (id ⊗₁ α⇐))
    ≈⟨ refl⟩∘⟨ (assoc ⟩∘⟨refl) ⟩
  α⇒
    ∘ ((α⇐
        ∘ ((swap₁ Q R (P ⊗₀ T) ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T))
        ∘ (id ⊗₁ α⇒))) ∘ (id ⊗₁ α⇐))
    ≈˘⟨ refl⟩∘⟨ (σ-side ⟩∘⟨refl) ⟩
  α⇒ ∘ (((σ⇒ {Q} {R} ⊗₁ id {P ⊗₀ T}) ∘ swap₁ P (Q ⊗₀ R) T) ∘ (id ⊗₁ α⇐))
    ≈⟨ refl⟩∘⟨ (natM-side ⟩∘⟨refl) ⟩
  α⇒
    ∘ ((α⇐
        ∘ (((id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T) ∘ (id ⊗₁ swap₁ Q R T))
        ∘ (id ⊗₁ α⇒))) ∘ (id ⊗₁ α⇐))
    ≈⟨ refl⟩∘⟨ (sym-assoc ⟩∘⟨refl) ⟩
  α⇒
    ∘ (((α⇐
        ∘ ((id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T) ∘ (id ⊗₁ swap₁ Q R T)))
      ∘ (id ⊗₁ α⇒)) ∘ (id ⊗₁ α⇐))
    ≈⟨ refl⟩∘⟨ Cancellers.cancelʳ (⊗-cancel identity² associator.isoʳ) ⟩
  α⇒ ∘ (α⇐
    ∘ ((id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T) ∘ (id ⊗₁ swap₁ Q R T)))
    ≈⟨ Cancellers.cancelˡ associator.isoʳ ⟩
  (id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T) ∘ (id ⊗₁ swap₁ Q R T) ∎
  where
    -- Both sides of the braid relation, conjugated into `σ ⊗ id ∘ swap₁` form.
    σ-side : (σ⇒ {Q} {R} ⊗₁ id {P ⊗₀ T}) ∘ swap₁ P (Q ⊗₀ R) T
           ≈ α⇐
               ∘ ((swap₁ Q R (P ⊗₀ T) ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T))
             ∘ (id ⊗₁ α⇒))
    σ-side = begin
      (σ⇒ ⊗₁ id) ∘ swap₁ P (Q ⊗₀ R) T
        ≈⟨ swap₁-σ ⟩∘⟨refl ⟩
      (α⇐ ∘ swap₁ Q R (P ⊗₀ T) ∘ α⇒) ∘ swap₁ P (Q ⊗₀ R) T
        ≈⟨ refl⟩∘⟨ swap₁-hexagon-conj ⟩
      (α⇐ ∘ swap₁ Q R (P ⊗₀ T) ∘ α⇒)
        ∘ ((α⇐ ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T))
          ∘ (id ⊗₁ α⇒))
        ≈⟨ assoc²βε ⟩
      α⇐ ∘ swap₁ Q R (P ⊗₀ T)
        ∘ (α⇒
          ∘ ((α⇐ ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T))
            ∘ (id ⊗₁ α⇒)))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ assoc) ⟩
      α⇐ ∘ swap₁ Q R (P ⊗₀ T)
        ∘ (α⇒
          ∘ (α⇐
            ∘ (((id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T)) ∘ (id ⊗₁ α⇒))))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Cancellers.cancelˡ associator.isoʳ ⟩
      α⇐ ∘ swap₁ Q R (P ⊗₀ T)
        ∘ (((id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T)) ∘ (id ⊗₁ α⇒))
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      α⇐
        ∘ ((swap₁ Q R (P ⊗₀ T) ∘ (id ⊗₁ swap₁ P R T) ∘ swap₁ P Q (R ⊗₀ T))
          ∘ (id ⊗₁ α⇒)) ∎

    natM-side : (σ⇒ {Q} {R} ⊗₁ id {P ⊗₀ T}) ∘ swap₁ P (Q ⊗₀ R) T
              ≈ α⇐
                  ∘ (((id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T) ∘ (id ⊗₁ swap₁ Q R T))
                ∘ (id ⊗₁ α⇒))
    natM-side = begin
      (σ⇒ ⊗₁ id) ∘ swap₁ P (Q ⊗₀ R) T
        ≈˘⟨ swap₁-naturalᵐ (σ⇒ {Q} {R}) ⟩
      swap₁ P (R ⊗₀ Q) T ∘ (id ⊗₁ (σ⇒ {Q} {R} ⊗₁ id {T}))
        ≈⟨ swap₁-hexagon-conj ⟩∘⟨ (refl⟩⊗⟨ swap₁-σ) ⟩
      ((α⇐ ∘ (id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T)) ∘ (id ⊗₁ α⇒))
        ∘ (id ⊗₁ (α⇐ ∘ swap₁ Q R T ∘ α⇒))
        ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
      ((α⇐ ∘ (id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T)) ∘ (id ⊗₁ α⇒))
        ∘ ((id ⊗₁ α⇐) ∘ (id ⊗₁ (swap₁ Q R T ∘ α⇒)))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩
      ((α⇐ ∘ (id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T)) ∘ (id ⊗₁ α⇒))
        ∘ ((id ⊗₁ α⇐) ∘ (id ⊗₁ swap₁ Q R T) ∘ (id ⊗₁ α⇒))
        ≈⟨ assoc ⟩
      (α⇐ ∘ (id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T))
        ∘ ((id ⊗₁ α⇒)
          ∘ ((id ⊗₁ α⇐) ∘ (id ⊗₁ swap₁ Q R T) ∘ (id ⊗₁ α⇒)))
        ≈⟨ refl⟩∘⟨ Cancellers.cancelˡ (⊗-cancel identity² associator.isoʳ) ⟩
      (α⇐ ∘ (id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T))
        ∘ ((id ⊗₁ swap₁ Q R T) ∘ (id ⊗₁ α⇒))
        ≈⟨ assoc ⟩
      α⇐
        ∘ (((id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T))
          ∘ ((id ⊗₁ swap₁ Q R T) ∘ (id ⊗₁ α⇒)))
        ≈⟨ refl⟩∘⟨ assoc ⟩
      α⇐
        ∘ ((id ⊗₁ swap₁ P Q T)
          ∘ (swap₁ P R (Q ⊗₀ T) ∘ ((id ⊗₁ swap₁ Q R T) ∘ (id ⊗₁ α⇒))))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
      α⇐
        ∘ ((id ⊗₁ swap₁ P Q T)
          ∘ ((swap₁ P R (Q ⊗₀ T) ∘ (id ⊗₁ swap₁ Q R T)) ∘ (id ⊗₁ α⇒)))
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      α⇐
        ∘ (((id ⊗₁ swap₁ P Q T) ∘ swap₁ P R (Q ⊗₀ T) ∘ (id ⊗₁ swap₁ Q R T))
          ∘ (id ⊗₁ α⇒)) ∎

-- The atomic swap commutes with the homomorphism merge `μ`.
swap₁-μ : (a b : Atom) (cs ds : List Atom)
  → (swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ⟧ᴹ ⊗₁ id {⟦ ds ⟧ᴹ}) ∘ μ (a ∷ b ∷ cs) ds
    ≈ μ (b ∷ a ∷ cs) ds ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ++ ds ⟧ᴹ
swap₁-μ a b cs ds = begin
  (swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ⟧ᴹ ⊗₁ id) ∘ μ (a ∷ b ∷ cs) ds
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩
  (swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ⟧ᴹ ⊗₁ id)
    ∘ (α⇐ ∘ ((id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ μ cs ds))))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  (swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ⟧ᴹ ⊗₁ id)
    ∘ ((α⇐ ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ (id ⊗₁ μ cs ds)))
    ≈⟨ pullˡ bridge ⟩
  ((α⇐ ∘ (id ⊗₁ α⇐)) ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ (⟦ cs ⟧ᴹ ⊗₀ ⟦ ds ⟧ᴹ))
    ∘ (id ⊗₁ (id ⊗₁ μ cs ds))
    ≈⟨ assoc ⟩
  (α⇐ ∘ (id ⊗₁ α⇐))
    ∘ (swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ (⟦ cs ⟧ᴹ ⊗₀ ⟦ ds ⟧ᴹ) ∘ (id ⊗₁ (id ⊗₁ μ cs ds)))
    ≈⟨ refl⟩∘⟨ swap₁-naturalʳ (μ cs ds) ⟩
  (α⇐ ∘ (id ⊗₁ α⇐))
    ∘ ((id ⊗₁ (id ⊗₁ μ cs ds)) ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ++ ds ⟧ᴹ)
    ≈⟨ sym-assoc ⟩
  ((α⇐ ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ (id ⊗₁ μ cs ds)))
    ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ++ ds ⟧ᴹ
    ≈⟨ assoc ⟩∘⟨refl ⟩
  (α⇐ ∘ ((id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ μ cs ds))))
    ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ++ ds ⟧ᴹ
    ≈⟨ (refl⟩∘⟨ ⟺ split₂ˡ) ⟩∘⟨refl ⟩
  μ (b ∷ a ∷ cs) ds ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ++ ds ⟧ᴹ ∎
  where
    -- Pure associator plus one braiding.
    bridge : (swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ⟧ᴹ ⊗₁ id {⟦ ds ⟧ᴹ})
               ∘ (α⇐ ∘ (id ⊗₁ α⇐))
           ≈ (α⇐ ∘ (id ⊗₁ α⇐))
               ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ (⟦ cs ⟧ᴹ ⊗₀ ⟦ ds ⟧ᴹ)
    bridge = begin
      (swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ⟧ᴹ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ α⇐))
        ≈⟨ split₁ˡ ⟩∘⟨refl ⟩
      ((α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id ∘ α⇐) ⊗₁ id))
        ∘ (α⇐ ∘ (id ⊗₁ α⇐))
        ≈⟨ (refl⟩∘⟨ split₁ˡ) ⟩∘⟨refl ⟩
      ((α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id))
        ∘ (α⇐ ∘ (id ⊗₁ α⇐))
        ≈⟨ assoc²βε ⟩
      (α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ⊗₁ id)
        ∘ ((α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
      (α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ⊗₁ id)
        ∘ (((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pentagon-inv ⟩
      (α⇒ ⊗₁ id) ∘ ((σ⇒ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ α⇐)
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      (α⇒ ⊗₁ id) ∘ (((σ⇒ ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ α⇐
        ≈⟨ refl⟩∘⟨ ⟺ assoc-commute-to ⟩∘⟨refl ⟩
      (α⇒ ⊗₁ id) ∘ (α⇐ ∘ (σ⇒ ⊗₁ (id ⊗₁ id))) ∘ α⇐
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity)) ⟩∘⟨refl ⟩
      (α⇒ ⊗₁ id) ∘ (α⇐ ∘ (σ⇒ ⊗₁ id)) ∘ α⇐
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (α⇒ ⊗₁ id) ∘ α⇐ ∘ (σ⇒ ⊗₁ id) ∘ α⇐
        ≈⟨ pullˡ (pentaR-swap {⟦ b ⟧ₐ} {⟦ a ⟧ₐ} {⟦ cs ⟧ᴹ} {⟦ ds ⟧ᴹ}) ⟩
      ((α⇐ ∘ (id ⊗₁ α⇐)) ∘ α⇒)
        ∘ (σ⇒ ⊗₁ id) ∘ α⇐
        ≈⟨ assoc ⟩
      (α⇐ ∘ (id ⊗₁ α⇐))
        ∘ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∎
