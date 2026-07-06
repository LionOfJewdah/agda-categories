{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)

module Categories.Category.Monoidal.CompactClosed.CapInterchange
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) (S : Symmetric M) (R : LeftRigid M) where

open Category C
open Monoidal M
open LeftRigid R using (_⁻¹; ε)
open Symmetric S using (braiding)
open import Data.Product using (_,_)
import Categories.Category.Monoidal.Utilities M as MonUtil
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided S)
  using (braiding-coherence; inv-braiding-coherence)
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Symmetric.Properties S
  using (braiding-selfInverse)
open import Categories.Category.Monoidal.Reasoning M
open TensorIdentity using (⊗id-∘)
open import Categories.Morphism.Reasoning C
import Categories.Category.Monoidal.Properties M as MonoidalProps
open MonoidalProps.Kelly's using (coherence₃)
open MonoidalProps.Structural using (cap-reassoc; ρ-sweep; ρ-sweep-open)
open import Categories.Category.Monoidal.Interchange.Braided (Symmetric.braided S)
  using (swapInner; module swapInner; swapˡ; swapˡ-hexagon; swapInner-openˡ)
open import Categories.Category.Monoidal.Interchange.Symmetric S
  using (swapˡ-cancelʳ; swapInner-braidˡ)

open MonUtil.Shorthands
open BraidShorthands using (σ⇒; σ⇐)

private variable A B X : Obj

capʳ : ∀ {X} → X ⊗₀ X ⁻¹ ⇒ unit
capʳ {X} = ε {X} ∘ σ⇒ {X} {X ⁻¹}

cap-contextˡ : ∀ {X B} → X ⁻¹ ⊗₀ (X ⊗₀ B) ⇒ B
cap-contextˡ {X} {B} = λ⇒ ∘ (ε {X} ⊗₁ id {B}) ∘ α⇐

cap-contextʳ : ∀ {X B} → X ⊗₀ (X ⁻¹ ⊗₀ B) ⇒ B
cap-contextʳ {X} {B} = λ⇒ ∘ (capʳ {X} ⊗₁ id {B}) ∘ α⇐

scalar-braid : ∀ {P Q} {f : P ⇒ unit} {g : Q ⇒ unit} →
  λ⇒ ∘ (g ⊗₁ f) ∘ σ⇒ {P} {Q} ≈ ρ⇒ ∘ (f ⊗₁ g)
scalar-braid {P} {Q} {f} {g} = begin
  λ⇒ ∘ (g ⊗₁ f) ∘ σ⇒ {P} {Q}             ≈˘⟨ refl⟩∘⟨ braiding.⇒.commute (f , g) ⟩
  λ⇒ ∘ σ⇒ {unit} {unit} ∘ (f ⊗₁ g)       ≈˘⟨ assoc ⟩
  (λ⇒ ∘ σ⇒ {unit} {unit}) ∘ (f ⊗₁ g)     ≈⟨ braiding-coherence ⟩∘⟨refl ⟩
  ρ⇒ ∘ (f ⊗₁ g)                          ∎

wire-cap-slideʳ : ∀ {A P Q} {cap : P ⊗₀ Q ⇒ unit} →
  ρ⇒ ∘ (id {A} ⊗₁ cap) ∘ σ⇒ {P ⊗₀ Q} {A}
  ≈ λ⇒ ∘ (cap ⊗₁ id {A})
wire-cap-slideʳ {A} {P} {Q} {cap} = begin
  ρ⇒ ∘ (id {A} ⊗₁ cap) ∘ σ⇒ {P ⊗₀ Q} {A}
    ≈˘⟨ refl⟩∘⟨ braiding.⇒.commute (cap , id {A}) ⟩
  ρ⇒ ∘ σ⇒ {unit} {A} ∘ (cap ⊗₁ id {A})
    ≈˘⟨ refl⟩∘⟨ braiding-selfInverse {X = A} {Y = unit} ⟩∘⟨refl ⟩
  ρ⇒ ∘ σ⇐ {A} {unit} ∘ (cap ⊗₁ id {A})
    ≈⟨ sym-assoc ⟩
  (ρ⇒ ∘ σ⇐ {A} {unit}) ∘ (cap ⊗₁ id {A})
    ≈⟨ inv-braiding-coherence ⟩∘⟨refl ⟩
  λ⇒ ∘ (cap ⊗₁ id {A})
    ∎

pair-toʳ : ∀ {P Q B} → P ⊗₀ (Q ⊗₀ B) ⇒ B ⊗₀ (P ⊗₀ Q)
pair-toʳ {P} {Q} {B} = σ⇒ {P ⊗₀ Q} {B} ∘ α⇐ {P} {Q} {B}

cap-context-slideˡ : ∀ {X B} →
  cap-contextˡ {X} {B}
  ≈ ρ⇒ ∘ (id {B} ⊗₁ ε {X}) ∘ pair-toʳ {X ⁻¹} {X} {B}
cap-context-slideˡ {X} {B} = begin
  cap-contextˡ {X} {B}
    ≈⟨ sym-assoc ⟩
  (λ⇒ ∘ (ε {X} ⊗₁ id {B})) ∘ α⇐ {X ⁻¹} {X} {B}
    ≈˘⟨ wire-cap-slideʳ {A = B} {P = X ⁻¹} {Q = X} {cap = ε {X}} ⟩∘⟨refl ⟩
  (ρ⇒ ∘ (id {B} ⊗₁ ε {X}) ∘ σ⇒ {X ⁻¹ ⊗₀ X} {B})
    ∘ α⇐ {X ⁻¹} {X} {B}
    ≈⟨ assoc ⟩
  ρ⇒ ∘ ((id {B} ⊗₁ ε {X}) ∘ σ⇒ {X ⁻¹ ⊗₀ X} {B})
    ∘ α⇐ {X ⁻¹} {X} {B}
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ ∘ (id {B} ⊗₁ ε {X}) ∘ pair-toʳ {X ⁻¹} {X} {B}
    ∎

cap-context-slideʳ : ∀ {X B} →
  cap-contextʳ {X} {B}
  ≈ ρ⇒ ∘ (id {B} ⊗₁ capʳ {X}) ∘ pair-toʳ {X} {X ⁻¹} {B}
cap-context-slideʳ {X} {B} = begin
  cap-contextʳ {X} {B}
    ≈⟨ sym-assoc ⟩
  (λ⇒ ∘ (capʳ {X} ⊗₁ id {B})) ∘ α⇐ {X} {X ⁻¹} {B}
    ≈˘⟨ wire-cap-slideʳ {A = B} {P = X} {Q = X ⁻¹} {cap = capʳ {X}} ⟩∘⟨refl ⟩
  (ρ⇒ ∘ (id {B} ⊗₁ capʳ {X}) ∘ σ⇒ {X ⊗₀ X ⁻¹} {B})
    ∘ α⇐ {X} {X ⁻¹} {B}
    ≈⟨ assoc ⟩
  ρ⇒ ∘ ((id {B} ⊗₁ capʳ {X}) ∘ σ⇒ {X ⊗₀ X ⁻¹} {B})
    ∘ α⇐ {X} {X ⁻¹} {B}
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ ∘ (id {B} ⊗₁ capʳ {X}) ∘ pair-toʳ {X} {X ⁻¹} {B}
    ∎

cap-context-braidʳ : ∀ {X B} →
  cap-contextʳ {X} {B} ∘ (id {X} ⊗₁ σ⇒ {B} {X ⁻¹})
  ≈ ρ⇒ ∘ (id {B} ⊗₁ capʳ {X}) ∘ swapˡ {X} {B} {X ⁻¹}
cap-context-braidʳ {X} {B} = begin
  cap-contextʳ {X} {B} ∘ (id {X} ⊗₁ σ⇒ {B} {X ⁻¹})
    ≈⟨ cap-context-slideʳ {X} {B} ⟩∘⟨refl ⟩
  (ρ⇒ ∘ (id {B} ⊗₁ capʳ {X}) ∘ pair-toʳ {X} {X ⁻¹} {B})
    ∘ (id {X} ⊗₁ σ⇒ {B} {X ⁻¹})
    ≈⟨ assoc ⟩
  ρ⇒ ∘ ((id {B} ⊗₁ capʳ {X}) ∘ pair-toʳ {X} {X ⁻¹} {B})
    ∘ (id {X} ⊗₁ σ⇒ {B} {X ⁻¹})
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ ∘ (id {B} ⊗₁ capʳ {X})
    ∘ (pair-toʳ {X} {X ⁻¹} {B} ∘ (id {X} ⊗₁ σ⇒ {B} {X ⁻¹}))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swapˡ-cancelʳ {X} {X ⁻¹} {B} ⟩
  ρ⇒ ∘ (id {B} ⊗₁ capʳ {X}) ∘ swapˡ {X} {B} {X ⁻¹}
    ∎

braid-through-α : ∀ {X Y} →
  α⇒ {Y ⁻¹} {X} {X ⁻¹ ⊗₀ Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
  ≈ (id {Y ⁻¹} ⊗₁ (id {X} ⊗₁ σ⇒ {Y} {X ⁻¹}))
      ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
      ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
braid-through-α {X} {Y} = begin
  α⇒ {Y ⁻¹} {X} {X ⁻¹ ⊗₀ Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ≈⟨ refl⟩∘⟨ serialize₂₁ ⟩
  α⇒
    ∘ (id {Y ⁻¹ ⊗₀ X} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈˘⟨ assoc ⟩
  (α⇒
    ∘ (id {Y ⁻¹ ⊗₀ X} ⊗₁ σ⇒ {Y} {X ⁻¹}))
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈⟨ (refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ⟩∘⟨refl ⟩
  (α⇒
    ∘ ((id {Y ⁻¹} ⊗₁ id {X}) ⊗₁ σ⇒ {Y} {X ⁻¹}))
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈⟨ assoc-commute-from ⟩∘⟨refl ⟩
  ((id {Y ⁻¹} ⊗₁ (id {X} ⊗₁ σ⇒ {Y} {X ⁻¹}))
    ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹})
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈⟨ assoc ⟩
  (id {Y ⁻¹} ⊗₁ (id {X} ⊗₁ σ⇒ {Y} {X ⁻¹}))
    ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ∎

mid-capˡ : ∀ {A X B} → (A ⊗₀ X ⁻¹) ⊗₀ (X ⊗₀ B) ⇒ A ⊗₀ B
mid-capˡ {A} {X} {B} =
  ((ρ⇒ ⊗₁ id {B}) ∘ ((id {A} ⊗₁ ε {X}) ⊗₁ id {B}))
    ∘ (α⇒ {A} {X ⁻¹} {X} ⊗₁ id {B})
    ∘ α⇐ {A ⊗₀ X ⁻¹} {X} {B}

mid-capʳ : ∀ {A X B} → (A ⊗₀ X) ⊗₀ (X ⁻¹ ⊗₀ B) ⇒ A ⊗₀ B
mid-capʳ {A} {X} {B} =
  ((ρ⇒ ⊗₁ id {B}) ∘ ((id {A} ⊗₁ capʳ {X}) ⊗₁ id {B}))
    ∘ (α⇒ {A} {X} {X ⁻¹} ⊗₁ id {B})
    ∘ α⇐ {A ⊗₀ X} {X ⁻¹} {B}

group-capsʳ : ∀ {X Y} →
  (X ⊗₀ Y ⁻¹) ⊗₀ (Y ⊗₀ X ⁻¹) ⇒ (X ⊗₀ X ⁻¹) ⊗₀ (Y ⁻¹ ⊗₀ Y)
group-capsʳ {X} {Y} =
  swapInner.from {X} {Y ⁻¹} {X ⁻¹} {Y}
    ∘ (id {X ⊗₀ Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})

group-capsˡ : ∀ {X Y} →
  (X ⊗₀ Y ⁻¹) ⊗₀ (Y ⊗₀ X ⁻¹) ⇒ (Y ⁻¹ ⊗₀ Y) ⊗₀ (X ⊗₀ X ⁻¹)
group-capsˡ {X} {Y} =
  swapInner.from {Y ⁻¹} {X} {Y} {X ⁻¹}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})

group-caps-openˡ : ∀ {X Y} →
  group-capsˡ {X} {Y}
  ≈ α⇐ {Y ⁻¹} {Y} {X ⊗₀ X ⁻¹}
      ∘ (id {Y ⁻¹} ⊗₁ swapˡ {X} {Y} {X ⁻¹})
      ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
      ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
group-caps-openˡ {X} {Y} = begin
  group-capsˡ {X} {Y}
    ≈⟨ assoc ⟩
  α⇐ {Y ⁻¹} {Y} {X ⊗₀ X ⁻¹}
    ∘ ((id {Y ⁻¹} ⊗₁ swapˡ {X} {Y} {X ⁻¹})
      ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹})
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ {Y ⁻¹} {Y} {X ⊗₀ X ⁻¹}
    ∘ (id {Y ⁻¹} ⊗₁ swapˡ {X} {Y} {X ⁻¹})
    ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ∎

group-caps-openʳ : ∀ {X Y} →
  α⇒ {X} {X ⁻¹} {Y ⁻¹ ⊗₀ Y} ∘ group-capsʳ {X} {Y}
  ≈ (id {X} ⊗₁ pair-toʳ {Y ⁻¹} {Y} {X ⁻¹})
      ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
group-caps-openʳ {X} {Y} = begin
  α⇒ {X} {X ⁻¹} {Y ⁻¹ ⊗₀ Y} ∘ group-capsʳ {X} {Y}
    ≈˘⟨ assoc ⟩
  (α⇒ {X} {X ⁻¹} {Y ⁻¹ ⊗₀ Y}
    ∘ swapInner.from {X} {Y ⁻¹} {X ⁻¹} {Y})
    ∘ id {X ⊗₀ Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹}
    ≈⟨ swapInner-openˡ ⟩∘⟨refl ⟩
  ((id {X} ⊗₁ swapˡ {Y ⁻¹} {X ⁻¹} {Y})
    ∘ α⇒ {X} {Y ⁻¹} {X ⁻¹ ⊗₀ Y})
    ∘ id {X ⊗₀ Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹}
    ≈⟨ assoc ⟩
  (id {X} ⊗₁ swapˡ {Y ⁻¹} {X ⁻¹} {Y})
    ∘ α⇒ {X} {Y ⁻¹} {X ⁻¹ ⊗₀ Y}
    ∘ id {X ⊗₀ Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹}
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ⟩
  (id {X} ⊗₁ swapˡ {Y ⁻¹} {X ⁻¹} {Y})
    ∘ α⇒ {X} {Y ⁻¹} {X ⁻¹ ⊗₀ Y}
    ∘ (id {X} ⊗₁ id {Y ⁻¹}) ⊗₁ σ⇒ {Y} {X ⁻¹}
    ≈⟨ refl⟩∘⟨ assoc-commute-from ⟩
  (id {X} ⊗₁ swapˡ {Y ⁻¹} {X ⁻¹} {Y})
    ∘ (id {X} ⊗₁ (id {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹}))
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ≈˘⟨ assoc ⟩
  ((id {X} ⊗₁ swapˡ {Y ⁻¹} {X ⁻¹} {Y})
    ∘ id {X} ⊗₁ (id {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹}))
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ≈˘⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
  ((id {X} ∘ id {X})
    ⊗₁ (swapˡ {Y ⁻¹} {X ⁻¹} {Y}
      ∘ id {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹}))
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ≈⟨ (identity² ⟩⊗⟨ ⟺ (swapˡ-hexagon {X = Y ⁻¹} {Y = Y} {Z = X ⁻¹})) ⟩∘⟨refl ⟩
  (id {X} ⊗₁ pair-toʳ {Y ⁻¹} {Y} {X ⁻¹})
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ∎

cap-unitorʳ : ∀ {X Y} →
  capʳ {X} ∘ ρ⇒ {X ⊗₀ X ⁻¹}
    ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})
  ≈ ρ⇒ ∘ (capʳ {X} ⊗₁ ε {Y})
cap-unitorʳ {X} {Y} = begin
  capʳ {X} ∘ ρ⇒ {X ⊗₀ X ⁻¹} ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})
    ≈⟨ sym-assoc ⟩
  (capʳ {X} ∘ ρ⇒ {X ⊗₀ X ⁻¹}) ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})
    ≈˘⟨ unitorʳ-commute-from {f = capʳ {X}} ⟩∘⟨refl ⟩
  (ρ⇒ ∘ (capʳ {X} ⊗₁ id {unit})) ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})
    ≈⟨ assoc ⟩
  ρ⇒ ∘ (capʳ {X} ⊗₁ id {unit}) ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})
    ≈⟨ refl⟩∘⟨ merge₂ʳ ⟩
  ρ⇒ ∘ (capʳ {X} ⊗₁ (id {unit} ∘ ε {Y}))
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ identityˡ ⟩
  ρ⇒ ∘ (capʳ {X} ⊗₁ ε {Y})
    ∎

scalar-unitˡ : ∀ {P Q} {f : P ⇒ unit} {g : Q ⇒ unit} →
  f ∘ ρ⇒ {P} ∘ (id {P} ⊗₁ g) ≈ λ⇒ ∘ (f ⊗₁ g)
scalar-unitˡ {P} {Q} {f} {g} = begin
  f ∘ ρ⇒ {P} ∘ (id {P} ⊗₁ g)
    ≈⟨ sym-assoc ⟩
  (f ∘ ρ⇒ {P}) ∘ (id {P} ⊗₁ g)
    ≈˘⟨ unitorʳ-commute-from {f = f} ⟩∘⟨refl ⟩
  (ρ⇒ ∘ (f ⊗₁ id {unit})) ∘ (id {P} ⊗₁ g)
    ≈⟨ assoc ⟩
  ρ⇒ ∘ (f ⊗₁ id {unit}) ∘ (id {P} ⊗₁ g)
    ≈⟨ refl⟩∘⟨ merge₂ʳ ⟩
  ρ⇒ ∘ (f ⊗₁ (id {unit} ∘ g))
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ identityˡ ⟩
  ρ⇒ ∘ (f ⊗₁ g)
    ≈˘⟨ coherence₃ ⟩∘⟨refl ⟩
  λ⇒ ∘ (f ⊗₁ g)
    ∎

pair-sweepʳ : ∀ {X Y} →
  (id {X} ⊗₁ ((ρ⇒ ∘ (id {X ⁻¹} ⊗₁ ε {Y}))
    ∘ pair-toʳ {Y ⁻¹} {Y} {X ⁻¹}))
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
  ≈ ρ⇒ {X ⊗₀ X ⁻¹}
      ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})
      ∘ group-capsʳ {X} {Y}
pair-sweepʳ {X} {Y} = begin
  (id {X} ⊗₁ ((ρ⇒ ∘ (id {X ⁻¹} ⊗₁ ε {Y}))
    ∘ pair-toʳ {Y ⁻¹} {Y} {X ⁻¹}))
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ≈⟨ split₂ˡ ⟩∘⟨refl ⟩
  ((id {X} ⊗₁ (ρ⇒ {X ⁻¹} ∘ (id {X ⁻¹} ⊗₁ ε {Y})))
    ∘ (id {X} ⊗₁ pair-toʳ {Y ⁻¹} {Y} {X ⁻¹}))
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ≈⟨ assoc ⟩
  (id {X} ⊗₁ (ρ⇒ {X ⁻¹} ∘ (id {X ⁻¹} ⊗₁ ε {Y})))
    ∘ (id {X} ⊗₁ pair-toʳ {Y ⁻¹} {Y} {X ⁻¹})
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ≈˘⟨ refl⟩∘⟨ group-caps-openʳ {X} {Y} ⟩
  (id {X} ⊗₁ (ρ⇒ {X ⁻¹} ∘ (id {X ⁻¹} ⊗₁ ε {Y})))
    ∘ α⇒ {X} {X ⁻¹} {Y ⁻¹ ⊗₀ Y} ∘ group-capsʳ {X} {Y}
    ≈˘⟨ assoc ⟩
  ((id {X} ⊗₁ (ρ⇒ {X ⁻¹} ∘ (id {X ⁻¹} ⊗₁ ε {Y})))
    ∘ α⇒ {X} {X ⁻¹} {Y ⁻¹ ⊗₀ Y}) ∘ group-capsʳ {X} {Y}
    ≈⟨ ρ-sweep-open {X} {X ⁻¹} {Y ⁻¹ ⊗₀ Y} {ε {Y}} ⟩∘⟨refl ⟩
  (ρ⇒ {X ⊗₀ X ⁻¹} ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})) ∘ group-capsʳ {X} {Y}
    ≈⟨ assoc ⟩
  ρ⇒ {X ⊗₀ X ⁻¹} ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})
    ∘ group-capsʳ {X} {Y}
    ∎

mid-groupedˡ : ∀ {X Y} →
  mid-capˡ {A = X} {X = Y} {B = X ⁻¹}
  ≈ ρ⇒ {X ⊗₀ X ⁻¹}
      ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})
      ∘ group-capsʳ {X} {Y}
mid-groupedˡ {X} {Y} = begin
  mid-capˡ {A = X} {X = Y} {B = X ⁻¹}
    ≈˘⟨ cap-reassoc {A = X} {P = Y ⁻¹} {Q = Y} {B = X ⁻¹} {cap = ε {Y}} ⟩
  (id {X} ⊗₁ cap-contextˡ {Y} {X ⁻¹})
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ≈⟨ (refl⟩⊗⟨ cap-context-slideˡ {Y} {X ⁻¹}) ⟩∘⟨refl ⟩
  (id {X} ⊗₁ (ρ⇒ {X ⁻¹} ∘ (id {X ⁻¹} ⊗₁ ε {Y}) ∘ pair-toʳ {Y ⁻¹} {Y} {X ⁻¹}))
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ≈⟨ (refl⟩⊗⟨ sym-assoc) ⟩∘⟨refl ⟩
  (id {X} ⊗₁ ((ρ⇒ {X ⁻¹} ∘ (id {X ⁻¹} ⊗₁ ε {Y}))
    ∘ pair-toʳ {Y ⁻¹} {Y} {X ⁻¹}))
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ≈⟨ pair-sweepʳ {X} {Y} ⟩
  ρ⇒ {X ⊗₀ X ⁻¹} ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})
    ∘ group-capsʳ {X} {Y}
    ∎

close-capsʳ : ∀ {X Y} →
  capʳ {X} ∘ mid-capˡ {A = X} {X = Y} {B = X ⁻¹}
  ≈ ρ⇒ ∘ (capʳ {X} ⊗₁ ε {Y}) ∘ group-capsʳ {X} {Y}
close-capsʳ {X} {Y} = begin
  capʳ {X} ∘ mid-capˡ {A = X} {X = Y} {B = X ⁻¹}
    ≈⟨ refl⟩∘⟨ mid-groupedˡ {X} {Y} ⟩
  capʳ {X} ∘ (ρ⇒ {X ⊗₀ X ⁻¹} ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y})
    ∘ group-capsʳ {X} {Y})
    ≈⟨ assoc²εα ⟩
  ((capʳ {X} ∘ ρ⇒ {X ⊗₀ X ⁻¹}) ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y}))
    ∘ group-capsʳ {X} {Y}
    ≈˘⟨ (sym-assoc ⟩∘⟨refl) ⟩
  (capʳ {X} ∘ ρ⇒ {X ⊗₀ X ⁻¹} ∘ (id {X ⊗₀ X ⁻¹} ⊗₁ ε {Y}))
    ∘ group-capsʳ {X} {Y}
    ≈⟨ cap-unitorʳ {X} {Y} ⟩∘⟨refl ⟩
  (ρ⇒ ∘ (capʳ {X} ⊗₁ ε {Y})) ∘ group-capsʳ {X} {Y}
    ≈⟨ assoc ⟩
  ρ⇒ ∘ (capʳ {X} ⊗₁ ε {Y}) ∘ group-capsʳ {X} {Y}
    ∎

private
  split-cap-contextʳ : ∀ {X Y} →
    id {Y ⁻¹} ⊗₁
      (ρ⇒ {Y} ∘ (id {Y} ⊗₁ capʳ {X})
        ∘ swapˡ {X} {Y} {X ⁻¹})
    ≈ (id {Y ⁻¹} ⊗₁ (ρ⇒ {Y} ∘ (id {Y} ⊗₁ capʳ {X})))
        ∘ (id {Y ⁻¹} ⊗₁ swapˡ {X} {Y} {X ⁻¹})
  split-cap-contextʳ {X} {Y} = begin
    id {Y ⁻¹} ⊗₁
      (ρ⇒ {Y} ∘ (id {Y} ⊗₁ capʳ {X}) ∘ swapˡ {X} {Y} {X ⁻¹})
      ≈⟨ refl⟩⊗⟨ sym-assoc ⟩
    id {Y ⁻¹} ⊗₁
      ((ρ⇒ {Y} ∘ (id {Y} ⊗₁ capʳ {X})) ∘ swapˡ {X} {Y} {X ⁻¹})
      ≈⟨ split₂ˡ
           {f = id {Y ⁻¹}}
           {g = ρ⇒ {Y} ∘ (id {Y} ⊗₁ capʳ {X})}
           {h = swapˡ {X} {Y} {X ⁻¹}} ⟩
    (id {Y ⁻¹} ⊗₁ (ρ⇒ {Y} ∘ (id {Y} ⊗₁ capʳ {X})))
      ∘ (id {Y ⁻¹} ⊗₁ swapˡ {X} {Y} {X ⁻¹})
      ∎

  sweep-cap-contextʳ : ∀ {X Y} →
    id {Y ⁻¹} ⊗₁ (ρ⇒ {Y} ∘ (id {Y} ⊗₁ capʳ {X}))
    ≈ ρ⇒ {Y ⁻¹ ⊗₀ Y}
        ∘ (id {Y ⁻¹ ⊗₀ Y} ⊗₁ capʳ {X})
        ∘ α⇐ {Y ⁻¹} {Y} {X ⊗₀ X ⁻¹}
  sweep-cap-contextʳ {X} {Y} =
    ⟺ (ρ-sweep {X = Y ⁻¹} {Y = Y} {L = X ⊗₀ X ⁻¹} {capʳ {X}})

mid-groupedʳ : ∀ {X Y} →
  mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
  ≈ ρ⇒ {Y ⁻¹ ⊗₀ Y}
      ∘ (id {Y ⁻¹ ⊗₀ Y} ⊗₁ capʳ {X})
      ∘ group-capsˡ {X} {Y}
mid-groupedʳ {X} {Y} = begin
  mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ≈˘⟨ cap-reassoc {A = Y ⁻¹} {P = X} {Q = X ⁻¹} {B = Y} {cap = capʳ {X}} ⟩∘⟨refl ⟩
  ((id {Y ⁻¹} ⊗₁ cap-contextʳ {X} {Y}) ∘ α⇒ {Y ⁻¹} {X} {X ⁻¹ ⊗₀ Y})
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ≈⟨ assoc ⟩
  (id {Y ⁻¹} ⊗₁ cap-contextʳ {X} {Y})
    ∘ α⇒ {Y ⁻¹} {X} {X ⁻¹ ⊗₀ Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ≈⟨ refl⟩∘⟨ braid-through-α {X} {Y} ⟩
  (id {Y ⁻¹} ⊗₁ cap-contextʳ {X} {Y})
    ∘ (id {Y ⁻¹} ⊗₁ (id {X} ⊗₁ σ⇒ {Y} {X ⁻¹}))
    ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈˘⟨ assoc ⟩
  ((id {Y ⁻¹} ⊗₁ cap-contextʳ {X} {Y})
    ∘ (id {Y ⁻¹} ⊗₁ (id {X} ⊗₁ σ⇒ {Y} {X ⁻¹})))
    ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈⟨ merge₂ˡ ⟩∘⟨refl ⟩
  (id {Y ⁻¹} ⊗₁ (cap-contextʳ {X} {Y} ∘ (id {X} ⊗₁ σ⇒ {Y} {X ⁻¹})))
    ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈⟨ (refl⟩⊗⟨ cap-context-braidʳ {X} {Y}) ⟩∘⟨refl ⟩
  (id {Y ⁻¹} ⊗₁ (ρ⇒ {Y} ∘ (id {Y} ⊗₁ capʳ {X}) ∘ swapˡ {X} {Y} {X ⁻¹}))
    ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈⟨ split-cap-contextʳ {X} {Y} ⟩∘⟨refl ⟩
  ((id {Y ⁻¹} ⊗₁ (ρ⇒ {Y} ∘ (id {Y} ⊗₁ capʳ {X})))
    ∘ (id {Y ⁻¹} ⊗₁ swapˡ {X} {Y} {X ⁻¹}))
    ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈⟨ assoc ⟩
  (id {Y ⁻¹} ⊗₁ (ρ⇒ {Y} ∘ (id {Y} ⊗₁ capʳ {X})))
    ∘ (id {Y ⁻¹} ⊗₁ swapˡ {X} {Y} {X ⁻¹})
    ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})
    ≈⟨ pushˡ sweep-cap-contextʳ
          {f = (id {Y ⁻¹} ⊗₁ swapˡ {X} {Y} {X ⁻¹})
            ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
            ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})} ⟩
  ρ⇒ ∘ (((id {Y ⁻¹ ⊗₀ Y} ⊗₁ capʳ {X})
    ∘ α⇐ {Y ⁻¹} {Y} {X ⊗₀ X ⁻¹})
    ∘ ((id {Y ⁻¹} ⊗₁ swapˡ {X} {Y} {X ⁻¹})
      ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
      ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹})))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ ∘ ((id {Y ⁻¹ ⊗₀ Y} ⊗₁ capʳ {X})
    ∘ (α⇐ {Y ⁻¹} {Y} {X ⊗₀ X ⁻¹}
      ∘ ((id {Y ⁻¹} ⊗₁ swapˡ {X} {Y} {X ⁻¹})
        ∘ α⇒ {Y ⁻¹} {X} {Y ⊗₀ X ⁻¹}
        ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ id {Y ⊗₀ X ⁻¹}))))
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ group-caps-openˡ {X} {Y} ⟩
  ρ⇒ {Y ⁻¹ ⊗₀ Y} ∘ (id {Y ⁻¹ ⊗₀ Y} ⊗₁ capʳ {X})
    ∘ group-capsˡ {X} {Y}
    ∎

close-capsˡ : ∀ {X Y} →
  ε {Y} ∘ mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
  ≈ λ⇒ ∘ (ε {Y} ⊗₁ capʳ {X}) ∘ group-capsˡ {X} {Y}
close-capsˡ {X} {Y} = begin
  ε {Y} ∘ mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ≈⟨ refl⟩∘⟨ mid-groupedʳ {X} {Y} ⟩
  ε {Y} ∘ (ρ⇒ {Y ⁻¹ ⊗₀ Y} ∘ (id {Y ⁻¹ ⊗₀ Y} ⊗₁ capʳ {X})
    ∘ group-capsˡ {X} {Y})
    ≈⟨ assoc²εα ⟩
  ((ε {Y} ∘ ρ⇒ {Y ⁻¹ ⊗₀ Y}) ∘ (id {Y ⁻¹ ⊗₀ Y} ⊗₁ capʳ {X}))
    ∘ group-capsˡ {X} {Y}
    ≈˘⟨ (sym-assoc ⟩∘⟨refl) ⟩
  (ε {Y} ∘ ρ⇒ {Y ⁻¹ ⊗₀ Y} ∘ (id {Y ⁻¹ ⊗₀ Y} ⊗₁ capʳ {X}))
    ∘ group-capsˡ {X} {Y}
    ≈⟨ scalar-unitˡ {f = ε {Y}} {g = capʳ {X}} ⟩∘⟨refl ⟩
  (λ⇒ ∘ (ε {Y} ⊗₁ capʳ {X})) ∘ group-capsˡ {X} {Y}
    ≈⟨ assoc ⟩
  λ⇒ ∘ (ε {Y} ⊗₁ capʳ {X}) ∘ group-capsˡ {X} {Y}
    ∎

group-caps-braid : ∀ {X Y} →
  group-capsˡ {X} {Y}
  ≈ σ⇒ {X ⊗₀ X ⁻¹} {Y ⁻¹ ⊗₀ Y} ∘ group-capsʳ {X} {Y}
group-caps-braid {X} {Y} =
  swapInner-braidˡ {W = X} {X = Y ⁻¹} {Y = Y} {Z = X ⁻¹}

cap-context-swapˡ : ∀ {X B} →
  cap-contextˡ {X} {B} ∘ swapˡ {X} {X ⁻¹} {B}
  ≈ cap-contextʳ {X} {B}
cap-context-swapˡ {X} {B} = begin
  cap-contextˡ {X} {B} ∘ swapˡ {X} {X ⁻¹} {B}
    ≈⟨ assoc ⟩
  λ⇒ ∘ ((ε {X} ⊗₁ id {B}) ∘ α⇐ {X ⁻¹} {X} {B}) ∘ swapˡ {X} {X ⁻¹} {B}
    ≈⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (ε {X} ⊗₁ id {B}) ∘ α⇐ {X ⁻¹} {X} {B} ∘ swapˡ {X} {X ⁻¹} {B}
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ (ε {X} ⊗₁ id {B})
    ∘ (α⇐ {X ⁻¹} {X} {B} ∘ α⇒ {X ⁻¹} {X} {B})
    ∘ (σ⇒ {X} {X ⁻¹} ⊗₁ id {B}) ∘ α⇐ {X} {X ⁻¹} {B}
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (associator.isoˡ ⟩∘⟨refl) ⟩
  λ⇒ ∘ (ε {X} ⊗₁ id {B}) ∘ id
    ∘ (σ⇒ {X} {X ⁻¹} ⊗₁ id {B}) ∘ α⇐ {X} {X ⁻¹} {B}
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ identityˡ ⟩
  λ⇒ ∘ (ε {X} ⊗₁ id {B}) ∘ (σ⇒ {X} {X ⁻¹} ⊗₁ id {B})
    ∘ α⇐ {X} {X ⁻¹} {B}
    ≈˘⟨ refl⟩∘⟨ assoc ⟩
  λ⇒ ∘ ((ε {X} ⊗₁ id {B}) ∘ (σ⇒ {X} {X ⁻¹} ⊗₁ id {B}))
    ∘ α⇐ {X} {X ⁻¹} {B}
    ≈˘⟨ refl⟩∘⟨ ⊗id-∘ ⟩∘⟨refl ⟩
  cap-contextʳ {X} {B}
    ∎

mid-swapInnerˡ : ∀ {A X B} →
  mid-capˡ {A} {X} {B} ∘ swapInner.from {A} {X} {X ⁻¹} {B}
  ≈ mid-capʳ {A} {X} {B}
mid-swapInnerˡ {A} {X} {B} = begin
  mid-capˡ {A} {X} {B} ∘ swapInner.from {A} {X} {X ⁻¹} {B}
    ≈˘⟨ cap-reassoc {A = A} {P = X ⁻¹} {Q = X} {B = B} {cap = ε {X}} ⟩∘⟨refl ⟩
  ((id {A} ⊗₁ cap-contextˡ {X} {B}) ∘ α⇒ {A} {X ⁻¹} {X ⊗₀ B})
    ∘ swapInner.from {A} {X} {X ⁻¹} {B}
    ≈⟨ assoc ⟩
  (id {A} ⊗₁ cap-contextˡ {X} {B})
    ∘ α⇒ {A} {X ⁻¹} {X ⊗₀ B} ∘ swapInner.from {A} {X} {X ⁻¹} {B}
    ≈⟨ refl⟩∘⟨ swapInner-openˡ ⟩
  (id {A} ⊗₁ cap-contextˡ {X} {B})
    ∘ (id {A} ⊗₁ swapˡ {X} {X ⁻¹} {B})
    ∘ α⇒ {A} {X} {X ⁻¹ ⊗₀ B}
    ≈˘⟨ assoc ⟩
  ((id {A} ⊗₁ cap-contextˡ {X} {B}) ∘ (id {A} ⊗₁ swapˡ {X} {X ⁻¹} {B}))
    ∘ α⇒ {A} {X} {X ⁻¹ ⊗₀ B}
    ≈⟨ (merge₂ˡ ⟩∘⟨refl) ⟩
  (id {A} ⊗₁ (cap-contextˡ {X} {B} ∘ swapˡ {X} {X ⁻¹} {B}))
    ∘ α⇒ {A} {X} {X ⁻¹ ⊗₀ B}
    ≈⟨ (refl⟩⊗⟨ cap-context-swapˡ {X} {B}) ⟩∘⟨refl ⟩
  (id {A} ⊗₁ cap-contextʳ {X} {B}) ∘ α⇒ {A} {X} {X ⁻¹ ⊗₀ B}
    ≈⟨ cap-reassoc {A = A} {P = X} {Q = X ⁻¹} {B = B} {cap = capʳ {X}} ⟩
  mid-capʳ {A} {X} {B}
    ∎

cap-context-slide : ∀ {X Y} →
  ε {Y} ∘ ((id {Y ⁻¹} ⊗₁ cap-contextʳ {X} {Y})
    ∘ α⇒ {Y ⁻¹} {X} {X ⁻¹ ⊗₀ Y})
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
  ≈ capʳ {X} ∘ (id {X} ⊗₁ cap-contextˡ {Y} {X ⁻¹})
      ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
cap-context-slide {X} {Y} =
  begin
  ε {Y} ∘ ((id {Y ⁻¹} ⊗₁ cap-contextʳ {X} {Y})
    ∘ α⇒ {Y ⁻¹} {X} {X ⁻¹ ⊗₀ Y})
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ≈⟨ refl⟩∘⟨ cap-reassoc {A = Y ⁻¹} {P = X} {Q = X ⁻¹} {B = Y} {cap = capʳ {X}} ⟩∘⟨refl ⟩
  ε {Y} ∘ mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ≈⟨ close-capsˡ {X} {Y} ⟩
  λ⇒ ∘ (ε {Y} ⊗₁ capʳ {X}) ∘ group-capsˡ {X} {Y}
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ group-caps-braid {X} {Y} ⟩
  λ⇒ ∘ (ε {Y} ⊗₁ capʳ {X}) ∘ σ⇒ {X ⊗₀ X ⁻¹} {Y ⁻¹ ⊗₀ Y} ∘ group-capsʳ {X} {Y}
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  λ⇒ ∘ (((ε {Y} ⊗₁ capʳ {X}) ∘ σ⇒ {X ⊗₀ X ⁻¹} {Y ⁻¹ ⊗₀ Y})
    ∘ group-capsʳ {X} {Y})
    ≈⟨ sym-assoc ⟩
  (λ⇒ ∘ ((ε {Y} ⊗₁ capʳ {X}) ∘ σ⇒ {X ⊗₀ X ⁻¹} {Y ⁻¹ ⊗₀ Y})) ∘ group-capsʳ {X} {Y}
    ≈⟨ scalar-braid {P = X ⊗₀ X ⁻¹} {Q = Y ⁻¹ ⊗₀ Y} {f = capʳ {X}} {g = ε {Y}} ⟩∘⟨refl ⟩
  (ρ⇒ ∘ (capʳ {X} ⊗₁ ε {Y})) ∘ group-capsʳ {X} {Y}
    ≈⟨ assoc ⟩
  ρ⇒ ∘ (capʳ {X} ⊗₁ ε {Y}) ∘ group-capsʳ {X} {Y}
    ≈˘⟨ close-capsʳ {X} {Y} ⟩
  capʳ {X} ∘ mid-capˡ {A = X} {X = Y} {B = X ⁻¹}
    ≈˘⟨ refl⟩∘⟨ cap-reassoc {A = X} {P = Y ⁻¹} {Q = Y} {B = X ⁻¹} {cap = ε {Y}} ⟩
  capʳ {X} ∘ (id {X} ⊗₁ cap-contextˡ {Y} {X ⁻¹}) ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ∎

paired-cap-interchangeʳ : ∀ {X Y} →
  ε {Y} ∘ mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
  ≈ capʳ {X} ∘ mid-capˡ {A = X} {X = Y} {B = X ⁻¹}
paired-cap-interchangeʳ {X} {Y} = begin
  ε {Y} ∘ mid-capʳ {A = Y ⁻¹} {X = X} {B = Y}
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ≈˘⟨ refl⟩∘⟨ cap-reassoc {A = Y ⁻¹} {P = X} {Q = X ⁻¹} {B = Y} {cap = capʳ {X}} ⟩∘⟨refl ⟩
  ε {Y} ∘ ((id {Y ⁻¹} ⊗₁ cap-contextʳ {X} {Y})
    ∘ α⇒ {Y ⁻¹} {X} {X ⁻¹ ⊗₀ Y})
    ∘ (σ⇒ {X} {Y ⁻¹} ⊗₁ σ⇒ {Y} {X ⁻¹})
    ≈⟨ cap-context-slide {X} {Y} ⟩
  capʳ {X} ∘ (id {X} ⊗₁ cap-contextˡ {Y} {X ⁻¹})
    ∘ α⇒ {X} {Y ⁻¹} {Y ⊗₀ X ⁻¹}
    ≈⟨ refl⟩∘⟨ cap-reassoc {A = X} {P = Y ⁻¹} {Q = Y} {B = X ⁻¹} {cap = ε {Y}} ⟩
  capʳ {X} ∘ mid-capˡ {A = X} {X = Y} {B = X ⁻¹}
    ∎
