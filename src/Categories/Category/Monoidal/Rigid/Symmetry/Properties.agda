{-# OPTIONS --without-K --safe #-}


open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Category.Monoidal.Rigid.Symmetry.Properties
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) (S : Symmetric M) where

open import Data.Product using (_,_)
open import Categories.Category.Monoidal.Braided M using (Braided)

open Category C
open Monoidal M
open Symmetric S using (braided; commutative)
private module B = Braided braided
import Categories.Category.Monoidal.Utilities M as MonUtil
open import Categories.Category.Monoidal.Braided.Properties braided
  using (assoc-reverse; braiding-coherence; braiding-coherence-inv
        ; inv-braiding-coherence)
  renaming (module Shorthands to BraidedShorthands)
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
import Categories.Category.Monoidal.Construction.Reverse as Reverse
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Symmetric.Properties S
  using (braiding-selfInverse)
open import Categories.Morphism.Reasoning C

open MonUtil.Shorthands
open BraidedShorthands

private
  module RevProps =
    BraidedProperties (Reverse.Reverse-Braided braided)

private
  variable
    X : Obj

  λ⇒-as-ρ⇒σ⇐ : ∀ {X} → λ⇒ {X} ≈ ρ⇒ ∘ σ⇐ {X} {unit}
  λ⇒-as-ρ⇒σ⇐ = ⟺ inv-braiding-coherence

  ρ⇐-as-σ⇐λ⇐ : ∀ {X} → ρ⇐ {X} ≈ σ⇐ {X} {unit} ∘ λ⇐
  ρ⇐-as-σ⇐λ⇐ = ⟺ braiding-coherence-inv

  ρ⇒-as-λ⇒σ⇒ : ∀ {X} → ρ⇒ {X} ≈ λ⇒ ∘ σ⇒ {X} {unit}
  ρ⇒-as-λ⇒σ⇒ = ⟺ braiding-coherence

  λ⇐-as-σ⇒ρ⇐ : ∀ {X} → λ⇐ {X} ≈ σ⇒ {X} {unit} ∘ ρ⇐
  λ⇐-as-σ⇒ρ⇐ {X} = begin
    λ⇐ {X}                                  ≈˘⟨ identityˡ ⟩
    id ∘ λ⇐ {X}                             ≈˘⟨ B.braiding.iso.isoʳ (X , unit) ⟩∘⟨refl ⟩
    (σ⇒ {X} {unit} ∘ σ⇐ {X} {unit}) ∘ λ⇐    ≈⟨ assoc ⟩
    σ⇒ {X} {unit} ∘ σ⇐ {X} {unit} ∘ λ⇐      ≈⟨ refl⟩∘⟨ braiding-coherence-inv ⟩
    σ⇒ {X} {unit} ∘ ρ⇐ ∎

  mirrorˡ : ∀ {X Y Z} →
    (id {X} ⊗₁ σ⇒ {Z} {Y}) ∘ σ⇐ {X} {Z ⊗₀ Y}
    ≈ σ⇒ {Y ⊗₀ Z} {X} ∘ (σ⇒ {Z} {Y} ⊗₁ id {X})
  mirrorˡ {X} {Y} {Z} = begin
    (id {X} ⊗₁ σ⇒ {Z} {Y}) ∘ σ⇐ {X} {Z ⊗₀ Y}
      ≈⟨ refl⟩∘⟨ braiding-selfInverse ⟩
    (id {X} ⊗₁ σ⇒ {Z} {Y}) ∘ σ⇒ {Z ⊗₀ Y} {X}
      ≈˘⟨ B.braiding.⇒.commute (σ⇒ {Z} {Y} , id {X}) ⟩
    σ⇒ {Y ⊗₀ Z} {X} ∘ (σ⇒ {Z} {Y} ⊗₁ id {X}) ∎

  mirrorʳ : ∀ {X Y Z} →
    σ⇒ {X} {Y} ⊗₁ id {Z} ≈ σ⇐ {Y} {X} ⊗₁ id {Z}
  mirrorʳ = ⟺ braiding-selfInverse ⟩⊗⟨refl

  assocˡ : ∀ {X Y} →
    (σ⇒ {Y} {X} ⊗₁ id {X}) ∘ σ⇒ {X} {Y ⊗₀ X}
    ≈ σ⇐ {X ⊗₀ Y} {X} ∘ (id {X} ⊗₁ σ⇐ {X} {Y})
  assocˡ {X} {Y} = begin
    (σ⇒ {Y} {X} ⊗₁ id {X}) ∘ σ⇒ {X} {Y ⊗₀ X}
      ≈˘⟨ B.braiding.⇒.commute (id {X} , σ⇒ {Y} {X}) ⟩
    σ⇒ {X} {X ⊗₀ Y} ∘ (id {X} ⊗₁ σ⇒ {Y} {X})
      ≈⟨ ⟺ braiding-selfInverse ⟩∘⟨ (refl⟩⊗⟨ ⟺ braiding-selfInverse) ⟩
    σ⇐ {X ⊗₀ Y} {X} ∘ (id {X} ⊗₁ σ⇐ {X} {Y}) ∎

  braid-assoc⇐ : ∀ {X Y} →
      (σ⇒ {Y} {X} ⊗₁ id {X})
        ∘ σ⇒ {X} {Y ⊗₀ X}
        ∘ α⇒
        ∘ σ⇒ {X} {X ⊗₀ Y}
        ∘ (id {X} ⊗₁ σ⇒ {Y} {X})
    ≈ α⇐ {X} {Y} {X}
  braid-assoc⇐ {X} {Y} = begin
    (σ⇒ {Y} {X} ⊗₁ id {X}) ∘ σ⇒ {X} {Y ⊗₀ X}
      ∘ α⇒ ∘ σ⇒ {X} {X ⊗₀ Y} ∘ (id {X} ⊗₁ σ⇒ {Y} {X})
      ≈⟨ pullˡ assocˡ ⟩
    (σ⇐ {X ⊗₀ Y} {X} ∘ (id {X} ⊗₁ σ⇐ {X} {Y}))
      ∘ α⇒ ∘ σ⇒ {X} {X ⊗₀ Y} ∘ (id {X} ⊗₁ σ⇒ {Y} {X})
      ≈⟨ assoc ⟩
    σ⇐ {X ⊗₀ Y} {X} ∘ (id {X} ⊗₁ σ⇐ {X} {Y})
      ∘ α⇒ ∘ σ⇒ {X} {X ⊗₀ Y} ∘ (id {X} ⊗₁ σ⇒ {Y} {X})
      ≈⟨ assoc-reverse {X = X} {Y = Y} {Z = X} ⟩
    α⇐ ∎

  mirror-assoc : ∀ {X Y Z} →
      (id {X} ⊗₁ σ⇒ {Z} {Y})
        ∘ σ⇐ {X} {Z ⊗₀ Y}
        ∘ α⇐
        ∘ σ⇐ {Z} {Y ⊗₀ X}
        ∘ (σ⇒ {X} {Y} ⊗₁ id {Z})
    ≈ α⇒ {X} {Y} {Z}
  mirror-assoc {X} {Y} {Z} = begin
    (id {X} ⊗₁ σ⇒ {Z} {Y}) ∘ σ⇐ {X} {Z ⊗₀ Y}
      ∘ α⇐ ∘ σ⇐ {Z} {Y ⊗₀ X} ∘ (σ⇒ {X} {Y} ⊗₁ id {Z})
      ≈⟨ pullˡ mirrorˡ ⟩
    (σ⇒ {Y ⊗₀ Z} {X} ∘ (σ⇒ {Z} {Y} ⊗₁ id {X}))
      ∘ α⇐ ∘ σ⇐ {Z} {Y ⊗₀ X} ∘ (σ⇒ {X} {Y} ⊗₁ id {Z})
      ≈⟨ assoc ⟩
    σ⇒ {Y ⊗₀ Z} {X} ∘ (σ⇒ {Z} {Y} ⊗₁ id {X})
      ∘ α⇐ ∘ σ⇐ {Z} {Y ⊗₀ X} ∘ (σ⇒ {X} {Y} ⊗₁ id {Z})
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ mirrorʳ))) ⟩
    σ⇒ {Y ⊗₀ Z} {X} ∘ (σ⇒ {Z} {Y} ⊗₁ id {X})
      ∘ α⇐ ∘ σ⇐ {Z} {Y ⊗₀ X} ∘ (σ⇐ {Y} {X} ⊗₁ id {Z})
      ≈⟨ RevProps.assoc-reverse {X = Z} {Y = Y} {Z = X} ⟩
    α⇒ {X} {Y} {Z} ∎

private
  module Transposeˡ⇒ʳHelpers
      {A B Y} {E : A ⊗₀ Y ⇒ unit} {H : unit ⇒ Y ⊗₀ B} where

    cap : σ⇐ {B} {unit} ∘ (E ⊗₁ id {B})
        ≈ (id {B} ⊗₁ E) ∘ σ⇐ {B} {A ⊗₀ Y}
    cap = B.braiding.⇐.commute (id {B} , E)

    cap-slide-context :
      σ⇐ {B} {unit} ∘ (E ⊗₁ id {B}) ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
      ≈ (id {B} ⊗₁ E) ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
    cap-slide-context = begin
      σ⇐ {B} {unit} ∘ (E ⊗₁ id {B}) ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
        ≈⟨ pullˡ cap ⟩
      ((id {B} ⊗₁ E) ∘ σ⇐ {B} {A ⊗₀ Y})
        ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
        ≈⟨ assoc ⟩
      (id {B} ⊗₁ E) ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
        ∎

    cup : (id {A} ⊗₁ H) ∘ ρ⇐
        ≈ σ⇐ {A} {Y ⊗₀ B} ∘ (H ⊗₁ id {A}) ∘ λ⇐
    cup = begin
      (id {A} ⊗₁ H) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ ρ⇐-as-σ⇐λ⇐ ⟩
      (id {A} ⊗₁ H) ∘ (σ⇐ {A} {unit} ∘ λ⇐)
        ≈˘⟨ assoc ⟩
      ((id {A} ⊗₁ H) ∘ σ⇐ {A} {unit}) ∘ λ⇐
        ≈⟨ ⟺ (B.braiding.⇐.commute (id {A} , H)) ⟩∘⟨refl ⟩
      (σ⇐ {A} {Y ⊗₀ B} ∘ (H ⊗₁ id {A})) ∘ λ⇐
        ≈⟨ assoc ⟩
      σ⇐ {A} {Y ⊗₀ B} ∘ (H ⊗₁ id {A}) ∘ λ⇐ ∎

    cup-slide-context :
      α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
      ≈ α⇐ ∘ σ⇐ {A} {Y ⊗₀ B} ∘ (H ⊗₁ id {A}) ∘ λ⇐
    cup-slide-context = refl⟩∘⟨ cup

    E-split : id {B} ⊗₁ E
            ≈ (id {B} ⊗₁ (E ∘ σ⇒ {Y} {A})) ∘ (id {B} ⊗₁ σ⇒ {A} {Y})
    E-split = begin
      id {B} ⊗₁ E
        ≈⟨ refl⟩⊗⟨ introʳ commutative ⟩
      id {B} ⊗₁ (E ∘ (σ⇒ {Y} {A} ∘ σ⇒ {A} {Y}))
        ≈⟨ refl⟩⊗⟨ sym-assoc ⟩
      id {B} ⊗₁ ((E ∘ σ⇒ {Y} {A}) ∘ σ⇒ {A} {Y})
        ≈⟨ split₂ˡ ⟩
      (id {B} ⊗₁ (E ∘ σ⇒ {Y} {A})) ∘ (id {B} ⊗₁ σ⇒ {A} {Y}) ∎

    E-split-context :
      (id {B} ⊗₁ E) ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐
        ∘ σ⇐ {A} {Y ⊗₀ B} ∘ (H ⊗₁ id {A}) ∘ λ⇐
      ≈ (id {B} ⊗₁ (E ∘ σ⇒ {Y} {A})) ∘ (id {B} ⊗₁ σ⇒ {A} {Y})
        ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐
        ∘ σ⇐ {A} {Y ⊗₀ B} ∘ (H ⊗₁ id {A}) ∘ λ⇐
    E-split-context = begin
      (id {B} ⊗₁ E) ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐
        ∘ σ⇐ {A} {Y ⊗₀ B} ∘ (H ⊗₁ id {A}) ∘ λ⇐
        ≈⟨ E-split ⟩∘⟨refl ⟩
      ((id {B} ⊗₁ (E ∘ σ⇒ {Y} {A})) ∘ (id {B} ⊗₁ σ⇒ {A} {Y}))
        ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐
        ∘ σ⇐ {A} {Y ⊗₀ B} ∘ (H ⊗₁ id {A}) ∘ λ⇐
        ≈⟨ assoc ⟩
      (id {B} ⊗₁ (E ∘ σ⇒ {Y} {A})) ∘ (id {B} ⊗₁ σ⇒ {A} {Y})
        ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐
        ∘ σ⇐ {A} {Y ⊗₀ B} ∘ (H ⊗₁ id {A}) ∘ λ⇐
        ∎

    H-split : H ⊗₁ id {A}
            ≈ (σ⇒ {B} {Y} ⊗₁ id {A}) ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A})
    H-split = begin
      H ⊗₁ id {A}
        ≈⟨ introˡ commutative ⟩⊗⟨refl ⟩
      ((σ⇒ {B} {Y} ∘ σ⇒ {Y} {B}) ∘ H) ⊗₁ id {A}
        ≈⟨ assoc ⟩⊗⟨refl ⟩
      (σ⇒ {B} {Y} ∘ (σ⇒ {Y} {B} ∘ H)) ⊗₁ id {A}
        ≈⟨ split₁ˡ ⟩
      (σ⇒ {B} {Y} ⊗₁ id {A}) ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∎

    H-split-context :
      (H ⊗₁ id {A}) ∘ λ⇐
      ≈ (σ⇒ {B} {Y} ⊗₁ id {A}) ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
    H-split-context = begin
      (H ⊗₁ id {A}) ∘ λ⇐
        ≈⟨ H-split ⟩∘⟨refl ⟩
      ((σ⇒ {B} {Y} ⊗₁ id {A}) ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A})) ∘ λ⇐
        ≈⟨ assoc ⟩
      (σ⇒ {B} {Y} ⊗₁ id {A}) ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
        ∎

    mirror-context :
      (id {B} ⊗₁ σ⇒ {A} {Y}) ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐
        ∘ σ⇐ {A} {Y ⊗₀ B} ∘ (σ⇒ {B} {Y} ⊗₁ id {A})
        ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
      ≈ α⇒ ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
    mirror-context = begin
      (id {B} ⊗₁ σ⇒ {A} {Y}) ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐
        ∘ σ⇐ {A} {Y ⊗₀ B} ∘ (σ⇒ {B} {Y} ⊗₁ id {A})
        ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
      (id {B} ⊗₁ σ⇒ {A} {Y}) ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐
        ∘ (σ⇐ {A} {Y ⊗₀ B} ∘ (σ⇒ {B} {Y} ⊗₁ id {A}))
        ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
      (id {B} ⊗₁ σ⇒ {A} {Y}) ∘ σ⇐ {B} {A ⊗₀ Y}
        ∘ (α⇐ ∘ (σ⇐ {A} {Y ⊗₀ B} ∘ (σ⇒ {B} {Y} ⊗₁ id {A})))
        ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      (id {B} ⊗₁ σ⇒ {A} {Y})
        ∘ (σ⇐ {B} {A ⊗₀ Y}
          ∘ (α⇐ ∘ (σ⇐ {A} {Y ⊗₀ B} ∘ (σ⇒ {B} {Y} ⊗₁ id {A}))))
        ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
        ≈⟨ sym-assoc ⟩
      ((id {B} ⊗₁ σ⇒ {A} {Y}) ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐
        ∘ σ⇐ {A} {Y ⊗₀ B} ∘ (σ⇒ {B} {Y} ⊗₁ id {A}))
        ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
        ≈⟨ mirror-assoc ⟩∘⟨refl ⟩
      α⇒ ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
        ∎

transposeˡ⇒ʳ :
  ∀ {A B Y} {E : A ⊗₀ Y ⇒ unit} {H : unit ⇒ Y ⊗₀ B} →
  λ⇒ ∘ (E ⊗₁ id {B}) ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
  ≈ ρ⇒ ∘ (id {B} ⊗₁ (E ∘ σ⇒ {Y} {A}))
      ∘ α⇒ ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
transposeˡ⇒ʳ {A} {B} {Y} {E} {H} =
  let open Transposeˡ⇒ʳHelpers {A = A} {B = B} {Y = Y} {E = E} {H = H} in begin
  λ⇒ ∘ (E ⊗₁ id {B}) ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
    ≈⟨ λ⇒-as-ρ⇒σ⇐ ⟩∘⟨refl ⟩
  (ρ⇒ ∘ σ⇐ {B} {unit}) ∘ (E ⊗₁ id {B}) ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
    ≈⟨ assoc ⟩
  ρ⇒ ∘ σ⇐ {B} {unit} ∘ (E ⊗₁ id {B}) ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ cap-slide-context ⟩
  ρ⇒ ∘ (id {B} ⊗₁ E) ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cup-slide-context ⟩
  ρ⇒ ∘ (id {B} ⊗₁ E) ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐
    ∘ σ⇐ {A} {Y ⊗₀ B} ∘ (H ⊗₁ id {A}) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ E-split-context ⟩
  ρ⇒ ∘ (id {B} ⊗₁ (E ∘ σ⇒ {Y} {A})) ∘ (id {B} ⊗₁ σ⇒ {A} {Y})
    ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐ ∘ σ⇐ {A} {Y ⊗₀ B}
    ∘ (H ⊗₁ id {A}) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ H-split-context ⟩
  ρ⇒ ∘ (id {B} ⊗₁ (E ∘ σ⇒ {Y} {A})) ∘ (id {B} ⊗₁ σ⇒ {A} {Y})
    ∘ σ⇐ {B} {A ⊗₀ Y} ∘ α⇐ ∘ σ⇐ {A} {Y ⊗₀ B}
    ∘ (σ⇒ {B} {Y} ⊗₁ id {A}) ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ mirror-context ⟩
  ρ⇒ ∘ (id {B} ⊗₁ (E ∘ σ⇒ {Y} {A}))
    ∘ α⇒ ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐ ∎

transposeʳ⇒ˡ :
  ∀ {A B Y} {E : A ⊗₀ Y ⇒ unit} {H : unit ⇒ Y ⊗₀ B} →
  ρ⇒ ∘ (id {B} ⊗₁ (E ∘ σ⇒ {Y} {A}))
      ∘ α⇒ ∘ ((σ⇒ {Y} {B} ∘ H) ⊗₁ id {A}) ∘ λ⇐
  ≈ λ⇒ ∘ (E ⊗₁ id {B}) ∘ α⇐ ∘ (id {A} ⊗₁ H) ∘ ρ⇐
transposeʳ⇒ˡ = Equiv.sym transposeˡ⇒ʳ

private
  σ-cancelʳ : ∀ {A X Y} {f : Y ⊗₀ X ⇒ A} →
    (f ∘ σ⇒ {X} {Y}) ∘ σ⇒ {Y} {X} ≈ f
  σ-cancelʳ {X = X} {Y} {f} = begin
    (f ∘ σ⇒ {X} {Y}) ∘ σ⇒ {Y} {X}  ≈⟨ assoc ⟩
    f ∘ (σ⇒ {X} {Y} ∘ σ⇒ {Y} {X})  ≈⟨ refl⟩∘⟨ commutative {X = X} {Y = Y} ⟩
    f ∘ id                                  ≈⟨ identityʳ ⟩
    f                                       ∎

  σ-cancelˡ : ∀ {A X Y} {f : A ⇒ X ⊗₀ Y} →
    σ⇒ {Y} {X} ∘ (σ⇒ {X} {Y} ∘ f) ≈ f
  σ-cancelˡ {X = X} {Y} {f} = begin
    σ⇒ {Y} {X} ∘ (σ⇒ {X} {Y} ∘ f)  ≈⟨ sym-assoc ⟩
    (σ⇒ {Y} {X} ∘ σ⇒ {X} {Y}) ∘ f  ≈⟨ commutative {X = Y} {Y = X} ⟩∘⟨refl ⟩
    id ∘ f                                  ≈⟨ identityˡ ⟩
    f                                       ∎

  id⊗σ-cancelʳ : ∀ {X Y} {f : Y ⊗₀ X ⇒ unit} →
    id {X} ⊗₁ ((f ∘ σ⇒ {X} {Y}) ∘ σ⇒ {Y} {X}) ≈ id {X} ⊗₁ f
  id⊗σ-cancelʳ = refl⟩⊗⟨ σ-cancelʳ

  σ-cancelˡ⊗id : ∀ {X Y} {f : unit ⇒ X ⊗₀ Y} →
    (σ⇒ {Y} {X} ∘ (σ⇒ {X} {Y} ∘ f)) ⊗₁ id {X} ≈ f ⊗₁ id {X}
  σ-cancelˡ⊗id = σ-cancelˡ ⟩⊗⟨refl

braid-snakeˡ :
  ∀ {X Y} {ηₗ : unit ⇒ X ⊗₀ Y} {εₗ : Y ⊗₀ X ⇒ unit} →
  ρ⇒ ∘ (id {X} ⊗₁ εₗ) ∘ α⇒ ∘ (ηₗ ⊗₁ id {X}) ∘ λ⇐ ≈ id {X} →
  λ⇒ ∘ ((εₗ ∘ σ⇒ {X} {Y}) ⊗₁ id {X})
    ∘ α⇐ ∘ (id {X} ⊗₁ (σ⇒ {X} {Y} ∘ ηₗ)) ∘ ρ⇐
  ≈ id {X}
braid-snakeˡ {X} {Y} {ηₗ} {εₗ} snake = begin
  λ⇒ ∘ ((εₗ ∘ σ⇒ {X} {Y}) ⊗₁ id {X}) ∘ α⇐
    ∘ (id {X} ⊗₁ (σ⇒ {X} {Y} ∘ ηₗ)) ∘ ρ⇐
    ≈⟨ transposeˡ⇒ʳ {E = εₗ ∘ σ⇒ {X} {Y}} {H = σ⇒ {X} {Y} ∘ ηₗ} ⟩
  ρ⇒ ∘ (id {X} ⊗₁ ((εₗ ∘ σ⇒ {X} {Y}) ∘ σ⇒ {Y} {X}))
    ∘ α⇒ ∘ ((σ⇒ {Y} {X} ∘ (σ⇒ {X} {Y} ∘ ηₗ)) ⊗₁ id {X}) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ id⊗σ-cancelʳ {X = X} {Y = Y} {f = εₗ} ⟩∘⟨refl ⟩
  ρ⇒ ∘ (id {X} ⊗₁ εₗ) ∘ α⇒
    ∘ ((σ⇒ {Y} {X} ∘ (σ⇒ {X} {Y} ∘ ηₗ)) ⊗₁ id {X}) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (σ-cancelˡ⊗id {X = X} {Y = Y} {f = ηₗ} ⟩∘⟨refl))) ⟩
  ρ⇒ ∘ (id ⊗₁ εₗ) ∘ α⇒ ∘ (ηₗ ⊗₁ id) ∘ λ⇐
    ≈⟨ snake ⟩
  id ∎

braid-snakeʳ :
  ∀ {X Y} {ηᵣ : unit ⇒ Y ⊗₀ X} {εᵣ : X ⊗₀ Y ⇒ unit} →
  λ⇒ ∘ (εᵣ ⊗₁ id {X}) ∘ α⇐ ∘ (id {X} ⊗₁ ηᵣ) ∘ ρ⇐ ≈ id {X} →
  ρ⇒ ∘ (id {X} ⊗₁ (εᵣ ∘ σ⇒ {Y} {X}))
    ∘ α⇒ ∘ ((σ⇒ {Y} {X} ∘ ηᵣ) ⊗₁ id {X}) ∘ λ⇐
  ≈ id {X}
braid-snakeʳ {X} {Y} {ηᵣ} {εᵣ} snake = begin
  ρ⇒ ∘ (id {X} ⊗₁ (εᵣ ∘ σ⇒ {Y} {X}))
    ∘ α⇒ ∘ ((σ⇒ {Y} {X} ∘ ηᵣ) ⊗₁ id {X}) ∘ λ⇐
    ≈⟨ transposeʳ⇒ˡ {E = εᵣ} {H = ηᵣ} ⟩
  λ⇒ ∘ (εᵣ ⊗₁ id {X}) ∘ α⇐ ∘ (id {X} ⊗₁ ηᵣ) ∘ ρ⇐
    ≈⟨ snake ⟩
  id ∎
