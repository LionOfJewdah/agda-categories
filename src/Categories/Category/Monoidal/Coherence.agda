{-# OPTIONS --without-K --safe #-}


open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Category.Monoidal.Coherence
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C) where

open Category C
open Monoidal M
import Categories.Category.Monoidal.Utilities M as MonUtil
open import Categories.Category.Monoidal.Reasoning M
open TensorIdentity using (id⊗id; whisker-∘; ⊗id-∘)
open import Categories.Morphism.Reasoning C
import Categories.Category.Monoidal.Properties M as MonoidalProps
open MonoidalProps.Kelly's using (coherence₂)
open import Categories.Tactic.Monoidal using (module Finite)
open Finite M using (module Solver)

open MonUtil.Shorthands

cancel-middle : ∀ {A B C D}
  {prefix : B ⇒ D} {from : C ⇒ B} {to : B ⇒ C} {suffix : A ⇒ B} →
  from ∘ to ≈ id → (prefix ∘ from) ∘ (to ∘ suffix) ≈ prefix ∘ suffix
cancel-middle {prefix = prefix} {from = from} {to = to} {suffix = suffix} from∘to =
  assoc
  ○ (refl⟩∘⟨ (sym-assoc ○ (from∘to ⟩∘⟨refl) ○ identityˡ))

α-slide : ∀ {A P Q Z} {h : P ⇒ Q} →
  (id {A} ⊗₁ (h ⊗₁ id {Z})) ∘ α⇒ {A} {P} {Z}
  ≈ α⇒ {A} {Q} {Z} ∘ ((id {A} ⊗₁ h) ⊗₁ id {Z})
α-slide = ⟺ assoc-commute-from

α-sweep : ∀ {Y B P Q} {k : P ⇒ Q} →
  α⇒ {Y} {B} {Q} ∘ (id {Y ⊗₀ B} ⊗₁ k)
    ≈ (id {Y} ⊗₁ (id {B} ⊗₁ k)) ∘ α⇒ {Y} {B} {P}
α-sweep {Y} {B} {k = k} =
  ⟺ (refl⟩∘⟨ (id⊗id ⟩⊗⟨refl))
  ○ assoc-commute-from

α⊗id-cancel : ∀ {A B C Z} →
  (α⇒ {A} {B} {C} ⊗₁ id {Z}) ∘ (α⇐ {A} {B} {C} ⊗₁ id {Z}) ≈ id
α⊗id-cancel = ⊗-cancel associator.isoʳ identity²

assoc-pair-coherence : ∀ {A B C D E} →
    α⇒ {A} {B ⊗₀ C} {D ⊗₀ E}
      ∘ (α⇒ {A} {B} {C} ⊗₁ id {D ⊗₀ E})
      ∘ α⇒ {(A ⊗₀ B) ⊗₀ C} {D} {E}
  ≈ (id {A} ⊗₁ α⇐ {B} {C} {D ⊗₀ E})
      ∘ α⇒ {A} {B} {C ⊗₀ (D ⊗₀ E)}
      ∘ (id {A ⊗₀ B} ⊗₁ α⇒ {C} {D} {E})
      ∘ α⇒ {A ⊗₀ B} {C ⊗₀ D} {E}
      ∘ (α⇒ {A ⊗₀ B} {C} {D} ⊗₁ id {E})
assoc-pair-coherence {A} {B} {C} {D} {E} =
  solve ((((x0 ⊗o x1) ⊗o x2) ⊗o x3) ⊗o x4)
        (fα⇒ ∘f (fα⇒ ⊗f idₘ) ∘f fα⇒)
        ((idₘ ⊗f fα⇐) ∘f fα⇒ ∘f (idₘ ⊗f fα⇒) ∘f fα⇒ ∘f (fα⇒ ⊗f idₘ))
  where open Solver A B C D E

assoc-to-coherence : ∀ {A B C D} →
  (id {A} ⊗₁ α⇐ {B} {C} {D})
    ∘ α⇒ {A} {B} {C ⊗₀ D}
  ≈ α⇒ {A} {B ⊗₀ C} {D}
      ∘ (α⇒ {A} {B} {C} ⊗₁ id {D})
      ∘ α⇐ {A ⊗₀ B} {C} {D}
assoc-to-coherence {A} {B} {C} {D} =
  solve ((x0 ⊗o x1) ⊗o (x2 ⊗o x3))
        ((idₘ ⊗f fα⇐) ∘f fα⇒)
        (fα⇒ ∘f (fα⇒ ⊗f idₘ) ∘f fα⇐)
  where open Solver A B C D unit

-- A second inverse-pentagon rearrangement (distinct associator pattern from
-- `assoc-to-coherence`): peels an `α⇐`-whisker off the left of a nested pair.
pentagon′ : ∀ {A B C D} →
    α⇒ {A ⊗₀ B} {C} {D}
      ∘ (α⇐ {A} {B} {C} ⊗₁ id {D})
  ≈ α⇐ {A} {B} {C ⊗₀ D}
      ∘ (id {A} ⊗₁ α⇒ {B} {C} {D})
      ∘ α⇒ {A} {B ⊗₀ C} {D}
pentagon′ {A} {B} {C} {D} =
  solve ((x0 ⊗o (x1 ⊗o x2)) ⊗o x3)
        (fα⇒ ∘f (fα⇐ ⊗f idₘ))
        (fα⇐ ∘f (idₘ ⊗f fα⇒) ∘f fα⇒)
  where open Solver A B C D unit

α-peel⊗id : ∀ {A X Y Z W} →
  (id {A} ⊗₁ (α⇒ {X} {Y} {Z} ⊗₁ id {W}))
    ∘ α⇒ {A} {(X ⊗₀ Y) ⊗₀ Z} {W}
    ∘ (α⇒ {A} {X ⊗₀ Y} {Z} ⊗₁ id {W})
  ≈ α⇒ {A} {X ⊗₀ (Y ⊗₀ Z)} {W}
      ∘ (α⇒ {A} {X} {Y ⊗₀ Z} ⊗₁ id {W})
      ∘ (α⇒ {A ⊗₀ X} {Y} {Z} ⊗₁ id {W})
      ∘ ((α⇐ {A} {X} {Y} ⊗₁ id {Z}) ⊗₁ id {W})
α-peel⊗id {A} {X} {Y} {Z} {W} =
  solve (((x0 ⊗o (x1 ⊗o x2)) ⊗o x3) ⊗o x4)
        ((idₘ ⊗f (fα⇒ ⊗f idₘ)) ∘f fα⇒ ∘f (fα⇒ ⊗f idₘ))
        (fα⇒ ∘f (fα⇒ ⊗f idₘ) ∘f (fα⇒ ⊗f idₘ) ∘f ((fα⇐ ⊗f idₘ) ⊗f idₘ))
  where open Solver A X Y Z W

α-inner : ∀ {A X P Q Z} {h : P ⇒ Q} →
  (id {A} ⊗₁ ((id {X} ⊗₁ h) ⊗₁ id {Z}))
    ∘ α⇒ {A} {X ⊗₀ P} {Z}
    ∘ (α⇒ {A} {X} {P} ⊗₁ id {Z})
  ≈ α⇒ {A} {X ⊗₀ Q} {Z}
      ∘ (α⇒ {A} {X} {Q} ⊗₁ id {Z})
      ∘ ((id {A ⊗₀ X} ⊗₁ h) ⊗₁ id {Z})
α-inner {A} {X} {P} {Q} {Z} {h} =
  (pullˡ α-slide ○ assoc)
  ○ refl⟩∘⟨ slide
  where
    slide :
      ((id {A} ⊗₁ (id {X} ⊗₁ h)) ⊗₁ id {Z}) ∘ (α⇒ {A} {X} {P} ⊗₁ id {Z})
      ≈ (α⇒ {A} {X} {Q} ⊗₁ id {Z})      ∘ ((id {A ⊗₀ X} ⊗₁ h) ⊗₁ id {Z})
    slide = ⊗id-∘
            ○ (⟺ assoc-commute-from) ⟩⊗⟨refl
            ○ (refl⟩∘⟨ (id⊗id ⟩⊗⟨refl)) ⟩⊗⟨refl
            ○ ⟺ (⊗id-∘)

ρ-peel : ∀ {A X Z} →
  (id {A} ⊗₁ (ρ⇒ {X} ⊗₁ id {Z}))
    ∘ α⇒ {A} {X ⊗₀ unit} {Z}
    ∘ (α⇒ {A} {X} {unit} ⊗₁ id {Z})
  ≈ α⇒ {A} {X} {Z} ∘ (ρ⇒ {A ⊗₀ X} ⊗₁ id {Z})
ρ-peel {A} {X} {Z} =
  solve (((x0 ⊗o x1) ⊗o I) ⊗o x2)
        ((idₘ ⊗f (fρ⇒ ⊗f idₘ)) ∘f fα⇒ ∘f (fα⇒ ⊗f idₘ))
        (fα⇒ ∘f (fρ⇒ ⊗f idₘ))
  where open Solver A X Z unit unit

λ-left : ∀ {P Q} →
  α⇒ {unit} {P} {Q} ∘ (λ⇐ ⊗₁ id {Q})
    ≈ λ⇐ {P ⊗₀ Q}
λ-left {P} {Q} =
  solve (x0 ⊗o x1)
        (fα⇒ ∘f (fλ⇐ ⊗f idₘ)) fλ⇐
  where open Solver P Q unit unit unit

-- The triangle identity in inverse form: reassociating onto an appended unit
-- is the left-unitor insertion.
triangle-inv : ∀ {A Z} →
  α⇒ {A} {unit} {Z} ∘ (ρ⇐ {A} ⊗₁ id {Z})
    ≈ id {A} ⊗₁ λ⇐ {Z}
triangle-inv {A} {Z} =
  solve (x0 ⊗o x1)
        (fα⇒ ∘f (fρ⇐ ⊗f idₘ))
        (idₘ ⊗f fλ⇐)
  where open Solver A Z unit unit unit

ρ-sweep : ∀ {X Y L} {h : L ⇒ unit} →
  ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ h) ∘ α⇐ {X} {Y} {L}
    ≈ id {X} ⊗₁ (ρ⇒ ∘ (id {Y} ⊗₁ h))
ρ-sweep {X} {Y} {L} {h} =
  refl⟩∘⟨ ρ-nat
  ○ pullˡ ρ-coh
  ○ merge₂ˡ
  where
    ρ-nat :
      (id {X ⊗₀ Y} ⊗₁ h) ∘ α⇐ {X} {Y} {L}
      ≈ α⇐ {X} {Y} {unit} ∘ (id {X} ⊗₁ (id {Y} ⊗₁ h))
    ρ-nat =
      ((⟺ id⊗id) ⟩⊗⟨refl) ⟩∘⟨refl
      ○ ⟺ (assoc-commute-to {f = id {X}} {g = id {Y}} {h = h})

    ρ-coh :
      ρ⇒ ∘ α⇐ {X} {Y} {unit}
      ≈ id {X} ⊗₁ ρ⇒
    ρ-coh = ⟺ (switch-fromtoʳ associator coherence₂)

ρ-sweep-open : ∀ {X Y L} {h : L ⇒ unit} →
  (id {X} ⊗₁ (ρ⇒ ∘ (id {Y} ⊗₁ h)))
    ∘ α⇒ {X} {Y} {L}
  ≈ ρ⇒ ∘ (id {X ⊗₀ Y} ⊗₁ h)
ρ-sweep-open {X} {Y} {L} {h} =
  ⟺ (ρ-sweep {X} {Y} {L} {h} ⟩∘⟨refl)
  ○ assoc²βε
  ○ refl⟩∘⟨ refl⟩∘⟨ associator.isoˡ
  ○ refl⟩∘⟨ identityʳ

cap-reassoc : ∀ {A P Q B} {cap : P ⊗₀ Q ⇒ unit} →
  (id {A} ⊗₁ (λ⇒ ∘ (cap ⊗₁ id {B}) ∘ α⇐))
    ∘ α⇒ {A} {P} {Q ⊗₀ B}
  ≈ ((ρ⇒ ⊗₁ id {B}) ∘ ((id {A} ⊗₁ cap) ⊗₁ id {B}))
      ∘ (α⇒ {A} {P} {Q} ⊗₁ id {B})
      ∘ α⇐ {A ⊗₀ P} {Q} {B}
cap-reassoc {A} {P} {Q} {B} {cap} =
  ((split₂ˡ ○ (refl⟩∘⟨ split₂ˡ)) ⟩∘⟨refl)
  ○ (assoc ○ (refl⟩∘⟨ assoc))
  ○ refl⟩∘⟨ refl⟩∘⟨ assoc-to-coherence
  ○ (refl⟩∘⟨ (sym-assoc ○ (⟺ assoc-commute-from ⟩∘⟨refl) ○ assoc))
  ○ ⟺ (assoc)
  ○ triangle ⟩∘⟨refl
  ○ ⟺ (assoc)

α-unit : ∀ {A B Z} →
  α⇒ {A} {B} {unit ⊗₀ Z}
    ∘ α⇒ {A ⊗₀ B} {unit} {Z}
    ∘ (ρ⇐ ⊗₁ id {Z})
    ∘ α⇐ {A} {B} {Z}
  ≈ id {A} ⊗₁ (id {B} ⊗₁ λ⇐ {Z})
α-unit {A} {B} {Z} =
  solve (x0 ⊗o (x1 ⊗o x2))
        (fα⇒ ∘f fα⇒ ∘f (fρ⇐ ⊗f idₘ) ∘f fα⇐)
        (idₘ ⊗f (idₘ ⊗f fλ⇐))
  where open Solver A B Z unit unit
