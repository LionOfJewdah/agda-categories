{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Monoidal expressions with opaque morphism leaves.
--
-- This module is intentionally conservative: opaque leaves carry no equations.
-- The solver API only accounts for category laws, functoriality of tensor, and
-- naturality of the monoidal structure.  Domain-specific laws such as snake
-- identities must still be supplied explicitly by the caller.
--------------------------------------------------------------------------------

module Categories.Tactic.Monoidal.Expression where

open import Function using (_⟨_⟩_)
open import Level using (Level; _⊔_)

open import Data.Bool using (Bool; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Agda.Builtin.Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term using (getName; _⋯⟅∷⟆_)
open import Reflection.TCM.Syntax

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
import Categories.Category.Monoidal.Symmetric.Properties as SymmetricProperties

private
  _==_ : Name → Name → Bool
  _==_ = primQNameEquality
  {-# INLINE _==_ #-}

module Core
  {o ℓ e : Level}
  {C : Category o ℓ e}
  (M : Monoidal C)
  where

  open Category C
  open Monoidal M
  open import Categories.Category.Monoidal.Reasoning M
  import Categories.Category.Monoidal.Utilities M as MonUtil
  open MonUtil.Shorthands using (α⇒; α⇐; λ⇒; λ⇐; ρ⇒; ρ⇐)

  private
    variable
      A B C′ D E F G H : Obj

  infixr 9 _∘ₑ_
  infixr 10 _⊗ₑ_
  infix 4 _≈ₑ_
  infixr 2 _○ₑ_

  data Expr : Obj → Obj → Set (o ⊔ ℓ) where
    idₑ  : Expr A A
    _∘ₑ_ : Expr B C′ → Expr A B → Expr A C′
    _⊗ₑ_ : Expr A B → Expr C′ D → Expr (A ⊗₀ C′) (B ⊗₀ D)
    α⇒ₑ  : Expr ((A ⊗₀ B) ⊗₀ C′) (A ⊗₀ (B ⊗₀ C′))
    α⇐ₑ  : Expr (A ⊗₀ (B ⊗₀ C′)) ((A ⊗₀ B) ⊗₀ C′)
    λ⇒ₑ  : Expr (unit ⊗₀ A) A
    λ⇐ₑ  : Expr A (unit ⊗₀ A)
    ρ⇒ₑ  : Expr (A ⊗₀ unit) A
    ρ⇐ₑ  : Expr A (A ⊗₀ unit)
    [_↑] : A ⇒ B → Expr A B

  ⟦_⟧ₑ : Expr A B → A ⇒ B
  ⟦ idₑ ⟧ₑ    = id
  ⟦ g ∘ₑ f ⟧ₑ = ⟦ g ⟧ₑ ∘ ⟦ f ⟧ₑ
  ⟦ f ⊗ₑ g ⟧ₑ = ⟦ f ⟧ₑ ⊗₁ ⟦ g ⟧ₑ
  ⟦ α⇒ₑ ⟧ₑ    = α⇒
  ⟦ α⇐ₑ ⟧ₑ    = α⇐
  ⟦ λ⇒ₑ ⟧ₑ    = λ⇒
  ⟦ λ⇐ₑ ⟧ₑ    = λ⇐
  ⟦ ρ⇒ₑ ⟧ₑ    = ρ⇒
  ⟦ ρ⇐ₑ ⟧ₑ    = ρ⇐
  ⟦ [ f ↑] ⟧ₑ = f

  -- Category-normal form used by the reflection macro. Tensor nodes are
  -- traversed recursively, while structural nodes remain opaque leaves here;
  -- monoidal laws are exposed by `_≈ₑ_` below.
  embed : Expr B C′ → A ⇒ B → A ⇒ C′
  embed (g ∘ₑ f) h = embed g (embed f h)
  embed idₑ      h = h
  embed (f ⊗ₑ g) h = (embed f id ⊗₁ embed g id) ∘ h
  embed f        h = ⟦ f ⟧ₑ ∘ h

  embed-≈′ : (f : Expr B C′) (h : A ⇒ B) → embed f id ∘ h ≈ embed f h
  embed-≈′ idₑ      h = identityˡ
  embed-≈′ [ f ↑]   h = ∘-resp-≈ˡ identityʳ
  embed-≈′ α⇒ₑ      h = ∘-resp-≈ˡ identityʳ
  embed-≈′ α⇐ₑ      h = ∘-resp-≈ˡ identityʳ
  embed-≈′ λ⇒ₑ      h = ∘-resp-≈ˡ identityʳ
  embed-≈′ λ⇐ₑ      h = ∘-resp-≈ˡ identityʳ
  embed-≈′ ρ⇒ₑ      h = ∘-resp-≈ˡ identityʳ
  embed-≈′ ρ⇐ₑ      h = ∘-resp-≈ˡ identityʳ
  embed-≈′ (f ⊗ₑ g) h = ∘-resp-≈ˡ identityʳ
  embed-≈′ (g ∘ₑ f) h = begin
    embed (g ∘ₑ f) id ∘ h             ≈˘⟨ embed-≈′ g (embed f id) ⟩∘⟨refl ⟩
    (embed g id ∘ embed f id) ∘ h     ≈⟨ assoc ⟩
    embed g id ∘ embed f id ∘ h       ≈⟨ refl⟩∘⟨ embed-≈′ f h ⟩
    embed g id ∘ embed f h            ≈⟨ embed-≈′ g (embed f h) ⟩
    embed (g ∘ₑ f) h                  ∎

  embed-≈ : (f : Expr A B) → embed f id ≈ ⟦ f ⟧ₑ
  embed-≈ idₑ      = Equiv.refl
  embed-≈ [ f ↑]   = identityʳ
  embed-≈ α⇒ₑ      = identityʳ
  embed-≈ α⇐ₑ      = identityʳ
  embed-≈ λ⇒ₑ      = identityʳ
  embed-≈ λ⇐ₑ      = identityʳ
  embed-≈ ρ⇒ₑ      = identityʳ
  embed-≈ ρ⇐ₑ      = identityʳ
  embed-≈ (f ⊗ₑ g) = identityʳ ○ (embed-≈ f ⟩⊗⟨ embed-≈ g)
  embed-≈ (g ∘ₑ f) = begin
    embed g (embed f id)       ≈˘⟨ embed-≈′ g (embed f id) ⟩
    embed g id ∘ embed f id    ≈⟨ embed-≈ g ⟩∘⟨ embed-≈ f ⟩
    ⟦ g ⟧ₑ ∘ ⟦ f ⟧ₑ            ∎

  normal : Expr A B → A ⇒ B
  normal f = embed f id

  normal-sound : (f : Expr A B) → normal f ≈ ⟦ f ⟧ₑ
  normal-sound = embed-≈

  data _≈ₑ_ : Expr A B → Expr A B → Set (o ⊔ ℓ ⊔ e) where
    reflₑ  : ∀ {f : Expr A B} → f ≈ₑ f
    symₑ   : ∀ {f g : Expr A B} → f ≈ₑ g → g ≈ₑ f
    transₑ : ∀ {f g h : Expr A B} → f ≈ₑ g → g ≈ₑ h → f ≈ₑ h
    leaf-≈ₑ : ∀ {f g : A ⇒ B} → f ≈ g → [ f ↑] ≈ₑ [ g ↑]

    _⟩∘ₑ⟨_ : ∀ {f h : Expr B C′} {g i : Expr A B}
      → f ≈ₑ h → g ≈ₑ i → (f ∘ₑ g) ≈ₑ (h ∘ₑ i)
    _⟩⊗ₑ⟨_ : ∀ {f h : Expr A B} {g i : Expr C′ D}
      → f ≈ₑ h → g ≈ₑ i → (f ⊗ₑ g) ≈ₑ (h ⊗ₑ i)

    assocₑ : ∀ {f : Expr C′ D} {g : Expr B C′} {h : Expr A B}
      → ((f ∘ₑ g) ∘ₑ h) ≈ₑ (f ∘ₑ (g ∘ₑ h))
    identityˡₑ : ∀ {f : Expr A B} → (idₑ ∘ₑ f) ≈ₑ f
    identityʳₑ : ∀ {f : Expr A B} → (f ∘ₑ idₑ) ≈ₑ f
    ⊗-identityₑ : (idₑ {A = A} ⊗ₑ idₑ {A = B}) ≈ₑ idₑ

    ⊗-distribₑ :
      ∀ {f : Expr B C′} {g : Expr A B} {h : Expr E F} {i : Expr D E} →
      ((f ∘ₑ g) ⊗ₑ (h ∘ₑ i)) ≈ₑ ((f ⊗ₑ h) ∘ₑ (g ⊗ₑ i))
    α⇒-naturalₑ :
      ∀ {f : Expr A B} {g : Expr C′ D} {h : Expr E F} →
      (α⇒ₑ ∘ₑ ((f ⊗ₑ g) ⊗ₑ h)) ≈ₑ ((f ⊗ₑ (g ⊗ₑ h)) ∘ₑ α⇒ₑ)
    α⇐-naturalₑ :
      ∀ {f : Expr A B} {g : Expr C′ D} {h : Expr E F} →
      (α⇐ₑ ∘ₑ (f ⊗ₑ (g ⊗ₑ h))) ≈ₑ (((f ⊗ₑ g) ⊗ₑ h) ∘ₑ α⇐ₑ)
    λ⇒-naturalₑ :
      ∀ {f : Expr A B} → (λ⇒ₑ ∘ₑ (idₑ ⊗ₑ f)) ≈ₑ (f ∘ₑ λ⇒ₑ)
    λ⇐-naturalₑ :
      ∀ {f : Expr A B} → ((idₑ ⊗ₑ f) ∘ₑ λ⇐ₑ) ≈ₑ (λ⇐ₑ ∘ₑ f)
    ρ⇒-naturalₑ :
      ∀ {f : Expr A B} → (ρ⇒ₑ ∘ₑ (f ⊗ₑ idₑ)) ≈ₑ (f ∘ₑ ρ⇒ₑ)
    ρ⇐-naturalₑ :
      ∀ {f : Expr A B} → ((f ⊗ₑ idₑ) ∘ₑ ρ⇐ₑ) ≈ₑ (ρ⇐ₑ ∘ₑ f)

    split₁ʳₑ :
      ∀ {f : Expr B C′} {g : Expr A B} {h : Expr D E} →
      ((f ∘ₑ g) ⊗ₑ h) ≈ₑ ((f ⊗ₑ h) ∘ₑ (g ⊗ₑ idₑ))
    split₁ˡₑ :
      ∀ {f : Expr B C′} {g : Expr A B} {h : Expr D E} →
      ((f ∘ₑ g) ⊗ₑ h) ≈ₑ ((f ⊗ₑ idₑ) ∘ₑ (g ⊗ₑ h))
    split₂ʳₑ :
      ∀ {f : Expr A B} {g : Expr E F} {h : Expr D E} →
      (f ⊗ₑ (g ∘ₑ h)) ≈ₑ ((f ⊗ₑ g) ∘ₑ (idₑ ⊗ₑ h))
    split₂ˡₑ :
      ∀ {f : Expr A B} {g : Expr E F} {h : Expr D E} →
      (f ⊗ₑ (g ∘ₑ h)) ≈ₑ ((idₑ ⊗ₑ g) ∘ₑ (f ⊗ₑ h))
    merge₁ʳₑ :
      ∀ {f : Expr B C′} {g : Expr A B} {h : Expr D E} →
      ((f ⊗ₑ h) ∘ₑ (g ⊗ₑ idₑ)) ≈ₑ ((f ∘ₑ g) ⊗ₑ h)
    merge₁ˡₑ :
      ∀ {f : Expr B C′} {g : Expr A B} {h : Expr D E} →
      ((f ⊗ₑ idₑ) ∘ₑ (g ⊗ₑ h)) ≈ₑ ((f ∘ₑ g) ⊗ₑ h)
    merge₂ʳₑ :
      ∀ {f : Expr A B} {g : Expr E F} {h : Expr D E} →
      ((f ⊗ₑ g) ∘ₑ (idₑ ⊗ₑ h)) ≈ₑ (f ⊗ₑ (g ∘ₑ h))
    merge₂ˡₑ :
      ∀ {f : Expr A B} {g : Expr E F} {h : Expr D E} →
      ((idₑ ⊗ₑ g) ∘ₑ (f ⊗ₑ h)) ≈ₑ (f ⊗ₑ (g ∘ₑ h))
    commute₂₁ₑ :
      ∀ {f : Expr A B} {g : Expr C′ D} →
      ((idₑ ⊗ₑ g) ∘ₑ (f ⊗ₑ idₑ)) ≈ₑ ((f ⊗ₑ idₑ) ∘ₑ (idₑ ⊗ₑ g))
    commute₁₂ₑ :
      ∀ {f : Expr A B} {g : Expr C′ D} →
      ((f ⊗ₑ idₑ) ∘ₑ (idₑ ⊗ₑ g)) ≈ₑ ((idₑ ⊗ₑ g) ∘ₑ (f ⊗ₑ idₑ))

  solveₑ : ∀ {f g : Expr A B} → f ≈ₑ g → ⟦ f ⟧ₑ ≈ ⟦ g ⟧ₑ
  solveₑ reflₑ              = Equiv.refl
  solveₑ (symₑ p)           = Equiv.sym (solveₑ p)
  solveₑ (transₑ p q)       = Equiv.trans (solveₑ p) (solveₑ q)
  solveₑ (leaf-≈ₑ p)        = p
  solveₑ (p ⟩∘ₑ⟨ q)         = solveₑ p ⟩∘⟨ solveₑ q
  solveₑ (p ⟩⊗ₑ⟨ q)         = solveₑ p ⟩⊗⟨ solveₑ q
  solveₑ assocₑ             = assoc
  solveₑ identityˡₑ         = identityˡ
  solveₑ identityʳₑ         = identityʳ
  solveₑ ⊗-identityₑ        = ⊗.identity
  solveₑ ⊗-distribₑ         = ⊗-distrib-over-∘
  solveₑ α⇒-naturalₑ        = assoc-commute-from
  solveₑ α⇐-naturalₑ        = assoc-commute-to
  solveₑ λ⇒-naturalₑ        = unitorˡ-commute-from
  solveₑ λ⇐-naturalₑ        = Equiv.sym unitorˡ-commute-to
  solveₑ ρ⇒-naturalₑ        = unitorʳ-commute-from
  solveₑ ρ⇐-naturalₑ        = Equiv.sym unitorʳ-commute-to
  solveₑ split₁ʳₑ           = split₁ʳ
  solveₑ split₁ˡₑ           = split₁ˡ
  solveₑ split₂ʳₑ           = split₂ʳ
  solveₑ split₂ˡₑ           = split₂ˡ
  solveₑ merge₁ʳₑ           = merge₁ʳ
  solveₑ merge₁ˡₑ           = merge₁ˡ
  solveₑ merge₂ʳₑ           = merge₂ʳ
  solveₑ merge₂ˡₑ           = merge₂ˡ
  solveₑ commute₂₁ₑ         = Equiv.sym serialize₂₁ ○ serialize₁₂
  solveₑ commute₁₂ₑ         = Equiv.sym serialize₁₂ ○ serialize₂₁

  _○ₑ_ : ∀ {f g h : Expr A B} → f ≈ₑ g → g ≈ₑ h → f ≈ₑ h
  _○ₑ_ = transₑ

  ⟺ₑ : ∀ {f g : Expr A B} → f ≈ₑ g → g ≈ₑ f
  ⟺ₑ = symₑ

  module BraidedExpression (Br : Braided M) where
    open Braided Br using (braiding; hexagon₁)
    open BraidedProperties Br
      using
        ( braiding-coherence
        ; braiding-coherence-inv
        ; braiding-coherenceʳ-inv
        ; inv-braiding-coherence
        )

    σ⇒ₑ : ∀ {A B} → Expr (A ⊗₀ B) (B ⊗₀ A)
    σ⇒ₑ = [ braiding.⇒.η (_ , _) ↑]

    σ⇐ₑ : ∀ {A B} → Expr (B ⊗₀ A) (A ⊗₀ B)
    σ⇐ₑ = [ braiding.⇐.η (_ , _) ↑]

    σₑ : ∀ {A B} → Expr (A ⊗₀ B) (B ⊗₀ A)
    σₑ = σ⇒ₑ

    σ⇒-natural : ∀ {f : Expr A B} {g : Expr C′ D} →
      ⟦ σ⇒ₑ ∘ₑ (f ⊗ₑ g) ⟧ₑ ≈ ⟦ (g ⊗ₑ f) ∘ₑ σ⇒ₑ ⟧ₑ
    σ⇒-natural = braiding.⇒.commute (_ , _)

    σ⇐-natural : ∀ {f : Expr A B} {g : Expr C′ D} →
      ⟦ σ⇐ₑ ∘ₑ (g ⊗ₑ f) ⟧ₑ ≈ ⟦ (f ⊗ₑ g) ∘ₑ σ⇐ₑ ⟧ₑ
    σ⇐-natural = braiding.⇐.commute (_ , _)

    σ⇐∘σ⇒ : ⟦ σ⇐ₑ {A = A} {B = B} ∘ₑ σ⇒ₑ {A = A} {B = B} ⟧ₑ ≈ ⟦ idₑ {A = A ⊗₀ B} ⟧ₑ
    σ⇐∘σ⇒ = braiding.iso.isoˡ (_ , _)

    σ⇒∘σ⇐ : ⟦ σ⇒ₑ {A = A} {B = B} ∘ₑ σ⇐ₑ {A = A} {B = B} ⟧ₑ ≈ ⟦ idₑ {A = B ⊗₀ A} ⟧ₑ
    σ⇒∘σ⇐ = braiding.iso.isoʳ (_ , _)

    σ-natural : ∀ {f : Expr A B} {g : Expr C′ D} →
      ⟦ σₑ ∘ₑ (f ⊗ₑ g) ⟧ₑ ≈ ⟦ (g ⊗ₑ f) ∘ₑ σₑ ⟧ₑ
    σ-natural = braiding.⇒.commute (_ , _)

    σ⇒-hexagon₁ :
      ⟦ (idₑ {A = B} ⊗ₑ σ⇒ₑ {A = A} {B = C′})
          ∘ₑ α⇒ₑ {A = B} {B = A} {C′ = C′}
          ∘ₑ (σ⇒ₑ {A = A} {B = B} ⊗ₑ idₑ {A = C′}) ⟧ₑ
      ≈ ⟦ α⇒ₑ {A = B} {B = C′} {C′ = A}
          ∘ₑ σ⇒ₑ {A = A} {B = B ⊗₀ C′}
          ∘ₑ α⇒ₑ {A = A} {B = B} {C′ = C′} ⟧ₑ
    σ⇒-hexagon₁ = hexagon₁

    σ⇒-unitʳ : ⟦ λ⇒ₑ {A = A} ∘ₑ σ⇒ₑ {A = A} {B = unit} ⟧ₑ ≈ ⟦ ρ⇒ₑ {A = A} ⟧ₑ
    σ⇒-unitʳ = braiding-coherence

    σ⇒-unitʳ-inv : ⟦ σ⇒ₑ {A = A} {B = unit} ∘ₑ ρ⇐ₑ {A = A} ⟧ₑ ≈ ⟦ λ⇐ₑ {A = A} ⟧ₑ
    σ⇒-unitʳ-inv = braiding-coherenceʳ-inv

    σ⇐-unitʳ-inv : ⟦ σ⇐ₑ {A = A} {B = unit} ∘ₑ λ⇐ₑ {A = A} ⟧ₑ ≈ ⟦ ρ⇐ₑ {A = A} ⟧ₑ
    σ⇐-unitʳ-inv = braiding-coherence-inv

    σ⇐-unitˡ : ⟦ ρ⇒ₑ {A = A} ∘ₑ σ⇐ₑ {A = A} {B = unit} ⟧ₑ ≈ ⟦ λ⇒ₑ {A = A} ⟧ₑ
    σ⇐-unitˡ = inv-braiding-coherence

  module SymmetricExpression (S : Symmetric M) where
    open Symmetric S using (braided; commutative)
    open BraidedExpression braided public
    open SymmetricProperties S using (braiding-selfInverse)

    σ⇐≈σ⇒ : ⟦ σ⇐ₑ {A = A} {B = B} ⟧ₑ ≈ ⟦ σ⇒ₑ {A = B} {B = A} ⟧ₑ
    σ⇐≈σ⇒ = braiding-selfInverse

    σ² : ⟦ σ⇒ₑ {A = B} {B = A} ∘ₑ σ⇒ₑ {A = A} {B = B} ⟧ₑ ≈ ⟦ idₑ {A = A ⊗₀ B} ⟧ₑ
    σ² = commutative

private
  getArgs′ : List (Arg Term) → Maybe (Term × Term)
  getArgs′ (vArg x ∷ vArg y ∷ []) = just (x , y)
  getArgs′ (_ ∷ xs)               = getArgs′ xs
  getArgs′ _                      = nothing

  getArgs : Term → Maybe (Term × Term)
  getArgs (def _ xs) = getArgs′ xs
  getArgs _          = nothing

  record CategoryNames : Set where
    field
      is-∘  : Name → Bool
      is-id : Name → Bool

  build-matcher : Name → Maybe Name → Name → Bool
  build-matcher n nothing  x = n == x
  build-matcher n (just m) x = n == x ∨ m == x

  find-category-names : Term → TC CategoryNames
  find-category-names cat = do
    ∘-altName ← normalise (def (quote Category._∘_) (3 ⋯⟅∷⟆ cat ⟨∷⟩ []))
    id-altName ← normalise (def (quote Category.id) (3 ⋯⟅∷⟆ cat ⟨∷⟩ []))
    returnTC record
      { is-∘  = build-matcher (quote Category._∘_) (getName ∘-altName)
      ; is-id = build-matcher (quote Category.id) (getName id-altName)
      }

  is-⊗ : Name → Bool
  is-⊗ n = n == quote Monoidal._⊗₁_

  ″idₑ″ : Term
  ″idₑ″ = quote Core.idₑ ⟨ con ⟩ []

  quote-leaf : Term → Term
  quote-leaf t = quote Core.[_↑] ⟨ con ⟩ t ⟨∷⟩ []

  module _ (names : CategoryNames) where
    open CategoryNames names

    mutual
      ″∘ₑ″ : List (Arg Term) → Term
      ″∘ₑ″ (x ⟨∷⟩ y ⟨∷⟩ xs) =
        quote Core._∘ₑ_ ⟨ con ⟩ build-expr x ⟨∷⟩ build-expr y ⟨∷⟩ []
      ″∘ₑ″ (x ∷ xs) = ″∘ₑ″ xs
      ″∘ₑ″ _        = unknown

      ″⊗ₑ″ : List (Arg Term) → Term
      ″⊗ₑ″ (x ⟨∷⟩ y ⟨∷⟩ xs) =
        quote Core._⊗ₑ_ ⟨ con ⟩ build-expr x ⟨∷⟩ build-expr y ⟨∷⟩ []
      ″⊗ₑ″ (x ∷ xs) = ″⊗ₑ″ xs
      ″⊗ₑ″ _        = unknown

      build-expr : Term → Term
      build-expr t@(def n xs) =
        if (is-∘ n)
          then ″∘ₑ″ xs
          else if (is-id n)
            then ″idₑ″
            else if (is-⊗ n)
              then ″⊗ₑ″ xs
              else quote-leaf t
      build-expr t@(con n xs) =
        if (is-∘ n)
          then ″∘ₑ″ xs
          else if (is-id n)
            then ″idₑ″
            else if (is-⊗ n)
              then ″⊗ₑ″ xs
              else quote-leaf t
      build-expr t = quote-leaf t

  construct-solution : Term → Term → CategoryNames → Term → Term → Term
  construct-solution cat M names lhs rhs =
    quote Category.Equiv.trans ⟨ def ⟩ 3 ⋯⟅∷⟆ cat ⟨∷⟩
      (quote Category.Equiv.sym ⟨ def ⟩ 3 ⋯⟅∷⟆ cat ⟨∷⟩
        (quote Core.embed-≈ ⟨ def ⟩ 4 ⋯⟅∷⟆ M ⟨∷⟩ build-expr names lhs ⟨∷⟩ []) ⟨∷⟩ [])
      ⟨∷⟩
      (quote Core.embed-≈ ⟨ def ⟩ 4 ⋯⟅∷⟆ M ⟨∷⟩ build-expr names rhs ⟨∷⟩ [])
      ⟨∷⟩ []

  solve-macro : Term → Term → Term → TC _
  solve-macro cat M hole = do
    goal ← inferType hole >>= normalise
    names ← find-category-names cat
    just (lhs , rhs) ← returnTC (getArgs goal)
      where nothing → typeError (termErr goal ∷ [])
    unify hole (construct-solution cat M names lhs rhs)

macro
  solveMonoidalExpr : Term → Term → Term → TC _
  solveMonoidalExpr = solve-macro
