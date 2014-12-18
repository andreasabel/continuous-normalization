{-# OPTIONS --copatterns #-}

module WeakBisim where

open import Library
open import Delay

-- Weak bisimilarity.
------------------------------------------------------------------------

mutual
  data _~_ {i : Size} {A : Set} : (a? b? : Delay ∞ A) → Set where
    ~now   : ∀ {a a? b?} → a? ⇓ a → b? ⇓ a → a? ~ b?
    ~later : ∀ {a∞ b∞} (eq : a∞ ∞~⟨ i ⟩~ b∞) → later a∞ ~ later b∞

  _~⟨_⟩~_ = λ {A} a? i b? → _~_ {i}{A} a? b?

  record _∞~⟨_⟩~_ {A} (a∞ : ∞Delay ∞ A) i (b∞ : ∞Delay ∞ A) : Set where
    coinductive
    field
      ~force : {j : Size< i} → force a∞ ~⟨ j ⟩~ force b∞

_∞~_ = λ {i} {A} a∞ b∞ → _∞~⟨_⟩~_ {A} a∞ i b∞
open _∞~⟨_⟩~_ public

-- Strong bisimilarity implies weak bisimilarity.

mutual
  ≈→~ : ∀{i A}{a? b? : Delay ∞ A} → a? ≈⟨ i ⟩≈ b? → a? ~⟨ i ⟩~ b?
  ≈→~ (≈now a)    = ~now now⇓ now⇓
  ≈→~ (≈later eq) = ~later (∞≈→~ eq)

  ∞≈→~ : ∀{i A}{a∞ b∞ : ∞Delay ∞ A} → a∞ ∞≈⟨ i ⟩≈ b∞ → a∞ ∞~⟨ i ⟩~ b∞
  ~force (∞≈→~ eq) = ≈→~ (≈force eq)
