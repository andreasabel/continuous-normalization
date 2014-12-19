{-# OPTIONS --copatterns #-}

module WeakBisim where

open import Library
open import Delay

-- Weak bisimilarity.
------------------------------------------------------------------------

mutual
  data Delay_∋_~_ {i : Size} {A : Set} (R : A → A → Set) : (a? b? : Delay ∞ A) → Set where
    ~now   : ∀ {a b a? b?} → a? ⇓ a → b? ⇓ b → R a b → Delay R ∋ a? ~ b?
    ~later : ∀ {a∞ b∞} (eq : ∞Delay R ∋ a∞ ~⟨ i ⟩~ b∞) → Delay R ∋ later a∞ ~ later b∞

  Delay_∋_~⟨_⟩~_ = λ {A} R a? i b? → Delay_∋_~_ {i}{A} R a? b?

  record ∞Delay_∋_~⟨_⟩~_ {A} (R : A → A → Set) (a∞ : ∞Delay ∞ A) i (b∞ : ∞Delay ∞ A) : Set where
    coinductive
    constructor ~delay
    field
      ~force : {j : Size< i} → Delay R ∋ force a∞ ~⟨ j ⟩~ force b∞

∞Delay_∋_~_ = λ {i} {A} R a∞ b∞ → ∞Delay_∋_~⟨_⟩~_ {A} R a∞ i b∞

-- Instantiation of R to propositional equality.

_~⟨_⟩~_ = λ {A} a i b → Delay_∋_~⟨_⟩~_ {A} _≡_ a i b
_~_ = λ {i} {A} a b → _~⟨_⟩~_ {A} a i b

_∞~⟨_⟩~_ = λ {A} a∞ i b∞ → ∞Delay_∋_~⟨_⟩~_ {A} _≡_ a∞ i b∞
_∞~_ = λ {i} {A} a∞ b∞ → _∞~⟨_⟩~_ {A} a∞ i b∞

open ∞Delay_∋_~⟨_⟩~_ public

-- Strong bisimilarity implies weak bisimilarity.

mutual
  ≈→~ : ∀{i A}{a? b? : Delay ∞ A} → a? ≈⟨ i ⟩≈ b? → a? ~⟨ i ⟩~ b?
  ≈→~ (≈now a)    = ~now now⇓ now⇓ refl
  ≈→~ (≈later eq) = ~later (∞≈→~ eq)

  ∞≈→~ : ∀{i A}{a∞ b∞ : ∞Delay ∞ A} → a∞ ∞≈⟨ i ⟩≈ b∞ → a∞ ∞~⟨ i ⟩~ b∞
  ~force (∞≈→~ eq) = ≈→~ (≈force eq)
