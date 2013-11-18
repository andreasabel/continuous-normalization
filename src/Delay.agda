{-# OPTIONS --copatterns --sized-types #-}
-- {-# OPTIONS -v tc.conv:10 -v tc.conv.size:15 #-}
module Delay where

open import Level renaming (zero to lzero; suc to lsuc)
open import Size

open import Category.Monad
open import Data.Product using (∃)

-- Coinductive delay monad.

mutual

  data Delay (A : Set) (i : Size) : Set where
    now   : A → Delay A i
    later : ∞Delay A i → Delay A i

  record ∞Delay (A : Set) (i : Size) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay A j

open ∞Delay public

-- Smart constructor.

later! : ∀ {A i} → Delay A i → Delay A (↑ i)
later! x = later (delay x)

-- Monad instance.

delayMonad : ∀ {i} → RawMonad {f = lzero} (λ A → Delay A i)
delayMonad = record
  { return = now
  ; _>>=_  = _>>=_
  }
  where
    mutual
      _>>=_ : ∀ {A B i} → Delay A i → (A → Delay B i) → Delay B i
      now   x >>= f = f x
      later x >>= f = later (x ∞>>= f)

      _∞>>=_ :  ∀ {A B i} → ∞Delay A i → (A → Delay B i) → ∞Delay B i
      force (x ∞>>= f) = force x >>= f

-- Termination.  Makes only sense for Delay A ∞.

mutual
  _⇓_ : {A : Set} (x : Delay A ∞) (a : A) → Set
  x ⇓ a = Terminates a x

  data Terminates {A : Set} (a : A) : Delay A ∞ → Set where
    now   : now a ⇓ a
    later : ∀ {x : ∞Delay A ∞} → force x ⇓ a → later x ⇓ a

_⇓ : {A : Set} (x : Delay A ∞) → Set
x ⇓ = ∃ λ a → x ⇓ a














{-
mutual
  _⇓_ : {A : Set} {i : Size} (x : Delay A i) (a : A) → Set
  x ⇓ a = Terminates a x

  data Terminates {A : Set} {i : Size} (a : A) : Delay A i → Set where
    now   : now a ⇓ a
    later : ∀ {x : ∞Delay A i} → (force x {j = ?}) ⇓ a → later x ⇓ a

mutual

  cast : ∀ {A i} → Delay A i → (j : Size< ↑ i) → Delay A j
  cast (now x) j = now x
  cast (later x) j = {!later (∞cast x j)!}

  ∞cast : ∀ {A i} → ∞Delay A i → (j : Size< ↑ i) → ∞Delay A j
  ♭ (∞cast x j) {k} = cast {i = j} (♭ x) k
-}
