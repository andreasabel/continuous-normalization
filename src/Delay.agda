{-# OPTIONS --copatterns --sized-types #-}
-- {-# OPTIONS -v tc.conv:10 -v tc.conv.size:15 #-}
module Delay where

open import Library

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

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i}) public renaming (_⊛_ to _<*>_)

_=<<2_,_ : ∀ {i A B C} → (A → B → Delay C i) → Delay A i → Delay B i → Delay C i
f =<<2 x , y = x >>= λ a → y >>= λ b → f a b

-- Termination.  Makes only sense for Delay A ∞.

data _⇓_ {A : Set} : (a? : Delay A ∞) (a : A) → Set where
  now⇓   : ∀ {a} → now a ⇓ a
  later⇓ : ∀ {a} {a∞ : ∞Delay A ∞} → force a∞ ⇓ a → later a∞ ⇓ a

_⇓ : {A : Set} (x : Delay A ∞) → Set
x ⇓ = ∃ λ a → x ⇓ a

-- Monotonicity.

map⇓ : ∀ {A B} {a : A} {a? : Delay A ∞}
  (f : A → B) (a⇓ : a? ⇓ a) → (f <$> a?) ⇓ f a
map⇓ f now⇓        = now⇓
map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)












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
