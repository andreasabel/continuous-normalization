{-# OPTIONS --copatterns --sized-types #-}
-- {-# OPTIONS -v tc.conv:10 -v tc.conv.size:15 #-}
module Delay where

open import Level renaming (zero to lzero; suc to lsuc)
open import Size

open import Category.Monad

mutual

  data Delay (A : Set) (i : Size) : Set where
    now   : A → Delay A i
    later : ∞Delay A i → Delay A i

  record ∞Delay (A : Set) (i : Size) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay A j

open ∞Delay

-- Smart constructor.

later! : ∀ {A i} → Delay A i → Delay A (↑ i)
later! x = later (delay x)

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

















{-
mutual

  cast : ∀ {A i} → Delay A i → (j : Size< ↑ i) → Delay A j
  cast (now x) j = now x
  cast (later x) j = {!later (∞cast x j)!}

  ∞cast : ∀ {A i} → ∞Delay A i → (j : Size< ↑ i) → ∞Delay A j
  ♭ (∞cast x j) {k} = cast {i = j} (♭ x) k
-}
