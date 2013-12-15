{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --show-implicit #-}
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

module Bind where
  mutual
    _>>=_ : ∀ {i A B} → Delay A i → (A → Delay B i) → Delay B i
    now   x >>= f = f x
    later x >>= f = later (x ∞>>= f)

    _∞>>=_ :  ∀ {i A B} → ∞Delay A i → (A → Delay B i) → ∞Delay B i
    force (x ∞>>= f) = force x >>= f

delayMonad : ∀ {i} → RawMonad {f = lzero} (λ A → Delay A i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i}) public renaming (_⊛_ to _<*>_)
open Bind public using (_∞>>=_)

_=<<2_,_ : ∀ {i A B C} → (A → B → Delay C i) → Delay A i → Delay B i → Delay C i
f =<<2 x , y = x >>= λ a → y >>= λ b → f a b

-- Strong bisimilarity

mutual
  data _~_ {i : Size} {A : Set} : (a? b? : Delay A ∞) → Set where
    ~now   : ∀ a → now a ~ now a
    ~later : ∀ {a∞ b∞} → _∞~_ {i} a∞ b∞ → later a∞ ~ later b∞

  record _∞~_ {i : Size} {A : Set} (a∞ b∞ : ∞Delay A ∞) : Set where
    field
      ~force : {j : Size< i} → _~_ {j} (force a∞) (force b∞)

open _∞~_

-- Reflexivity

mutual
  ~refl  : ∀ {i A} (a? : Delay A ∞) → _~_ {i} a? a?
  ~refl (now a)    = ~now a
  ~refl (later a∞) = ~later (∞~refl a∞)

  ∞~refl : ∀ {i A} (a∞ : ∞Delay A ∞) → _∞~_ {i} a∞ a∞
  ~force (∞~refl a∞) = ~refl (force a∞)

-- Symmetry: TODO

-- Transitivity: TODO

-- Monad laws.

mutual
  bind-assoc : ∀ {i A B C} (m : Delay A ∞) {k : A → Delay B ∞} {l : B → Delay C ∞} →

    _~_ {i} ((m >>= k) >>= l)  (m >>= λ a → k a >>= l)

  bind-assoc (now a)    = ~refl _
  bind-assoc (later a∞) = ~later (∞bind-assoc a∞)

  ∞bind-assoc : ∀ {i A B C} (a∞ : ∞Delay A ∞) {k : A → Delay B ∞} {l : B → Delay C ∞} →

    _∞~_ {i} ((a∞ ∞>>= λ a → k a) ∞>>= l) (a∞ ∞>>= λ a → k a >>= l)

  ~force (∞bind-assoc a∞) = bind-assoc (force a∞)

-- Termination/Convergence.  Makes only sense for Delay A ∞.

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
