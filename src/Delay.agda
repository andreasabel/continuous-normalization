{-# OPTIONS --copatterns --sized-types #-}
-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.conv:10 -v tc.conv.size:15 #-}
module Delay where

open import Library
open import Category.Applicative.Indexed
-- Coinductive delay monad.

mutual

  data Delay (i : Size) (A : Set) : Set where
    now   : A          → Delay i A
    later : ∞Delay i A → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay j A

open ∞Delay public

-- Smart constructor.

later! : ∀ {A i} → Delay i A → Delay (↑ i) A
later! x = later (delay x)

-- Example: non-termination.

never : ∀ {A i} → ∞Delay A i
force never = later never

-- Monad instance.

module Bind where
  mutual
    _>>=_ : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
    now   x >>= f = f x
    later x >>= f = later (x ∞>>= f)

    _∞>>=_ :  ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (x ∞>>= f) = force x >>= f

delayMonad : ∀ {i} → RawMonad {f = lzero} (Delay i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i})
                           public renaming (_⊛_ to _<*>_)
open Bind public using (_∞>>=_)

-- Map for ∞Delay

_∞<$>_ : ∀ {i A B} (f : A → B) (∞a : ∞Delay i A) → ∞Delay i B
f ∞<$> ∞a = ∞a ∞>>= λ a → return (f a)
-- force (f ∞<$> ∞a) = f <$> force ∞a

-- Double bind

_=<<2_,_ : ∀ {i A B C} → (A → B → Delay i C) → Delay i A → Delay i B → Delay i C
f =<<2 x , y = x >>= λ a → y >>= λ b → f a b

-- Lifting a predicate to Delay (without convergence).

mutual
  data Delay₁ i {A : Set} (P : A → Set) : Delay ∞ A → Set where
    now₁   : ∀{a}  → (p : P a) → Delay₁ i P (now a)
    later₁ : ∀{a∞} → ∞Delay₁ i P a∞ → Delay₁ i P (later a∞)

  record ∞Delay₁ i {A : Set} (P : A → Set) (a∞ : ∞Delay ∞ A) : Set where
    coinductive
    constructor delay₁
    field force₁ :  {j : Size< i} → Delay₁ j P (force a∞)
open ∞Delay₁ public

{-
_<*>₁_ : ∀{A B : Set}{Q : A → Set}{R : B → Set}
        {f : Delay ∞ (A → B)}
        {v : Delay ∞ A} → 
        Delay₁ ∞ (λ f → ∀ v → Q v → R (f v)) f →
        Delay₁ ∞ Q v →
        Delay₁ ∞ R (f <*> v)
p <*>₁ q = ?
-}
-- Strong bisimilarity

mutual
  data _≈_ {i : Size} {A : Set} : (a? b? : Delay ∞ A) → Set where
    ≈now   : ∀ a → now a ≈ now a
    ≈later : ∀ {a∞ b∞} (eq : a∞ ∞≈⟨ i ⟩≈ b∞) → later a∞ ≈ later b∞

  _≈⟨_⟩≈_ = λ {A} a? i b? → _≈_ {i}{A} a? b?

  record _∞≈⟨_⟩≈_ {A} (a∞ : ∞Delay ∞ A) i (b∞ : ∞Delay ∞ A) : Set where
    coinductive
    field
      ≈force : {j : Size< i} → force a∞ ≈⟨ j ⟩≈ force b∞

_∞≈_ = λ {i} {A} a∞ b∞ → _∞≈⟨_⟩≈_ {A} a∞ i b∞
open _∞≈⟨_⟩≈_ public

≡to≈ : ∀{A}{a a' : A} → a ≡ a' → now a ≈ now a'
≡to≈ refl = ≈now _

-- Reflexivity

mutual
  ≈refl  : ∀ {i A} (a? : Delay ∞ A) → a? ≈⟨ i ⟩≈ a?
  ≈refl (now a)    = ≈now a
  ≈refl (later a∞) = ≈later (∞≈refl a∞)

  ∞≈refl : ∀ {i A} (a∞ : ∞Delay ∞ A) → _∞≈_ {i} a∞ a∞
  ≈force (∞≈refl a∞) = ≈refl (force a∞)

-- Symmetry

mutual
  ≈sym : ∀ {i A} {a? b? : Delay ∞ A} → a? ≈⟨ i ⟩≈ b? → b? ≈⟨ i ⟩≈ a?
  ≈sym (≈now a)    = ≈now a
  ≈sym (≈later eq) = ≈later (∞≈sym eq)

  ∞≈sym : ∀ {i A} {a? b? : ∞Delay ∞ A} → a? ∞≈⟨ i ⟩≈ b? → b? ∞≈⟨ i ⟩≈ a?
  ≈force (∞≈sym eq) = ≈sym (≈force eq)

-- Transitivity

mutual
  ≈trans : ∀ {i A} {a? b? c? : Delay ∞ A}
    (eq : a? ≈⟨ i ⟩≈ b?) (eq' : b? ≈⟨ i ⟩≈ c?) → a? ≈⟨ i ⟩≈ c?
  ≈trans (≈now a)    (≈now .a)    = ≈now a
  ≈trans (≈later eq) (≈later eq') = ≈later (∞≈trans eq eq')

  ∞≈trans : ∀ {i A} {a∞ b∞ c∞ : ∞Delay ∞ A}
    (eq : a∞ ∞≈⟨ i ⟩≈ b∞) (eq' : b∞ ∞≈⟨ i ⟩≈ c∞) → a∞ ∞≈⟨ i ⟩≈ c∞
  ≈force (∞≈trans eq eq') = ≈trans (≈force eq) (≈force eq')

-- Equality reasoning

≈setoid : (i : Size) (A : Set) → Setoid lzero lzero
≈setoid i A = record
  { Carrier       = Delay ∞ A
  ; _≈_           = _≈_ {i}
  ; isEquivalence = record
    { refl  = λ {a?} → ≈refl a?
    ; sym   = ≈sym
    ; trans = ≈trans
    }
  }

module ≈-Reasoning {i : Size} {A : Set} where
  open Pre (Setoid.preorder (≈setoid i A)) public
--    using (begin_; _∎) (_≈⟨⟩_ to _≈⟨⟩_; _≈⟨_⟩_ to _≈⟨_⟩_)
    renaming (_≈⟨⟩_ to _≡⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _≈⟨_⟩_; begin_ to proof_)

∞≈setoid : (i : Size) (A : Set) → Setoid lzero lzero
∞≈setoid i A = record
  { Carrier       = ∞Delay ∞ A
  ; _≈_           = _∞≈_ {i}
  ; isEquivalence = record
    { refl  = λ {a?} → ∞≈refl a?
    ; sym   = ∞≈sym
    ; trans = ∞≈trans
    }
  }

module ∞≈-Reasoning {i : Size} {A : Set} where
  open Pre (Setoid.preorder (∞≈setoid i A)) public
--    using (begin_; _∎) (_≈⟨⟩_ to _≈⟨⟩_; _≈⟨_⟩_ to _≈⟨_⟩_)
    renaming (_≈⟨⟩_ to _≡⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _∞≈⟨_⟩_; begin_ to proof_)


-- Congruence laws.

mutual
  bind-cong-l : ∀ {i A B} {a? b? : Delay ∞ A} (eq : a? ≈⟨ i ⟩≈ b?)
    (k : A → Delay ∞ B) → (a? >>= k) ≈⟨ i ⟩≈ (b? >>= k)
  bind-cong-l (≈now a)    k = ≈refl _
  bind-cong-l (≈later eq) k = ≈later (∞bind-cong-l eq k)

  ∞bind-cong-l : ∀ {i A B} {a∞ b∞ : ∞Delay ∞ A} (eq : a∞ ∞≈⟨ i ⟩≈ b∞) →
    (k : A → Delay ∞ B) →
    _∞≈_ {i} (a∞ ∞>>= k)  (b∞ ∞>>= k)
  ≈force (∞bind-cong-l eq k) = bind-cong-l (≈force eq) k

_>>=l_ = bind-cong-l

mutual
  bind-cong-r : ∀ {i A B} (a? : Delay ∞ A) {k l : A → Delay ∞ B} →
    (h : ∀ a → (k a) ≈⟨ i ⟩≈ (l a)) → (a? >>= k) ≈⟨ i ⟩≈ (a? >>= l)
  bind-cong-r (now a)    h = h a
  bind-cong-r (later a∞) h = ≈later (∞bind-cong-r a∞ h)

  ∞bind-cong-r : ∀ {i A B} (a∞ : ∞Delay ∞ A) {k l : A → Delay ∞ B} →
    (h : ∀ a → (k a) ≈⟨ i ⟩≈ (l a)) → (a∞ ∞>>= k) ∞≈⟨ i ⟩≈ (a∞ ∞>>= l)
  ≈force (∞bind-cong-r a∞ h) = bind-cong-r (force a∞) h

_>>=r_ = bind-cong-r

mutual
  bind-cong : ∀ {i A B}  {a? b? : Delay ∞ A} (eq : a? ≈⟨ i ⟩≈ b?)
              {k l : A → Delay ∞ B} (h : ∀ a → (k a) ≈⟨ i ⟩≈ (l a)) →
              (a? >>= k) ≈⟨ i ⟩≈ (b? >>= l)
  bind-cong (≈now a)    h = h a
  bind-cong (≈later eq) h = ≈later (∞bind-cong eq h)

  ∞bind-cong : ∀ {i A B} {a∞ b∞ : ∞Delay ∞ A} (eq : a∞ ∞≈⟨ i ⟩≈ b∞)
    {k l : A → Delay ∞ B} (h : ∀ a → (k a) ≈⟨ i ⟩≈ (l a)) →
    _∞≈_ {i} (a∞ ∞>>= k)  (b∞ ∞>>= l)
  ≈force (∞bind-cong eq h) = bind-cong (≈force eq) h

_≈>>=_ = bind-cong

-- Monad laws.

mutual -- why don't I need size i here?
  bind-now : ∀{A}(m : Delay ∞ A) → m ≈ (m >>= now)
  bind-now (now a)   = ≈now a
  bind-now (later m) = ≈later (∞bind-now m)

  ∞bind-now : ∀{A}(m : ∞Delay ∞ A) → m ∞≈ (m ∞>>= now)
  ≈force (∞bind-now m) = bind-now (force m)

mutual
  bind-assoc : ∀{i A B C}(m : Delay ∞ A)
               {k : A → Delay ∞ B}{l : B → Delay ∞ C} →
               ((m >>= k) >>= l) ≈⟨ i ⟩≈ (m >>= λ a → k a >>= l)
  bind-assoc (now a)    = ≈refl _
  bind-assoc (later a∞) = ≈later (∞bind-assoc a∞)

  ∞bind-assoc : ∀{i A B C}(a∞ : ∞Delay ∞ A)
                {k : A → Delay ∞ B}{l : B → Delay ∞ C} →
                ((a∞ ∞>>= λ a → k a) ∞>>= l) ∞≈⟨ i ⟩≈ (a∞ ∞>>= λ a → k a >>= l)
  ≈force (∞bind-assoc a∞) = bind-assoc (force a∞)

map-compose : ∀{i A B C} (a? : Delay ∞ A) {f : A → B} {g : B → C} →
  (g <$> (f <$> a?)) ≈⟨ i ⟩≈ ((g ∘ f) <$> a?)
map-compose a? = bind-assoc a?

map-cong : ∀{i A B}{a? b? : Delay ∞ A} (f : A → B) →
  a? ≈⟨ i ⟩≈ b? → (f <$> a?) ≈⟨ i ⟩≈ (f <$> b?)
map-cong f eq = bind-cong-l eq (now ∘ f)

-- Termination/Convergence.  Makes sense only for Delay A ∞.

data _⇓_ {A : Set} : (a? : Delay ∞ A) (a : A) → Set where
  now⇓   : ∀ {a} → now a ⇓ a
  later⇓ : ∀ {a} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a → later a∞ ⇓ a

_⇓ : {A : Set} (x : Delay ∞ A) → Set
x ⇓ = ∃ λ a → x ⇓ a

-- Lifting a predicate to Delay using convergence.

record Delay⇓ {A : Set} (P : A → Set) (a? : Delay ∞ A) : Set where
  constructor delay⇓
  field
    a  : A
    a⇓ : a? ⇓ a
    pa : P a

-- Monotonicity.

map⇓ : ∀ {A B} {a : A} {a? : Delay ∞ A}
  (f : A → B) (a⇓ : a? ⇓ a) → (f <$> a?) ⇓ f a
map⇓ f now⇓        = now⇓
map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)

-- some lemmas about convergence
subst≈⇓ : ∀{A}{t t' : Delay ∞ A}{n : A} → t ⇓ n → t ≈ t' → t' ⇓ n
subst≈⇓ now⇓ (≈now a) = now⇓
subst≈⇓ (later⇓ p) (≈later eq) = later⇓ (subst≈⇓ p (≈force eq))

uniq⇓ : ∀{A}{a? : Delay ∞ A}{a a' : A} → a? ⇓ a → a? ⇓ a' → a ≡ a'
uniq⇓ now⇓ now⇓             = refl
uniq⇓ (later⇓ p) (later⇓ q) = uniq⇓ p q

-- this should also hold for weak bisimularity right?
{-
subst≈⇓ : ∀{A}{t t' : Delay A ∞}{n : A} → t ⇓ n → t ≈ t' → t' ⇓ n
subst≈⇓ = ?
-}


⇓bind : ∀{A B}(f : A → Delay ∞ B)
       {?a : Delay ∞ A}{a : A} → ?a ⇓ a →
       {b : B} → (?a >>= f) ⇓ b → f a ⇓ b
⇓bind f now⇓ q = q
⇓bind f (later⇓ p) (later⇓ q) = ⇓bind f p q

bind⇓ : ∀{A B}(f : A → Delay ∞ B)
       {?a : Delay ∞ A}{a : A} → ?a ⇓ a →
       {b : B} → f a ⇓ b → (?a >>= f) ⇓ b
bind⇓ f now⇓ q = q
bind⇓ f (later⇓ p) q = later⇓ (bind⇓ f p q)

-- handy when you can't pattern match like in a let definition
unlater : ∀{A}{∞a : ∞Delay ∞ A}{a : A} → later ∞a ⇓ a → force ∞a ⇓ a
unlater (later⇓ p) = p








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


-- transD and transP could just be defined using mapD
mutual
  transD : ∀{i}{A : Set} (P : A → Set){a? b? : Delay ∞ A} →
           a? ≈⟨ i ⟩≈ b? → Delay₁ i P a? → Delay₁ i P b?
  transD P (≈now a)    (now₁ p)   = now₁ p
  transD P (≈later eq) (later₁ p) = later₁ $ ∞transD P eq p

  ∞transD : ∀{i}{A : Set}(P : A → Set){a? b? : ∞Delay ∞ A} →
           a? ∞≈⟨ i ⟩≈ b? → ∞Delay₁ i P a? → ∞Delay₁ i P b?
  force₁ (∞transD P p q) = transD P (≈force p) (force₁ q)

mutual
  transP : ∀{i}{A : Set}(P Q : A → Set){a? : Delay ∞ A} → (∀ {a} → P a → Q a) →
             Delay₁ i P a? → Delay₁ i Q a?
  transP P Q p (now₁ q)   = now₁ (p q)
  transP P Q p (later₁ q) = later₁ (∞transP P Q p q)

  ∞transP : ∀{i}{A : Set}(P Q : A → Set){a? : ∞Delay ∞ A} → 
            (∀ {a} → P a → Q a) →
            ∞Delay₁ i P a? → ∞Delay₁ i Q a?
  force₁ (∞transP P Q p q) = transP P Q p (force₁ q)

mutual
  -- map
  mapD : ∀{i}{A B : Set}(P : A → Set)(Q : B → Set){a? : Delay ∞ A}
            (f : A → B) →
            (∀ {a} → P a → Q (f a)) →
             Delay₁ i P a? → Delay₁ i Q (f <$> a?)
  mapD P Q f p (now₁ q)   = now₁ (p q) 
  mapD P Q f p (later₁ q) = later₁ (∞mapD P Q f p q)

  ∞mapD : ∀{i}{A B : Set}(P : A → Set)(Q : B → Set){a? : ∞Delay ∞ A}
             (f : A → B) → 
             (∀ {a} → P a → Q (f a)) →
             ∞Delay₁ i P a? → ∞Delay₁ i Q (f ∞<$> a?)
  force₁ (∞mapD P Q f p q) = mapD P Q f p (force₁ q)

mutual
  -- bind
  bindD : ∀{A B : Set}(P : A → Set)(Q : B → Set){a? : Delay ∞ A} →
            (f : A → Delay ∞ B) → 
            (g : ∀ a → P a → Delay₁ ∞ Q (f a)) →
            Delay₁ ∞ P a? → Delay₁ ∞ Q (a? >>= f)
  bindD P Q f g (now₁ p)   = g _ p
  bindD P Q f g (later₁ p) = later₁ (∞bindD P Q f g p)

  ∞bindD : ∀{A B : Set}(P : A → Set)(Q : B → Set){a? : ∞Delay ∞ A} →
            (f : A → Delay ∞ B) → 
            (g : ∀ a → P a → Delay₁ ∞ Q (f a)) →
            ∞Delay₁ ∞ P a? → ∞Delay₁ ∞ Q (a? ∞>>= f)
  force₁ (∞bindD P Q f g p) = bindD P Q f g (force₁ p)
