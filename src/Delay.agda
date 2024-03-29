module Delay where

open import Library
open import Category.Applicative.Indexed
-- Coinductive delay monad.

infix 10 _⇓_

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

  infixl 10 _>>=_  _∞>>=_

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


_∞<*>_ : ∀ {i A B} (f : ∞Delay i (A → B))(a : Delay i A) → ∞Delay i B
f ∞<*> a = f ∞>>= λ f → f <$> a
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

-- Strong bisimilarity

mutual
  data Delay_∋_≈_ {i}{A}(R : A → A → Set) : (a? b? : Delay ∞ A) → Set where
    ≈now   : ∀ a a' → R a a' → Delay R ∋ now a ≈ now a'
    ≈later : ∀ {a∞ b∞}(eq : ∞Delay R ∋ a∞ ≈⟨ i ⟩≈ b∞) →
             Delay R ∋ later a∞ ≈ later b∞

  Delay_∋_≈⟨_⟩≈_ = λ {A} R a? i b? → Delay_∋_≈_ {i}{A} R a? b?

  record ∞Delay_∋_≈⟨_⟩≈_ {A} R (a∞ : ∞Delay ∞ A) i (b∞ : ∞Delay ∞ A) : Set where
    coinductive
    field
      ≈force : {j : Size< i} → Delay R ∋ force a∞ ≈⟨ j ⟩≈ force b∞


∞Delay_∋_≈_ = λ {i} {A} R a∞ b∞ → ∞Delay_∋_≈⟨_⟩≈_ {A} R a∞ i b∞
open ∞Delay_∋_≈⟨_⟩≈_ public

_≈⟨_⟩≈_ = λ {A} a i b → Delay_∋_≈⟨_⟩≈_ {A} _≡_ a i b
_≈_ = λ {i} {A} a b → _≈⟨_⟩≈_ {A} a i b

_∞≈⟨_⟩≈_ = λ {A} a∞ i b∞ → ∞Delay_∋_≈⟨_⟩≈_ {A} _≡_ a∞ i b∞
_∞≈_ = λ {i} {A} a∞ b∞ → _∞≈⟨_⟩≈_ {A} a∞ i b∞

≡to≈ : ∀{A}{a a' : A} → a ≡ a' → now a ≈ now a'
≡to≈ refl = ≈now _ _ refl

-- Reflexivity

mutual
  ≈refl  : ∀ {i A}{R : A → A → Set}(X : ∀ {a} → R a a)
           (a? : Delay ∞ A) → Delay R ∋ a? ≈⟨ i ⟩≈ a?
  ≈refl X (now a)    = ≈now a a X
  ≈refl X (later a∞) = ≈later (∞≈refl X a∞)

  ∞≈refl : ∀ {i A}{R : A → A → Set}(X : ∀ {a} → R a a)
           (a∞ : ∞Delay ∞ A) → ∞Delay R ∋ a∞ ≈⟨ i ⟩≈ a∞
  ≈force (∞≈refl X a∞) = ≈refl X (force a∞)

-- Symmetry


mutual
  ≈sym' : ∀ {i A} {a? b? : Delay ∞ A}{R : A → A → Set} →
          (∀ {a a'} → R a a' → R a' a) →
          Delay R ∋ a? ≈⟨ i ⟩≈ b? → Delay R ∋ b? ≈⟨ i ⟩≈ a?
  ≈sym' p (≈now a a' q) = ≈now a' a (p q)
  ≈sym' p (≈later q) = ≈later (∞≈sym' p q)

  ∞≈sym' : ∀ {i A} {a? b? : ∞Delay ∞ A}{R : A → A → Set} →
           (∀ {a a'} → R a a' → R a' a) →
           ∞Delay R ∋ a? ≈⟨ i ⟩≈ b? → ∞Delay R ∋ b? ≈⟨ i ⟩≈ a?
  ≈force (∞≈sym' p q) = ≈sym' p (≈force q)

≈sym : ∀ {i A} {a? b? : Delay ∞ A} → a? ≈⟨ i ⟩≈ b? → b? ≈⟨ i ⟩≈ a?
≈sym = ≈sym' sym

∞≈sym : ∀ {i A} {a? b? : ∞Delay ∞ A} → a? ∞≈⟨ i ⟩≈ b? → b? ∞≈⟨ i ⟩≈ a?
∞≈sym = ∞≈sym' sym

-- Transitivity

mutual
  ≈trans : ∀ {i A} {a? b? c? : Delay ∞ A}
    (eq : a? ≈⟨ i ⟩≈ b?) (eq' : b? ≈⟨ i ⟩≈ c?) → a? ≈⟨ i ⟩≈ c?
  ≈trans (≈now a a' p)    (≈now .a' a'' q)    = ≈now a a'' (trans p q)
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
    { refl  = λ {a?} → ≈refl refl a?
    ; sym   = ≈sym
    ; trans = ≈trans
    }
  }

module ≈-Reasoning {i : Size} {A : Set} where
  open SetoidReasoning (≈setoid i A) public

∞≈setoid : (i : Size) (A : Set) → Setoid lzero lzero
∞≈setoid i A = record
  { Carrier       = ∞Delay ∞ A
  ; _≈_           = _∞≈_ {i}
  ; isEquivalence = record
    { refl  = λ {a?} → ∞≈refl  refl a?
    ; sym   = ∞≈sym
    ; trans = ∞≈trans
    }
  }

module ∞≈-Reasoning {i : Size} {A : Set} where
  private module M = SetoidReasoning (∞≈setoid i A)
  open M public using (begin_; _∎; _≡⟨⟩_; step-≡)
  step-∞≈ = M.step-≈
  infixr 2 step-∞≈
  syntax step-∞≈ x y≈z x≈y = x ∞≈⟨ x≈y ⟩ y≈z

-- Congruence laws.

mutual
  bind-cong-l : ∀ {i A B} {a? b? : Delay ∞ A} (eq : a? ≈⟨ i ⟩≈ b?)
   (k : A → Delay ∞ B) → (a? >>= k) ≈⟨ i ⟩≈ (b? >>= k)
  bind-cong-l (≈now a .a refl) k = ≈refl refl (k a)
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
  bind-cong (≈now a .a refl) h = h a
  bind-cong (≈later eq) h = ≈later (∞bind-cong eq h)

  ∞bind-cong : ∀ {i A B} {a∞ b∞ : ∞Delay ∞ A} (eq : a∞ ∞≈⟨ i ⟩≈ b∞)
    {k l : A → Delay ∞ B} (h : ∀ a → (k a) ≈⟨ i ⟩≈ (l a)) →
    _∞≈_ {i} (a∞ ∞>>= k)  (b∞ ∞>>= l)
  ≈force (∞bind-cong eq h) = bind-cong (≈force eq) h

_≈>>=_ = bind-cong

-- Monad laws.

mutual -- why don't I need size i here?
  bind-now : ∀{i A}(m : Delay ∞ A) → m ≈⟨ i ⟩≈ (m >>= now)
  bind-now (now a)   = ≈now a a refl
  bind-now (later m) = ≈later (∞bind-now m)

  ∞bind-now : ∀{i A}(m : ∞Delay ∞ A) → m ∞≈⟨ i ⟩≈ (m ∞>>= now)
  ≈force (∞bind-now m) = bind-now (force m)

mutual
  bind-assoc' : ∀{i A B C}(m : Delay ∞ A){R : C → C → Set} → (∀ {c} → R c c) →
               {k : A → Delay ∞ B}{l : B → Delay ∞ C} →
               Delay R ∋ ((m >>= k) >>= l) ≈⟨ i ⟩≈ (m >>= λ a → k a >>= l)
  bind-assoc' (now a)    p = ≈refl p _
  bind-assoc' (later a∞) p = ≈later (∞bind-assoc' a∞ p)

  ∞bind-assoc' : ∀{i A B C}(a∞ : ∞Delay ∞ A){R : C → C → Set} → (∀ {c} → R c c) →
                {k : A → Delay ∞ B}{l : B → Delay ∞ C} →
                ∞Delay R ∋ ((a∞ ∞>>= λ a → k a) ∞>>= l) ≈⟨ i ⟩≈ (a∞ ∞>>= λ a → k a >>= l)
  ≈force (∞bind-assoc' a∞ p) = bind-assoc' (force a∞) p

bind-assoc : ∀{i A B C}(m : Delay ∞ A)
               {k : A → Delay ∞ B}{l : B → Delay ∞ C} →
               Delay _≡_ ∋ ((m >>= k) >>= l) ≈⟨ i ⟩≈ (m >>= λ a → k a >>= l)
bind-assoc m = bind-assoc' m {R = _≡_} refl

∞bind-assoc : ∀{i A B C}(a∞ : ∞Delay ∞ A) →
               {k : A → Delay ∞ B}{l : B → Delay ∞ C} →
               ((a∞ ∞>>= λ a → k a) ∞>>= l) ∞≈⟨ i ⟩≈ (a∞ ∞>>= λ a → k a >>= l)
∞bind-assoc a∞ = ∞bind-assoc' a∞ refl

map-compose : ∀{i A B C} (a? : Delay ∞ A) {f : A → B} {g : B → C} →
  (g <$> (f <$> a?)) ≈⟨ i ⟩≈ ((g ∘ f) <$> a?)
map-compose a? = bind-assoc a?

map-cong : ∀{i A B}{a? b? : Delay ∞ A} (f : A → B) →
  a? ≈⟨ i ⟩≈ b? → (f <$> a?) ≈⟨ i ⟩≈ (f <$> b?)
map-cong f eq = bind-cong-l eq (now ∘ f)

∞map-cong : ∀{i A B}{a? b? : ∞Delay ∞ A} (f : A → B) →
  a? ∞≈⟨ i ⟩≈ b? → (f ∞<$> a?) ∞≈⟨ i ⟩≈ (f ∞<$> b?)
∞map-cong f eq = ∞bind-cong-l eq (now ∘ f)

*-cong : ∀{i A B}{a? b? : Delay ∞ A}{f f' : Delay ∞ (A → B)} →
  f ≈⟨ i ⟩≈ f' → a? ≈⟨ i ⟩≈ b? → (f <*> a?) ≈⟨ i ⟩≈ (f' <*> b?)
*-cong p q = bind-cong p (λ f → bind-cong-l q (now ∘ f))

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


map2⇓ : ∀ {A B C}
        {a : A}{a? : Delay ∞ A}
        {b : B}{b? : Delay ∞ B}
        (f : A → B → C)
        (a⇓ : a? ⇓ a) →
        (b⇓ : b? ⇓ b) →
        (f <$> a? <*> b?) ⇓ f a b
map2⇓ f now⇓        now⇓       = now⇓
map2⇓ f now⇓        (later⇓ p) = later⇓ (map2⇓ f now⇓ p)
map2⇓ f (later⇓ p) q           = later⇓ (map2⇓ f p q)

{-
bind⇓' : ∀ {A B} {a : A} {a? : Delay ∞ A}
  (f : A → Delay ∞ B) (a⇓ : a? ⇓ a) → (a? >>= f) ⇓ f a
bind⇓' f now⇓        = {!!}
bind⇓' f (later⇓ a⇓) = {!!} -- later⇓ (map⇓ f a⇓)
-}
-- some lemmas about convergence
subst≈⇓ : ∀{A}{t t' : Delay ∞ A}{n : A} → t ⇓ n → t ≈ t' → t' ⇓ n
subst≈⇓ now⇓ (≈now a .a refl) = now⇓
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

bind⇓2 : ∀{A B C}(f : A → B → Delay ∞ C)
         {?a : Delay ∞ A}{a : A} → ?a ⇓ a →
         {?b : Delay ∞ B}{b : B} → ?b ⇓ b →
         {c : C} → f a b ⇓ c → (?a >>= (λ a → ?b >>= f a)) ⇓ c
bind⇓2 f now⇓ now⇓ r = r
bind⇓2 f now⇓ (later⇓ q) r = later⇓ (bind⇓2 f now⇓ q r)
bind⇓2 f (later⇓ p) q r = later⇓ (bind⇓2 f p q r)

-- nereadback w >>= λ m → app m <$> readback v


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
  transD P (≈now a .a refl)    (now₁ p)   = now₁ p
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
  mapD2 : ∀{i}{A B C : Set}(P : A → Set)(Q : B → Set)(R : C → Set)
          {a? : Delay ∞ A}{b? : Delay ∞ B}
          (f : A → B → C) →
          (∀ {a b} → P a → Q b → R (f a b)) →
          Delay₁ i P a? →
          Delay₁ i Q b? →
          Delay₁ i R (f <$> a? <*> b?)
  mapD2 P Q R f p (now₁ p₁) (now₁ p₂) = now₁ (p p₁ p₂)
  mapD2 P Q R f p (now₁ p₁) (later₁ x) = later₁ (∞mapD Q R (f _) (p p₁) x)
  mapD2 P Q R f p (later₁ x) p₂ = later₁ (∞mapD2 P Q R f p x p₂)

  ∞mapD2 : ∀{i}{A B C : Set}(P : A → Set)(Q : B → Set)(R : C → Set)
           {a? : ∞Delay ∞ A}{b? : Delay ∞ B}
           (f : A → B → C) →
           (∀ {a b} → P a → Q b → R (f a b)) →
           ∞Delay₁ i P a? →
           Delay₁ i Q b? →
           ∞Delay₁ i R ((f ∞<$> a?) ∞<*> b?  )
  force₁ (∞mapD2 P Q R f p q r) = mapD2 P Q R f p (force₁ q) r

mutual
  -- bind
  bindD : ∀{i A B} (P : A → Set)(Q : B → Set){a? : Delay ∞ A} →
            (f : A → Delay ∞ B) →
            (g : ∀ a → P a → Delay₁ i Q (f a)) →
            Delay₁ i P a? → Delay₁ i Q (a? >>= f)
  bindD P Q f g (now₁ p)   = g _ p
  bindD P Q f g (later₁ p) = later₁ (∞bindD P Q f g p)

  ∞bindD : ∀{i A B}(P : A → Set)(Q : B → Set){a? : ∞Delay ∞ A} →
            (f : A → Delay ∞ B) →
            (g : ∀ a → P a → Delay₁ i Q (f a)) →
            ∞Delay₁ i P a? → ∞Delay₁ i Q (a? ∞>>= f)
  force₁ (∞bindD P Q f g p) = bindD P Q f g (force₁ p)


mutual
  ≈reflPER  : ∀ {i A}{R : A → A → Set}(X : ∀ {a a'} → R a a' → R a a)
              (a? : Delay ∞ A){b? : Delay ∞ A} → Delay R ∋ a? ≈⟨ i ⟩≈ b? →
              Delay R ∋ a? ≈⟨ i ⟩≈ a?
  ≈reflPER X (now a) (≈now .a a' p) = ≈now a a (X p)
  ≈reflPER X (later a∞) (≈later eq) = ≈later (∞≈reflPER X a∞ eq)

  ∞≈reflPER  : ∀ {i A}{R : A → A → Set}(X : ∀ {a a'} → R a a' → R a a)
              (a? : ∞Delay ∞ A){b? : ∞Delay ∞ A} → ∞Delay R ∋ a? ≈⟨ i ⟩≈ b? →
              ∞Delay R ∋ a? ≈⟨ i ⟩≈ a?
  ≈force (∞≈reflPER X a? p) = ≈reflPER X (force a?) (≈force p)

-- some laws about <$> and <*>
lifta2lem1 : ∀{A B C D}
             (f : A → B → C)(g : C → D)(a : Delay ∞ A)(b : Delay ∞ B) →
             (g <$> (f <$> a <*> b)) ≈ ((λ a b → g (f a b)) <$> a <*> b)
lifta2lem1 f g a b = begin
  (((a >>= now ∘ f) >>= (λ f' → b >>= now ∘ f')) >>= now ∘ g)
  ≈⟨ bind-assoc (a >>= now ∘ f) ⟩
  ((a >>= now ∘ f) >>= (λ f → (b >>= now ∘ f) >>= now ∘ g))
  ≈⟨ bind-cong-r (a >>= now ∘ f) (λ f' → bind-assoc b) ⟩
  ((a >>= now ∘ f) >>= ( λ f → b >>= λ a' → now (g (f a'))))
  ≈⟨ bind-assoc a ⟩
  (a >>= (λ x' → b >>= λ a' → now (g (f x' a'))))
  ≈⟨ ≈sym (bind-assoc a) ⟩
  ((a >>= (λ x' → now (g ∘ f x'))) >>= (λ f' → b >>= now ∘ f'))
  ∎
 where open ≈-Reasoning

lifta2lem2 : ∀{A A' B B' C : Set}
             (f : A → B → C)(g : A' → A)(h : B' → B)
             (a : Delay ∞ A')(b : Delay ∞ B') →
             ((λ a' b' → f (g a') (h b')) <$> a <*> b) ≈
             (f <$> (g <$> a) <*> (h <$> b))
lifta2lem2 f g h a b = begin
  ((a >>= (λ x' → now (λ b' → f (g x') (h b')))) >>= (λ f' → b >>= (now ∘ f')))
  ≈⟨ bind-assoc a ⟩
  (a >>= (λ x' → b >>= λ x → now (f (g x') (h x))))
  ≈⟨ bind-cong-r a (λ x → ≈sym (bind-assoc b)) ⟩
  (a >>= (λ x → b >>= (now ∘ h) >>= now ∘ f (g x)))
  ≈⟨ ≈sym (bind-assoc a) ⟩
  ((a >>= (now ∘ g)) >>= (λ x' → b >>= (now ∘ h) >>= now ∘ f x' ))
  ≈⟨ ≈sym (bind-assoc (a >>= now ∘ g)) ⟩
  (((a >>= (now ∘ g)) >>= (now ∘ f)) >>= (λ f' → b >>= (now ∘ h) >>= now ∘ f'))
  ∎
  where open ≈-Reasoning
