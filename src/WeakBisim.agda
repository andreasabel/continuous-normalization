{-# OPTIONS --copatterns #-}

module WeakBisim where

open import Library
open import Delay

-- Weak bisimilarity.
------------------------------------------------------------------------

mutual
  data Delay_∋_~_ {i}{A}(R : A → A → Set) : (a? b? : Delay ∞ A) → Set where
    ~now   : ∀{a b a? b?}
           → (a⇓ : a? ⇓ a) (b⇓ : b? ⇓ b) (aRb : R a b)
           → Delay R ∋ a? ~ b?
    ~later : ∀{a∞ b∞}
           → (∞p : ∞Delay R ∋ a∞ ~⟨ i ⟩~ b∞)
           → Delay R ∋ later a∞ ~ later b∞

  Delay_∋_~⟨_⟩~_ = λ {A} R a? i b? → Delay_∋_~_ {i}{A} R a? b?

  record ∞Delay_∋_~⟨_⟩~_ {A} R (a∞ : ∞Delay ∞ A) i (b∞ : ∞Delay ∞ A) : Set where
    coinductive
    constructor ~delay
    field
      ~force : {j : Size< i} → Delay R ∋ force a∞ ~⟨ j ⟩~ force b∞

open ∞Delay_∋_~⟨_⟩~_ public
∞Delay_∋_~_ = λ {i} {A} R a∞ b∞ → ∞Delay_∋_~⟨_⟩~_ {A} R a∞ i b∞

mutual
  map~ : ∀ {A B R S}{a a' : Delay ∞ A}
         (f : A → B)
         (g : ∀ a a' → R a a' → S (f a) (f a')) → 
         Delay R ∋ a ~ a' → Delay S ∋ f <$> a ~ (f <$> a')
  map~ f g (~now a⇓ a'⇓ aRa') = ~now (map⇓ f a⇓) (map⇓ f a'⇓) (g _ _ aRa')
  map~ f g (~later ∞p)      = ~later (∞map~ f g ∞p)       

  ∞map~ : ∀ {A B R S}{a a' : ∞Delay ∞ A}
         (f : A → B)
         (g : ∀ a a' → R a a' → S (f a) (f a')) → 
         ∞Delay R ∋ a ~ a' → ∞Delay S ∋ f ∞<$> a ~ (f ∞<$> a')
  ~force (∞map~ f g p) = map~ f g (~force p)

-- Delaying left only

mutual
  ~laterl : ∀{i A} {R : A → A → Set} {a∞ : ∞Delay ∞ A} {b? : Delay ∞ A} →
    (p : Delay R ∋ force a∞ ~⟨ i ⟩~ b?) → Delay R ∋ later a∞ ~⟨ i ⟩~ b?
  ~laterl {a∞ = a∞} p with force a∞ {∞} | inspect (λ a∞ → force a∞ {∞}) a∞
  ~laterl (~now a⇓ b⇓ aRb) | ._ | [ eq ] with eq
  ~laterl (~now a⇓ b⇓ aRb) | ._ | [ eq ] | refl = ~now (later⇓ a⇓) b⇓ aRb
  ~laterl {A = A}{R} (~later ∞p) | ._ | [ eq ] = ~later (aux eq ∞p)
     where

       aux' : ∀ {i} {a∞ a∞₁ b∞ : ∞Delay ∞ A}
            → (eq : force a∞ ≡ later a∞₁)
            → (∞p : ∞Delay R ∋ a∞₁ ~⟨ i ⟩~ b∞)
            → {j : Size< i} → Delay R ∋ force a∞ ~⟨ j ⟩~ force b∞
       aux' eq ∞p rewrite eq = ~laterl (∞Delay_∋_~⟨_⟩~_.~force ∞p)

       aux : ∀ {i} {a∞ a∞₁ b∞ : ∞Delay ∞ A}
           → (eq : force a∞ ≡ later a∞₁)
           → (∞p : ∞Delay R ∋ a∞₁ ~⟨ i ⟩~ b∞)
           → ∞Delay R ∋ a∞ ~⟨ i ⟩~ b∞
       ∞Delay_∋_~⟨_⟩~_.~force (aux {a∞ = a∞} eq ∞p) {j} = aux' {a∞ = a∞} eq ∞p {j}
         -- NYI: rewrite with copatterns.  Thus, we need aux'.

~laterl′ : ∀{i A} {R : A → A → Set} {a? : Delay ∞ A} {b? : Delay ∞ A} →
  (p : Delay R ∋ a? ~⟨ i ⟩~ b?) → Delay R ∋ later (delay a?) ~⟨ i ⟩~ b?
~laterl′ p = ~laterl p

∞~laterl : ∀{i A} {R : A → A → Set} {a∞ : ∞Delay ∞ A} {b∞ : ∞Delay ∞ A} →
  (p : ∞Delay R ∋ a∞ ~⟨ i ⟩~ b∞) → ∞Delay R ∋ delay (later a∞) ~⟨ i ⟩~ b∞
∞Delay_∋_~⟨_⟩~_.~force (∞~laterl p) = ~laterl ( ∞Delay_∋_~⟨_⟩~_.~force p)

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

-- two computations are weakly bisimilar, and one converges,
-- so does the other, and to the same value

subst~⇓ : ∀{A}{t t' : Delay ∞ A}{n : A} → t ⇓ n → t ~⟨ ∞ ⟩~ t' → t' ⇓ n
subst~⇓ now⇓       (~now now⇓ q refl)       = q
subst~⇓ (later⇓ p) (~now (later⇓ p') q' r') = subst~⇓ p (~now p' q' r')
subst~⇓ (later⇓ p) (~later q)               = later⇓ (subst~⇓ p (~force q))

-- Reflexivity

~refl  : ∀ {i A} (a? : Delay ∞ A) → a? ~⟨ i ⟩~ a?
~refl a = ≈→~ (≈refl a)

∞~refl : ∀ {i A} (a∞ : ∞Delay ∞ A) → _∞~_ {i} a∞ a∞
∞~refl a∞ = ∞≈→~ (∞≈refl a∞)

-- Symmetry

mutual
  ~sym : ∀ {i A} {a? b? : Delay ∞ A} → a? ~⟨ i ⟩~ b? → b? ~⟨ i ⟩~ a?
  ~sym (~now p q r) = ~now q p (sym r)
  ~sym (~later p)   = ~later (∞~sym p)

  ∞~sym : ∀ {i A} {a? b? : ∞Delay ∞ A} → a? ∞~⟨ i ⟩~ b? → b? ∞~⟨ i ⟩~ a?
  ~force (∞~sym p) = ~sym (~force p)

-- Transitivity

mutual
  ~trans : ∀ {i A} {a? b? c? : Delay ∞ A}
    (eq : a? ~⟨ ∞ ⟩~ b?) (eq' : b? ~⟨ ∞ ⟩~ c?) → a? ~⟨ i ⟩~ c?
  ~trans (~now p q refl) (~now p' q' refl) = ~now p q' (uniq⇓ q p')
  ~trans (~now p q r)    p'                = ~now p (subst~⇓ q  p') r
  ~trans p               (~now p' q' r')   = ~now (subst~⇓ p' (~sym p)) q' r'
  ~trans (~later p)      (~later p')       = ~later (∞~trans p p')

  ∞~trans : ∀ {i A} {a∞ b∞ c∞ : ∞Delay ∞ A}
    (eq : a∞ ∞~⟨ ∞ ⟩~ b∞) (eq' : b∞ ∞~⟨ ∞ ⟩~ c∞) → a∞ ∞~⟨ i ⟩~ c∞
  ~force (∞~trans p p') = ~trans (~force p) (~force p')

