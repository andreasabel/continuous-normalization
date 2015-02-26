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

subst~⇓ : ∀{A R}{t t' : Delay ∞ A}{n : A} → t ⇓ n → Delay R ∋ t ~ t' → t' ⇓
subst~⇓        now⇓       (~now a⇓ b⇓ aRb)          = _ , b⇓
subst~⇓ {R = R}(later⇓ p) (~now (later⇓ a⇓) b⇓ aRb) =
  subst~⇓ {R = R} p (~now a⇓ b⇓ aRb)
subst~⇓        (later⇓ p) (~later ∞p)               =
  let n' , p = subst~⇓ p (~force ∞p) in n' , later⇓ p

-- don't want to assume symmetry of R in ~trans, so... 
subst~⇓' : ∀{A R}{t t' : Delay ∞ A}{n : A} → t' ⇓ n → Delay R ∋ t ~ t' → t ⇓
subst~⇓'         now⇓       (~now a⇓ b⇓ aRb)          = _  , a⇓
subst~⇓' {R = R} (later⇓ p) (~now a⇓ (later⇓ b⇓) aRb) =
  subst~⇓' {R = R} p (~now a⇓ b⇓ aRb)
subst~⇓'         (later⇓ p) (~later ∞p)               =
  let n' , p = subst~⇓' p (~force ∞p) in n' , later⇓ p 


det~⇓ : ∀{A R}{t t' : Delay ∞ A}{n n' : A} →
        t ⇓ n → Delay R ∋ t ~ t' → t' ⇓ n' → R n n'
det~⇓ p (~now a⇓ b⇓ aRb) r with uniq⇓ p a⇓ | uniq⇓ b⇓ r
... | refl | refl = aRb
det~⇓ (later⇓ p) (~later ∞p) (later⇓ r) = det~⇓ p (~force ∞p) r


-- Reflexivity

~refl  : ∀ {i A} (a? : Delay ∞ A) → a? ~⟨ i ⟩~ a?
~refl a = ≈→~ (≈refl a)

∞~refl : ∀ {i A} (a∞ : ∞Delay ∞ A) → _∞~_ {i} a∞ a∞
∞~refl a∞ = ∞≈→~ (∞≈refl a∞)

-- Symmetry

mutual
  ~sym : ∀ {i A R} {a? b? : Delay ∞ A} →
        (∀ {a b} → R a b → R b a) → 
         Delay R ∋ a? ~⟨ i ⟩~ b? → Delay R ∋ b? ~⟨ i ⟩~ a?
  ~sym X (~now p q r) = ~now q p (X r)
  ~sym X (~later p)   = ~later (∞~sym X p)

  ∞~sym : ∀ {i A R} {a? b? : ∞Delay ∞ A} →
          (∀ {a b} → R a b → R b a) →
          ∞Delay R ∋ a? ~⟨ i ⟩~ b? → ∞Delay R ∋ b? ~⟨ i ⟩~ a?
  ~force (∞~sym X p) = ~sym X (~force p)

-- Transitivity

mutual
  ~trans : ∀ {i A R} {a? b? c? : Delay ∞ A} → 
   (∀ {a b c} → R a b → R b c → R a c) → 
   (eq : Delay R ∋ a? ~⟨ ∞ ⟩~ b?) (eq' : Delay R ∋ b? ~⟨ ∞ ⟩~ c?) →
    Delay R ∋ a? ~⟨ i ⟩~ c?
  ~trans {R = R} X (~now p q r) (~now p' q' r') =
    ~now p q' (X r (subst (λ x → R x _) (sym (uniq⇓ q p')) r' ))
  ~trans X (~now p q r)    p'                = let x , y = subst~⇓ q p' in
    ~now p y (X r (det~⇓ q p' y))
    
  ~trans X p               (~now p' q' r')   = let x , y = subst~⇓' p' p in
    ~now y q' (X (det~⇓ y p p') r')

  ~trans X (~later p)      (~later p')       = ~later (∞~trans X p p')

  ∞~trans : ∀ {i A R} {a∞ b∞ c∞ : ∞Delay ∞ A} → 
    (∀ {a b c} → R a b → R b c → R a c) → 
    (eq : ∞Delay R ∋ a∞ ~⟨ ∞ ⟩~ b∞) (eq' : ∞Delay R ∋ b∞ ~⟨ ∞ ⟩~ c∞) →
    ∞Delay R ∋ a∞ ~⟨ i ⟩~ c∞
  ~force (∞~trans X p p') = ~trans X (~force p) (~force p')

