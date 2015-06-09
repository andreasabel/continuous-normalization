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

--open ∞Delay_∋_~⟨_⟩~_ public
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
  ∞Delay_∋_~⟨_⟩~_.~force (∞map~ f g p) = map~ f g (∞Delay_∋_~⟨_⟩~_.~force p)


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

--open ∞Delay_∋_~⟨_⟩~_ public

-- Strong bisimilarity implies weak bisimilarity.

mutual
  ≈→~ : ∀{i A R}{a? b? : Delay ∞ A} →
        Delay R ∋ a? ≈⟨ i ⟩≈ b? → Delay R ∋ a? ~⟨ i ⟩~ b?
  ≈→~ (≈now a a' p)    = ~now now⇓ now⇓ p
  ≈→~ (≈later eq) = ~later (∞≈→~ eq)

  ∞≈→~ : ∀{i A R}{a∞ b∞ : ∞Delay ∞ A} →
         ∞Delay R ∋ a∞ ≈⟨ i ⟩≈ b∞ →
         ∞Delay R ∋ a∞ ~⟨ i ⟩~ b∞
  ∞Delay_∋_~⟨_⟩~_.~force (∞≈→~ eq) = ≈→~ (≈force eq)

{-
bindlem : ∀{A B R i}{f f' : A → Delay ∞ B}{v v' : A}{v? v?' : Delay ∞ A} →
          Delay R ∋ v? >>= f ~⟨ i ⟩~ (v?' >>= f') → v? ⇓ v → v?' ⇓ v' →
      Delay R ∋ f v ~⟨ i ⟩~ f' v'
bindlem p now⇓       now⇓       = p
bindlem p now⇓       (later⇓ r) = {!p!}
bindlem p (later⇓ q) now⇓       = {!~laterl!}
bindlem (~now (later⇓ a⇓) (later⇓ b⇓) aRb) (later⇓ q) (later⇓ r) = bindlem (~now a⇓ b⇓ aRb) q r
bindlem (~later ∞p) (later⇓ q) (later⇓ r) = {!!}
-}

-- two computations are weakly bisimilar, and one converges,
-- so does the other, and to the same value

subst~⇓ : ∀{A R}{t t' : Delay ∞ A}{n : A} → t ⇓ n → Delay R ∋ t ~ t' → t' ⇓
subst~⇓        now⇓       (~now a⇓ b⇓ aRb)          = _ , b⇓
subst~⇓ {R = R}(later⇓ p) (~now (later⇓ a⇓) b⇓ aRb) =
  subst~⇓ {R = R} p (~now a⇓ b⇓ aRb)
subst~⇓        (later⇓ p) (~later ∞p)               =
  let n' , p = subst~⇓ p (∞Delay_∋_~⟨_⟩~_.~force ∞p) in n' , later⇓ p

-- don't want to assume symmetry of R in ~trans, so...
subst~⇓' : ∀{A R}{t t' : Delay ∞ A}{n : A} → t' ⇓ n → Delay R ∋ t ~ t' → t ⇓
subst~⇓'         now⇓       (~now a⇓ b⇓ aRb)          = _  , a⇓
subst~⇓' {R = R} (later⇓ p) (~now a⇓ (later⇓ b⇓) aRb) =
  subst~⇓' {R = R} p (~now a⇓ b⇓ aRb)
subst~⇓'         (later⇓ p) (~later ∞p)               =
  let n' , p = subst~⇓' p (∞Delay_∋_~⟨_⟩~_.~force ∞p) in n' , later⇓ p


det~⇓ : ∀{A R}{t t' : Delay ∞ A}{n n' : A} →
        t ⇓ n → Delay R ∋ t ~ t' → t' ⇓ n' → R n n'
det~⇓ p (~now a⇓ b⇓ aRb) r with uniq⇓ p a⇓ | uniq⇓ b⇓ r
... | refl | refl = aRb
det~⇓ (later⇓ p) (~later ∞p) (later⇓ r) = det~⇓ p (∞Delay_∋_~⟨_⟩~_.~force ∞p) r




-- Reflexivity

~refl  : ∀ {i A R}(X : ∀{a} → R a a)(a? : Delay ∞ A) → Delay R ∋ a? ~⟨ i ⟩~ a?
~refl X a = ≈→~ (≈refl X a)

∞~refl : ∀ {i A R}(X : ∀{a} → R a a)(a∞ : ∞Delay ∞ A) → ∞Delay R ∋ a∞ ~⟨ i ⟩~ a∞
∞~refl X a∞ = ∞≈→~ (∞≈refl X a∞)

-- ~laterl seems essential here, and a reflexive R
~bind : ∀{A B R} → (∀ {a} → R a a) → (f : A → Delay ∞ B)
        {?a : Delay ∞ A}{a : A} → ?a ⇓ a → Delay R ∋ (?a >>= f) ~ f a
~bind X f {now x} now⇓ = ~refl X (f x)
~bind X f {later x} (later⇓ p) = ~laterl (~bind X f {force x} p)


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
  ∞Delay_∋_~⟨_⟩~_.~force (∞~sym X p) = ~sym X (∞Delay_∋_~⟨_⟩~_.~force p)

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
  ∞Delay_∋_~⟨_⟩~_.~force (∞~trans X p p') = ~trans X (∞Delay_∋_~⟨_⟩~_.~force p) (∞Delay_∋_~⟨_⟩~_.~force p')

bindlem : ∀{A B R i}{v : A} {f : A → Delay ∞ B} → Delay R ∋ f v ~ f v  →
         {v? : Delay ∞ A} →
          v? ⇓ v → Delay R ∋ v? >>= f ~⟨ i ⟩~ f v
bindlem X now⇓       = X
bindlem X (later⇓ p) = ~laterl (bindlem X p)

{-
mutual
  ~reflPER  : ∀ {i A}{R : A → A → Set}(X : ∀ {a a'} → R a a' → R a a)
              (a? : Delay ∞ A){b? : Delay ∞ A} → Delay R ∋ a? ~⟨ i ⟩~ b? →
              Delay R ∋ a? ~⟨ i ⟩~ a?
  ~reflPER X (now x) (~now now⇓ b⇓ aRb) = ~now now⇓ now⇓ (X aRb)
  ~reflPER X (later x){b?} (~now (later⇓ a⇓) b⇓ aRb) = {!!}
  ~reflPER X (later a∞) (~later ∞p) = ~later (∞~reflPER X a∞ ∞p)

  ∞~reflPER  : ∀ {i A}{R : A → A → Set}(X : ∀ {a a'} → R a a' → R a a)
              (a? : ∞Delay ∞ A){b? : ∞Delay ∞ A} → ∞Delay R ∋ a? ~⟨ i ⟩~ b? →
              ∞Delay R ∋ a? ~⟨ i ⟩~ a?
  ~force (∞~reflPER X a? p) = ~reflPER X (force a?) (~force p)
-}

open import Syntax

mutual
  Val∋_~⟨_⟩~_ = λ {Δ}{a} a? i b? → Val∋_~_ {i}{Δ}{a} a? b?
  NeVal∋_~⟨_⟩~_ = λ {Δ}{a} a? i b? → NeVal∋_~_ {i}{Δ}{a} a? b?
  Env∋_~⟨_⟩~_ = λ {Δ}{Γ} a? i b? → Env∋_~_ {i}{Δ}{Γ} a? b?

  data NeVal∋_~_ {i}{Δ} : {a : Ty}(a? b? : NeVal ∞ Δ a) → Set where
    ~var : ∀{a}{x : Var Δ a} → NeVal∋ var x ~ var x
    ~app : ∀{a b}{n n' : NeVal ∞ Δ (a ⇒ b)} → NeVal∋ n ~⟨ i ⟩~ n' →
           {v v' : Val ∞ Δ a} → Val∋ v ~⟨ i ⟩~ v' → NeVal∋ app n v ~ app n' v'
 
  data Env∋_~_ {i}{Δ} : ∀{Γ} → Env ∞ Δ Γ → Env ∞ Δ Γ → Set where
    ~ε : Env∋ ε ~ ε
    _~,_ : ∀{Γ a}{ρ ρ' : Env ∞ Δ Γ} → Env∋ ρ ~⟨ i ⟩~ ρ' →
           {v v' : Val ∞ Δ a} → Val∋ v ~⟨ i ⟩~ v' → Env∋ (ρ , v) ~ (ρ' , v')
    
  data Val∋_~_ {i}{Δ} : {a : Ty}(a? b? : Val ∞ Δ a) → Set where
    ~lam : ∀{Γ a b}{t : Tm (Γ , a) b}{ρ ρ' : Env ∞ Δ Γ} → Env∋ ρ ~⟨ i ⟩~ ρ' →
           Val∋ lam t ρ ~ lam t ρ'
    ~ne  : ∀{a}{n n' : NeVal ∞ Δ a} → NeVal∋ n ~⟨ i ⟩~ n' → Val∋ ne n ~ ne n'
    ~llater : ∀ {a}{a∞ : ∞Val ∞ Δ a}{b : Val ∞ Δ a}
              (eq : ∞Val∋ a∞ ~⟨ i ⟩~ ∞val b ) → Val∋ later a∞ ~ b
    ~rlater : ∀ {t}{a : Val ∞ Δ t}{b∞ : ∞Val ∞ Δ t}
              (eq : ∞Val∋ ∞val a ~⟨ i ⟩~ b∞) → Val∋ a ~ later b∞

  record ∞Val∋_~⟨_⟩~_ {Δ a} (a∞ : ∞Val ∞ Δ a) i (b∞ : ∞Val ∞ Δ a) : Set where
    coinductive
    constructor ∞~val
    field
      ~forceVal : {j : Size< i} → Val∋ ∞Val.force a∞ ~⟨ j ⟩~ ∞Val.force b∞

  ∞Val∋_~_ = λ {i}{Δ}{a} a? b? → ∞Val∋_~⟨_⟩~_ {Δ}{a} a? i b?
open ∞Val∋_~⟨_⟩~_ public

mutual
  ~symVal : ∀{i Δ a}{v v' : Val ∞ Δ a} →
            Val∋ v ~⟨ i ⟩~ v' → Val∋ v' ~⟨ i ⟩~ v
  ~symVal (~lam p)     = ~lam (~symEnv p)
  ~symVal (~ne p)      = ~ne (~symNeVal p)
  ~symVal (~llater p) = ~rlater (∞~symVal p)
  ~symVal (~rlater p) = ~llater (∞~symVal p)

  ∞~symVal : ∀{i Δ a}{v v' : ∞Val ∞ Δ a} →
            ∞Val∋ v ~⟨ i ⟩~ v' → ∞Val∋ v' ~⟨ i ⟩~ v
  ~forceVal (∞~symVal p) = ~symVal (~forceVal p)

  ~symNeVal : ∀{i Δ a}{n n' : NeVal ∞ Δ a} →
              NeVal∋ n ~⟨ i ⟩~ n' → NeVal∋ n' ~⟨ i ⟩~ n
  ~symNeVal ~var       = ~var
  ~symNeVal (~app p q) = ~app (~symNeVal p) (~symVal q)              

  ~symEnv : ∀{i Δ Γ}{ρ ρ' : Env ∞ Δ Γ} →
            Env∋ ρ ~⟨ i ⟩~ ρ' → Env∋ ρ' ~⟨ i ⟩~ ρ
  ~symEnv ~ε       = ~ε
  ~symEnv (p ~, q) = ~symEnv p ~, ~symVal q            
           
mutual
  ~transVal : ∀{i Δ a}{v v' v'' : Val ∞ Δ a} →
            Val∋ v ~⟨ ∞ ⟩~ v' → Val∋ v' ~⟨ ∞ ⟩~ v'' → Val∋ v ~⟨ i ⟩~ v''
  ~transVal (~lam p)    (~lam q)    = ~lam {!~transEnv p q!}
  ~transVal (~lam p)    (~rlater q) = ~rlater (∞~transVal (∞~val (~lam p)) q)
  ~transVal (~ne p)     (~ne q)     = ~ne {!~transNeVal p q!}
  ~transVal (~ne p)     (~rlater q) = ~rlater (∞~transVal (∞~val (~ne p)) q)
  ~transVal (~llater p) (~lam q)    = ~llater (∞~transVal p (∞~val (~lam q)))
  ~transVal (~llater p) (~ne q)     = ~llater (∞~transVal p (∞~val (~ne q)))
  ~transVal (~llater p) (~llater q) = {!!}
  ~transVal (~llater p) (~rlater q) = {!!}
  ~transVal (~rlater p) (~llater q) = {!!}
  ~transVal (~rlater p) (~rlater q) = {!!}            

  ∞~transVal : ∀{i Δ a}{v v' v'' : ∞Val ∞ Δ a} →
            ∞Val∋ v ~⟨ ∞ ⟩~ v' → ∞Val∋ v' ~⟨ ∞ ⟩~ v'' → ∞Val∋ v ~⟨ i ⟩~ v''
  ∞~transVal = {!!}
