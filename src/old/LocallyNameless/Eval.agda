{-# OPTIONS --copatterns --sized-types #-}

module LocallyNameless.Eval where

open import Library
open import Term
open import Delay
open import Spine
open import DBLevel

-- Values and environments

mutual
  data Env {i : Size} (Δ : Cxt) : (Γ : Cxt) → Set where
    ε   : Env Δ ε
    _,_ : ∀ {Γ a} (ρ : Env {i = i} Δ Γ) (v : Val {i = i} Δ a) → Env Δ (Γ , a)

  data Val {i : Size} (Δ : Cxt) : (a : Ty) → Set where
    ne  : ∀ {j : Size< i}{a c} (x : Lvl Δ a) (vs : ValSpine {i = j} Δ a c) → Val Δ c
    lam : ∀ {Γ a b}            (t : Tm (Γ , a) b) (ρ : Env {i = i} Δ Γ)    → Val Δ (a ⇒ b)

  ValSpine : {i : Size} (Δ : Cxt) (a c : Ty) → Set
  ValSpine {i = i} Δ = RSpine (Val {i = i} Δ)

lookup : ∀ {i Γ Δ a} → Var Γ a → Env {i = i} Δ Γ → Val {i = i} Δ a
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

-- Weakening.

mutual
  weakEnv : ∀ {i Γ Δ a} → Env {i = i} Δ Γ → Env {i = i} (Δ , a) Γ
  weakEnv ε        = ε
  weakEnv (ρ , v)  = weakEnv ρ , weakVal v

  weakVal : ∀ {i Δ a c} → Val {i = i} Δ c → Val {i = i} (Δ , a) c
  weakVal (ne {j = j} x vs)  = ne (weakLvl x) (weakValSpine {i = j} vs)
  weakVal (lam t ρ)          = lam t (weakEnv ρ)

  weakValSpine : ∀ {i Δ a b c} → ValSpine {i = i} Δ b c → ValSpine {i = i} (Δ , a) b c
  weakValSpine = mapRSp weakVal

-- Lifting.

var0 : ∀ {Δ a} → Val (Δ , a) a
var0 = ne (newLvl _) ε

liftEnv : ∀ {Γ Δ a} → Env Δ Γ → Env (Δ , a) (Γ , a)
liftEnv {Δ = Δ} ρ = weakEnv ρ , var0

-- Call-by-value evaluation.

mutual
  〖_〗  : ∀ {i} {Γ : Cxt} {a : Ty} → Tm Γ a → {Δ : Cxt} → Env Δ Γ → Delay i (Val Δ a)
  〖 var x   〗 ρ = now (lookup x ρ)
  〖 abs t   〗 ρ = now (lam t ρ)
  〖 app t u 〗 ρ = apply* (〖 t 〗 ρ) (〖 u 〗 ρ)

  apply* : ∀ {i Δ a b} → Delay i (Val Δ (a ⇒ b)) → Delay i (Val Δ a) → Delay i (Val Δ b)
  apply* f⊥ v⊥ = apply =<<2 f⊥ , v⊥

  apply : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay i (Val Δ b)
  apply f v = later (∞apply f v)

  ∞apply : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → ∞Delay i (Val Δ b)
  force (∞apply (lam t ρ) v) = 〖 t 〗 (ρ , v)
  force (∞apply (ne x sp) v) = now (ne x (sp , v))

-- β-quoting

mutual
  β-readback : ∀{i Γ a} → Val Γ a → Delay i (βNf Γ a)
  β-readback v = later (∞β-readback v)

  ∞β-readback : ∀{i Γ a} → Val Γ a → ∞Delay i (βNf Γ a)
  force (∞β-readback (lam t ρ)) = lam  <$> (β-readback =<< 〖 t 〗 (liftEnv ρ))
  force (∞β-readback (ne x rs)) = ne (ind x) <$> mapRSpM β-readback rs

-- βη-quoting

mutual

  readback : ∀{i j Γ a} → Val {j} Γ a → Delay i (Nf Γ a)
  readback {a = ★} (ne x vs) = ne (ind x) <$> readbackSpine vs
  readback {a = b ⇒ c}     v = later (∞readback v)

  ∞readback : ∀{i Γ b c} → Val Γ (b ⇒ c) → ∞Delay i (Nf Γ (b ⇒ c))
  force (∞readback v) = lam <$> (readback =<< apply (weakVal v) var0)

  readbackSpine : ∀{i j Γ a c} → ValSpine {j} Γ a c → Delay i (NfSpine Γ a c)
  readbackSpine = mapRSpM readback

------------------------------------------------------------------------

-- Monotonicity of values

mutual
  env≤ : ∀ {i Γ Δ Δ′} (η : Δ′ ≤ Δ) (ρ : Env {i = i} Δ Γ) → Env {i = i} Δ′ Γ
  env≤ η ε        = ε
  env≤ η (ρ , v)  = env≤ η ρ , val≤ η v

  val≤ : ∀ {i Γ Δ a} (η : Γ ≤ Δ) (v : Val {i = i} Δ a) → Val {i = i} Γ a
  val≤ η (ne {j = j} x vs)  = ne (lvl≤ η x) (valSpine≤ η vs)
  val≤ η (lam t ρ)          = lam t (env≤ η ρ)

  valSpine≤ : ∀ {i Γ Δ a c} (η : Γ ≤ Δ) (vs : ValSpine {i = i} Δ a c) → ValSpine {i = i} Γ a c
  valSpine≤ η vs = mapRSp (val≤ η) vs

-- First functor law.

mutual
  env≤-id : ∀ {i Γ Δ} (ρ : Env {i} Δ Γ) → env≤ id ρ ≡ ρ
  env≤-id ε         = refl
  env≤-id (ρ , v)   = cong₂ _,_ (env≤-id ρ) (val≤-id v)

  val≤-id : ∀ {i Δ a} (v : Val {i} Δ a) → val≤ id v ≡ v
  val≤-id (ne x vs) = cong₂ ne refl (valSpine≤-id vs)
  val≤-id (lam t ρ) = cong (lam t) (env≤-id ρ)

  valSpine≤-id : ∀ {i Δ a c} (vs : ValSpine {i} Δ a c) → valSpine≤ id vs ≡ vs
  valSpine≤-id = mapRSp-id val≤-id
{-
  valSpine≤-id ε         = refl
  valSpine≤-id (vs , v)  = cong₂ _,_ (valSpine≤-id vs) (val≤-id v)
-}

-- Second functor law.

mutual
  env≤-• : ∀ {i Γ Δ₁ Δ₂ Δ₃} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (ρ : Env {i} Δ₃ Γ) →
    env≤ η (env≤ η' ρ) ≡ env≤ (η • η') ρ
  env≤-• η η' ε       = refl
  env≤-• η η' (ρ , v) = cong₂ _,_ (env≤-• η η' ρ) (val≤-• η η' v)

  val≤-• : ∀ {i Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (v : Val {i} Δ₃ a) →
    val≤ η (val≤ η' v) ≡ val≤ (η • η') v
  val≤-• η η' (ne x vs) = cong₂ ne (lvl≤-• η η' x) (valSpine≤-• η η' vs)
  val≤-• η η' (lam t ρ) = cong (lam t) (env≤-• η η' ρ)

  valSpine≤-• : ∀ {i Δ₁ Δ₂ Δ₃ a c} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (vs : ValSpine {i} Δ₃ a c) →
    valSpine≤ η (valSpine≤ η' vs) ≡ valSpine≤ (η • η') vs
  valSpine≤-• η η' = mapRSp-∘ (val≤-• η η')

-- weakVal and weakEnv are special cases

mutual
  weakEnvLem : ∀ {i Γ Δ a} (ρ : Env {i = i} Δ Γ) → weakEnv ρ ≡ env≤ (weak {a = a} id) ρ
  weakEnvLem ε       = refl
  weakEnvLem (ρ , v) = cong₂ _,_ (weakEnvLem ρ) (weakValLem v)

  weakValLem : ∀ {i Δ a c} (v : Val {i = i} Δ c) → weakVal v ≡ val≤ (weak {a = a} id) v
  weakValLem (ne x vs) = cong₂ ne (weakLvlLem x) (weakValSpineLem vs)
  weakValLem (lam t ρ) = cong (lam t) (weakEnvLem ρ)

  weakValSpineLem : ∀ {i Δ a b c} (vs : ValSpine {i = i} Δ b c) → weakValSpine vs ≡ valSpine≤ (weak {a = a} id) vs
  weakValSpineLem ε = refl
  weakValSpineLem (vs , v) = cong₂ _,_ (weakValSpineLem vs) (weakValLem v)

-- Monotonicity for lookup

lookup≤ : ∀ {Γ Δ Δ' a} (x : Var Γ a) (ρ : Env Δ Γ) (η : Δ' ≤ Δ) →
  val≤ η (lookup x ρ) ≡ lookup x (env≤ η ρ)
lookup≤ zero    (ρ , v) η = refl
lookup≤ (suc x) (ρ , v) η = lookup≤ x ρ η

-- Congruence fore eval/apply

~apply* : ∀ {Δ a b} {f1? f2? : Delay ∞ (Val Δ (a ⇒ b))} {u1? u2? : Delay ∞ (Val Δ a)} →
  (eqf : f1? ~ f2?) (equ : u1? ~ u2?) → apply* f1? u1? ~ apply* f2? u2?
~apply* eqf equ = eqf ~>>= λ f → equ ~>>= λ u → ~refl _

-- Monotonicity for eval/apply

mutual

  eval≤ : ∀ {Γ Δ Δ' a} (t : Tm Γ a) (ρ : Env Δ Γ) (η : Δ' ≤ Δ) →
    (val≤ η <$> (〖 t 〗 ρ)) ~ 〖 t 〗 (env≤ η ρ)
  eval≤ (var x  ) ρ η rewrite lookup≤ x ρ η = ~now _
  eval≤ (abs t  ) ρ η = ~refl _
  eval≤ (app t u) ρ η = begin

      (val≤ η <$> apply* (〖 t 〗 ρ) (〖 u 〗 ρ))

    ~⟨ apply*≤ (〖 t 〗 ρ) (〖 u 〗 ρ) η ⟩

      apply* (val≤ η <$> 〖 t 〗 ρ) (val≤ η <$> 〖 u 〗 ρ)

    ~⟨ ~apply* (eval≤ t ρ η) (eval≤ u ρ η) ⟩

      apply* (〖 t 〗 (env≤ η ρ)) (〖 u 〗 (env≤ η ρ))

    ∎ where open ~-Reasoning

  apply*≤ : ∀ {Γ Δ a b} (f? : Delay ∞ (Val Δ (a ⇒ b))) (u? : Delay ∞ (Val Δ a)) (η : Γ ≤ Δ) →
    (val≤ η <$> apply* f? u?) ~ apply* (val≤ η <$> f?) (val≤ η <$> u?)
  apply*≤ f? u? η = begin

      val≤ η <$> apply* f? u?

    ≡⟨⟩

      val≤ η <$> apply =<<2 f? , u?

    ≡⟨⟩

      val≤ η <$> (f? >>= λ f → u? >>= apply f)

    ≡⟨⟩

      ((f? >>= (λ f → u? >>= apply f)) >>= λ v → return (val≤ η v))

    ~⟨ bind-assoc f? ⟩

      (f? >>= λ f → (u? >>= apply f) >>= λ v → return (val≤ η v))

    ~⟨ (f? >>=r λ f → bind-assoc u?) ⟩

      (f? >>= λ f → u? >>= λ u → apply f u >>= λ v → return (val≤ η v))

    ≡⟨⟩

      (f? >>= λ f → u? >>= λ u → val≤ η <$> apply f u)

    ~⟨ (f? >>=r λ f → u? >>=r λ u → apply≤ f u η) ⟩

      (f? >>= λ f → u? >>= λ u → apply (val≤ η f) (val≤ η u))

    ~⟨ ~sym (bind-assoc f?)  ⟩

      ((f? >>= λ f → return (val≤ η f)) >>= λ f' → u? >>= λ u → apply f' (val≤ η u))

    ≡⟨⟩

      ((val≤ η <$> f?) >>= λ f' → u? >>= λ u → apply f' (val≤ η u))

    ~⟨ ((val≤ η <$> f?) >>=r λ f' → ~sym (bind-assoc u?)) ⟩

      ((val≤ η <$> f?) >>= λ f' → (u? >>= λ u → return (val≤ η u)) >>= λ u' → apply f' u')

    ≡⟨⟩

      ((val≤ η <$> f?) >>= λ f' → (val≤ η <$> u?) >>= λ u' → apply f' u')

    ≡⟨⟩

      apply =<<2 (val≤ η <$> f?) , (val≤ η <$> u?)

    ≡⟨⟩

      apply* (val≤ η <$> f?) (val≤ η <$> u?)

    ∎ where open ~-Reasoning

  apply≤ : ∀ {Γ Δ a b} (f : Val {∞} Δ (a ⇒ b)) (v : Val {∞} Δ a) (η : Γ ≤ Δ) →
    (val≤ η <$> apply f v) ~ apply (val≤ η f) (val≤ η v)
  apply≤ f v η = ~later (∞apply≤ f v η)

  ∞apply≤ : ∀ {Γ Δ a b} (f : Val {∞} Δ (a ⇒ b)) (v : Val {∞} Δ a) (η : Γ ≤ Δ) →
    (val≤ η ∞<$> ∞apply f v) ∞~ ∞apply (val≤ η f) (val≤ η v)
  ∞apply≤ f v η = {!!}
