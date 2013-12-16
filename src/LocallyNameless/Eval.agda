{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --show-implicit #-}

module LocallyNameless.Eval where

open import Library
open import Spine
open import Term
open import Delay
open import DBLevel
open import LocallyNameless.Values

-- Lifting.

var0 : ∀ {Δ a} → Val (Δ , a) a
var0 = ne (newLvl _) ε

liftEnv : ∀ {Γ Δ a} → Env Δ Γ → Env (Δ , a) (Γ , a)
liftEnv {Δ = Δ} ρ = weakEnv ρ , var0

-- Call-by-value evaluation.

mutual
  〖_〗  : ∀ {i} {Γ : Cxt} {a : Ty} → Tm Γ a → {Δ : Cxt} → Env Δ Γ → Delay (Val Δ a) i
  〖 var x   〗 ρ = now (lookup x ρ)
  〖 abs t   〗 ρ = now (lam t ρ)
  〖 app t u 〗 ρ = apply* (〖 t 〗 ρ) (〖 u 〗 ρ)

  apply* : ∀ {i Δ a b} → Delay (Val Δ (a ⇒ b)) i → Delay (Val Δ a) i → Delay (Val Δ b) i
  apply* f⊥ v⊥ = apply =<<2 f⊥ , v⊥

  apply : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay (Val Δ b) i
  apply (ne x sp) v = now (ne x (sp , v))
  apply (lam t ρ) v = later (beta t ρ v)

  beta : ∀ {i Γ a b} (t : Tm (Γ , a) b)
    {Δ : Cxt} (ρ : Env Δ Γ) (v : Val Δ a) → ∞Delay (Val Δ b) i
  force (beta t ρ v) = 〖 t 〗 (ρ , v)

-- β-quoting

mutual
  β-readback : ∀{i Γ a} → Val Γ a → Delay (βNf Γ a) i
  β-readback v = later (∞β-readback v)

  ∞β-readback : ∀{i Γ a} → Val Γ a → ∞Delay (βNf Γ a) i
  force (∞β-readback (lam t ρ)) = lam  <$> (β-readback =<< 〖 t 〗 (liftEnv ρ))
  force (∞β-readback (ne x rs)) = ne (ind x) <$> mapRSpM β-readback rs

-- βη-quoting

mutual

  readback : ∀{i j Γ a} → Val {j} Γ a → Delay (Nf Γ a) i
  readback {a = ★} (ne x vs) = ne (ind x) <$> readbackSpine vs
  readback {a = b ⇒ c}     v = later (∞readback v)

  ∞readback : ∀{i Γ b c} → Val Γ (b ⇒ c) → ∞Delay (Nf Γ (b ⇒ c)) i
  force (∞readback v) = lam <$> (readback =<< apply (weakVal v) var0)

  readbackSpine : ∀{i j Γ a c} → ValSpine {j} Γ a c → Delay (NfSpine Γ a c) i
  readbackSpine = mapRSpM readback

------------------------------------------------------------------------

-- Congruence fore eval/apply

~apply* : ∀ {i Δ a b} {f1? f2? : Delay (Val Δ (a ⇒ b)) ∞} {u1? u2? : Delay (Val Δ a) ∞} →
  (eqf : _~_ {i} f1? f2?) (equ : _~_ {i} u1? u2?) →
  _~_ {i} (apply* f1? u1?) (apply* f2? u2?)
~apply* eqf equ = eqf ~>>= λ f → equ ~>>= λ u → ~refl _

-- Monotonicity for eval/apply

mutual

  eval≤ : ∀ {i Γ Δ Δ' a} (t : Tm Γ a) (ρ : Env Δ Γ) (η : Δ' ≤ Δ) →
    _~_ {i} (val≤ η <$> (〖 t 〗 ρ)) (〖 t 〗 (env≤ η ρ))
  eval≤ (var x  ) ρ η rewrite lookup≤ x ρ η = ~now _
  eval≤ (abs t  ) ρ η = ~refl _
  eval≤ (app t u) ρ η = begin

      (val≤ η <$> apply* (〖 t 〗 ρ) (〖 u 〗 ρ))

    ~⟨ apply*≤ (〖 t 〗 ρ) (〖 u 〗 ρ) η ⟩

      apply* (val≤ η <$> 〖 t 〗 ρ) (val≤ η <$> 〖 u 〗 ρ)

    ~⟨ ~apply* (eval≤ t ρ η) (eval≤ u ρ η) ⟩

      apply* (〖 t 〗 (env≤ η ρ)) (〖 u 〗 (env≤ η ρ))

    ∎ where open ~-Reasoning

  apply*≤ : ∀ {i Γ Δ a b} (f? : Delay (Val Δ (a ⇒ b)) ∞) (u? : Delay (Val Δ a) ∞) (η : Γ ≤ Δ) →
    _~_ {i} (val≤ η <$> apply* f? u?) (apply* (val≤ η <$> f?) (val≤ η <$> u?))
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

  apply≤ : ∀ {i Γ Δ a b} (f : Val Δ (a ⇒ b)) (v : Val Δ a) (η : Γ ≤ Δ) →
    _~_ {i} (val≤ {∞} η <$> apply f v) (apply (val≤ {∞} η f) (val≤ {∞} η v))
  apply≤ (ne x vs) v η = {!~refl _!}  -- PROBLEM with sized types
  apply≤ (lam t ρ) v η = ~later (beta≤ t ρ v η)

  beta≤ : ∀ {i Γ a b} (t : Tm (Γ , a) b)
    {Δ}  (ρ : Env Δ Γ) (v : Val Δ a) {Δ'} (η : Δ' ≤ Δ) →
     _∞~_ {i} (val≤ η ∞<$> beta t ρ v) (beta t (env≤ {∞} η ρ) (val≤ {∞} η v))
  ~force (beta≤ t ρ v η) = eval≤ t (ρ , v) η
