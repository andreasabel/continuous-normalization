{-# OPTIONS --copatterns --sized-types #-}

module LocallyNamelessValues where

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
  weakVal (ne {j = j} x vs)  = ne (weakLvl x) (mapRSp (weakVal {i = j}) vs)
  weakVal (lam t ρ)          = lam t (weakEnv ρ)

-- Lifting.

var0 : ∀ Δ {a} → Val (Δ , a) a
var0 Δ = ne (newLvl Δ) ε

liftEnv : ∀ {Γ Δ a} → Env Δ Γ → Env (Δ , a) (Γ , a)
liftEnv {Δ = Δ} ρ = weakEnv ρ , var0 Δ

-- Call-by-value evaluation.

mutual
  〖_〗  : ∀ {i} {Γ : Cxt} {a : Ty} → Tm Γ a → {Δ : Cxt} → Env Δ Γ → Delay (Val Δ a) i
  〖 var x   〗 ρ = now (lookup x ρ)
  〖 abs t   〗 ρ = now (lam t ρ)
  〖 app t u 〗 ρ = apply* (〖 t 〗 ρ) (〖 u 〗 ρ)

  apply* : ∀ {i Δ a b} → Delay (Val Δ (a ⇒ b)) i → Delay (Val Δ a) i → Delay (Val Δ b) i
  apply* f⊥ v⊥ = apply =<<2 f⊥ , v⊥

  apply : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay (Val Δ b) i
  apply f v = later (∞apply f v)

  ∞apply : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → ∞Delay (Val Δ b) i
  force (∞apply (lam t ρ) v) = 〖 t 〗 (ρ , v)
  force (∞apply (ne x sp) v) = now (ne x (sp , v))

mutual
  readback : ∀ {i Γ a} → Val Γ a → Delay (βNf Γ a) i
  readback v = later (∞readback v)

  ∞readback : ∀ {i Γ a} → Val Γ a → ∞Delay (βNf Γ a) i
  force (∞readback (lam t ρ)) = lam  <$> (readback =<< 〖 t 〗 (liftEnv ρ))
  force (∞readback (ne x rs)) = ne (ind x) <$> mapRSpM readback rs

-- Monotonicity

mutual
  env≤ : ∀ {i Γ Δ Δ′} (η : Δ′ ≤ Δ) (ρ : Env {i = i} Δ Γ) → Env {i = i} Δ′ Γ
  env≤ η ε        = ε
  env≤ η (ρ , v)  = env≤ η ρ , val≤ η v

  val≤ : ∀ {i Δ Δ′ c} (η : Δ′ ≤ Δ) (v : Val {i = i} Δ c) → Val {i = i} Δ′ c
  val≤ η (ne {j = j} x vs)  = ne (lvl≤ η x) (mapRSp (val≤ {i = j} η) vs)
  val≤ η (lam t ρ)          = lam t (env≤ η ρ)

-- First functor law.

mutual
  env≤-id : ∀ {i Γ Δ} (ρ : Env {i} Δ Γ) → env≤ id ρ ≡ ρ
  env≤-id ε         = refl
  env≤-id (ρ , v)   = cong₂ _,_ (env≤-id ρ) (val≤-id v)

  val≤-id : ∀ {i Δ a} (v : Val {i} Δ a) → val≤ id v ≡ v
  val≤-id (ne x vs) = cong₂ ne refl (mapRSp-id val≤-id vs)
  val≤-id (lam t ρ) = cong (lam t) (env≤-id ρ)

{- SUBSUMED
  rsp≤-id : ∀ {i Δ a c} (vs : ValSpine {i} Δ a c) → mapRSp (val≤ id) vs ≡ vs
  rsp≤-id ε         = refl
  rsp≤-id (vs , v)  = cong₂ _,_ (rsp≤-id vs) (val≤-id v)
-}
mutual
  env≤-• : ∀ {i Γ Δ₁ Δ₂ Δ₃} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (ρ : Env {i} Δ₃ Γ) →
    env≤ η (env≤ η' ρ) ≡ env≤ (η • η') ρ
  env≤-• η η' ε       = refl
  env≤-• η η' (ρ , v) = cong₂ _,_ (env≤-• η η' ρ) (val≤-• η η' v)

  val≤-• : ∀ {i Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (v : Val {i} Δ₃ a) →
    val≤ η (val≤ η' v) ≡ val≤ (η • η') v
  val≤-• η η' (ne x vs) = cong₂ ne (lvl≤-• η η' x) (mapRSp-∘ (val≤-• η η') vs )
  val≤-• η η' (lam t ρ) = cong (lam t) (env≤-• η η' ρ)

-- Type interpretation

mutual
  V⟦_⟧ : (a : Ty) {Δ : Cxt} (v : Val Δ a) → Set
  V⟦ ★     ⟧ {Δ = Δ} v = ⊤
  V⟦ a ⇒ b ⟧ {Δ = Δ} f = {Γ : Cxt} (η : Γ ≤ Δ) →
    {u : Val Γ a} (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (apply (val≤ η f) u)

  C⟦_⟧ : (a : Ty) {Δ : Cxt} (v? : Delay (Val Δ a) ∞) → Set
  C⟦ a ⟧ v? = ∃ λ v → v? ⇓ v × V⟦ a ⟧ v

⟪_⟫ : (Γ : Cxt) {Δ : Cxt} (ρ : Env Δ Γ) → Set
⟪ ε ⟫     ε       = ⊤
⟪ Γ , a ⟫ (ρ , v) = ⟪ Γ ⟫ ρ × V⟦ a ⟧ v

-- Monotonicity

mutual
  V≤ : ∀ {Δ Δ′ a} (η : Δ′ ≤ Δ) {v : Val Δ a} (〖v〗 : V⟦ a ⟧ v) → V⟦ a ⟧ (val≤ η v)
  V≤ {a = ★}     η 〖v〗         = _
  V≤ {a = a ⇒ b} η {f}〖f〗 η′ {u} 〖u〗 =
    let v , v⇓ , 〖v〗 = 〖f〗 (η′ • η) 〖u〗
        v⇓'           = subst (λ f' → apply f' u ⇓ v) (sym (val≤-• η′ η f)) v⇓
    in  v , v⇓' , 〖v〗

  C≤ : ∀ {Δ Δ′ a} (η : Δ′ ≤ Δ) {v? : Delay (Val Δ a) ∞} (v⇓ : C⟦ a ⟧ v?) → C⟦ a ⟧ (val≤ η <$> v?)
  C≤ η (v , v⇓ , 〖v〗) = val≤ η v , map⇓ (val≤ η) v⇓ , V≤ η 〖v〗

CXT≤ : ∀ {Γ Δ Δ′} (η : Δ′ ≤ Δ) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → ⟪ Γ ⟫ (env≤ η ρ)
CXT≤ η ε       θ        = _
CXT≤ η (ρ , v) (θ , v⇓) = CXT≤ η ρ θ , V≤ η v⇓

-- Type soundness

〖var〗 : ∀ {Γ Δ a} (x : Var Γ a) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (now (lookup x ρ))
〖var〗 zero    (_ , v) (_ , v⇓) = v , now⇓ , v⇓
〖var〗 (suc x) (ρ , _) (θ , _ ) = 〖var〗 x ρ θ

sound-β : ∀ {Γ Δ a b} {t : Tm (Γ , a) b} {ρ : Env Δ Γ} {u : Val Δ a} →

  C⟦ b ⟧ (〖 t 〗 (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)

sound-β (v , v⇓ , ⟦v⟧) = v , later⇓ v⇓ , ⟦v⟧

〖abs〗 : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) →

  ({Δ′ : Cxt} (η : Δ′ ≤ Δ) {u : Val Δ′ a} (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (〖 t 〗 (env≤ η ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))

〖abs〗 t ρ θ ih = lam t ρ , now⇓ , λ η u⇓ → sound-β (ih η u⇓)

sound-app' : ∀ {Δ a b} (f : Val Δ (a ⇒ b)) →
  {u* : Delay (Val Δ a) _} {u : Val Δ a} (u⇓ : u* ⇓ u) →
  {v : Val Δ b} →  later (∞apply f u) ⇓ v → (u* >>= λ u → apply f u) ⇓ v
sound-app' f (later⇓ u⇓) h = later⇓ (sound-app' f u⇓ h)
sound-app' f  now⇓       h = h

sound-app : ∀ {Δ a b} →
  {f* : Delay (Val Δ (a ⇒ b)) _} {f : Val Δ (a ⇒ b)} (f⇓ : f* ⇓ f) →
  {u* : Delay (Val Δ a)       _} {u : Val Δ a}       (u⇓ : u* ⇓ u) →
  {v : Val Δ b} →  later (∞apply f u) ⇓ v → apply* f* u* ⇓ v
sound-app  (later⇓ f⇓) u⇓ h = later⇓ (sound-app f⇓ u⇓ h)
sound-app {f = f} now⇓ u⇓ h = sound-app' f u⇓ h


〖app〗 : ∀ {Δ a b} {f : Delay (Val Δ (a ⇒ b)) _} {u : Delay (Val Δ a) _} →

  C⟦ a ⇒ b ⟧ f → C⟦ a ⟧ u → C⟦ b ⟧ (apply* f u)

〖app〗 (f , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) =
  let v , v⇓ , ⟦v⟧ = ⟦f⟧ id ⟦u⟧
      v⇓'          = subst (λ f' → later (∞apply f' u) ⇓ _) (val≤-id f) v⇓
  in  v , sound-app f⇓ u⇓ v⇓' , ⟦v⟧

sound : ∀ {Γ Δ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (〖 t 〗 ρ)
sound (var x)   ρ θ = 〖var〗 x ρ θ
sound (abs t)   ρ θ = 〖abs〗 t ρ θ (λ {Δ′} η {u} u⇓ → sound t (env≤ η ρ , u) (CXT≤ η ρ θ , u⇓))
sound (app t u) ρ θ = 〖app〗 (sound t ρ θ) (sound u ρ θ)


{-
mutual
  data Nf (Γ : Cxt) : Ty → Set where
    lam : ∀{σ τ} → Nf (Γ , σ) τ → Nf Γ (σ ⇒ τ)
    ne  : Ne Γ ★  → Nf Γ ★

  data Ne (Γ : Cxt) : Ty → Set where
    var : ∀{σ} → Var Γ σ → Ne Γ σ
    app : ∀{σ τ} → Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ

mutual
  reify : ∀{Γ} σ → Val Γ σ → Nf Γ σ
  reify = ?

  reflect : ∀ {Γ} σ → Ne Γ σ → Val Γ σ
  reflect = ?
-}
