{-# OPTIONS --copatterns --sized-types #-}

module TypedValues where

open import Level using () renaming (zero to lzero; suc to lsuc)
open import Size

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Term
open import Delay
open import Spine

-- Values and environments

mutual
  data Env {i : Size} (Δ : Cxt) : (Γ : Cxt) → Set where
    ε   : Env Δ ε
    _,_ : ∀ {Γ a} (ρ : Env {i = i} Δ Γ) (v : Val {i = i} Δ a) → Env Δ (Γ , a)

  data Val {i : Size} (Δ : Cxt) : (a : Ty) → Set where
    ne  : ∀ {j : Size< i}{a c} (x : Var Δ a) (vs : ValSpine {i = j} Δ a c) → Val Δ c
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
  weakVal (ne {j = j} x vs)  = ne (suc x) (mapRSp (weakVal {i = j}) vs)
  weakVal (lam t ρ)          = lam t (weakEnv ρ)

-- Lifting.

var0 : ∀ {Δ a} → Val (Δ , a) a
var0 = ne zero ε

liftEnv : ∀ {Γ Δ a} → Env Δ Γ → Env (Δ , a) (Γ , a)
liftEnv ρ = weakEnv ρ , var0

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

β-expand : ∀ {Γ Δ a b} {t : Tm (Γ , a) b} {ρ : Env Δ Γ} {u : Val Δ a} {v : Val Δ b} →
  (h : 〖 t 〗 (ρ , u) ⇓ v) → apply (lam t ρ) u ⇓ v
β-expand h = later⇓ h

mutual
  readback : ∀ {i Γ a} → Val Γ a → Delay (βNf Γ a) i
  readback v = later (∞readback v)

  ∞readback : ∀ {i Γ a} → Val Γ a → ∞Delay (βNf Γ a) i
  force (∞readback (lam t ρ)) = lam  <$> (readback =<< 〖 t 〗 (liftEnv ρ))
  force (∞readback (ne x rs)) = ne x <$> mapRSpM readback rs

{-

-- Type interpretation

mutual
  V⟦_⟧_  : (a : Ty) → Val Δ a → Set
  V⟦ ★     ⟧ v = ⊤
  V⟦ a ⇒ b ⟧ f = {u : Val a} (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (apply f u)

  C⟦_⟧_ : (a : Ty) → Delay (Val a) ∞ → Set
  C⟦ a ⟧ x = ∃ λ v → x ⇓ v × V⟦ a ⟧ v

{-
  C⟦ ★     ⟧ v = v ⇓
  C⟦ a ⇒ b ⟧ f = (u : Delay (Val a) ∞) → ⟦ a ⟧ u → ⟦ b ⟧ (apply* f u)
-}

⟪_⟫_ : (Γ : Cxt) → Env Γ → Set
⟪ ε ⟫     ε       = ⊤
⟪ Γ , a ⟫ (ρ , v) = ⟪ Γ ⟫ ρ × V⟦ a ⟧ v

-- Type soundness

〖var〗 : ∀ {Γ a} (x : Var Γ a) (ρ : Env Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (now (lookup x ρ))
〖var〗 zero    (_ , v) (_ , v⇓) = v , now⇓ , v⇓
〖var〗 (suc x) (ρ , _) (θ , _ ) = 〖var〗 x ρ θ

sound-β : ∀ {Γ a b} {t : Tm (Γ , a) b} {ρ : Env Γ} {u : Val a} →

  C⟦ b ⟧ (〖 t 〗 (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)

sound-β (v , v⇓ , ⟦v⟧) = v , β-expand v⇓ , ⟦v⟧


〖abs〗 : ∀ {Γ a b} (t : Tm (Γ , a) b) (ρ : Env Γ) (θ : ⟪ Γ ⟫ ρ) →

  ({u : Val a} (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (〖 t 〗 (ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))

〖abs〗 t ρ θ ih = lam t ρ , now⇓ , λ u⇓ → sound-β (ih u⇓)

sound-app' : ∀ {a b} (f : Val (a ⇒ b)) →
  {u* : Delay (Val a) _} {u : Val a} (u⇓ : u* ⇓ u) →
  {v : Val b} →  later (∞apply f u) ⇓ v → (u* >>= λ u → apply f u) ⇓ v
sound-app' f (later⇓ u⇓) h = later⇓ (sound-app' f u⇓ h)
sound-app' f  now⇓       h = h

sound-app : ∀ {a b} →
  {f* : Delay (Val (a ⇒ b)) _} {f : Val (a ⇒ b)} (f⇓ : f* ⇓ f) →
  {u* : Delay (Val a)       _} {u : Val a}       (u⇓ : u* ⇓ u) →
  {v : Val b} →  later (∞apply f u) ⇓ v → apply* f* u* ⇓ v
sound-app  (later⇓ f⇓) u⇓ h = later⇓ (sound-app f⇓ u⇓ h)
sound-app {f = f} now⇓ u⇓ h = sound-app' f u⇓ h

〖app〗 : ∀ {a b} {f : Delay (Val (a ⇒ b)) _} {u : Delay (Val a) _} →

  C⟦ a ⇒ b ⟧ f → C⟦ a ⟧ u → C⟦ b ⟧ (apply* f u)

〖app〗 (f , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) = let v , v⇓                 , ⟦v⟧ = ⟦f⟧ ⟦u⟧
                                       in  v , sound-app f⇓ u⇓ v⇓ , ⟦v⟧

norm : ∀ {Γ a} (t : Tm Γ a) (ρ : Env Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (〖 t 〗 ρ)
norm (var x)   ρ θ = 〖var〗 x ρ θ
norm (abs t)   ρ θ = 〖abs〗 t ρ θ (λ {u} u⇓ → norm t (ρ , u) (θ , u⇓))
norm (app t u) ρ θ = 〖app〗 (norm t ρ θ) (norm u ρ θ)

-}
