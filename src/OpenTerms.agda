{-# OPTIONS --copatterns --sized-types #-}
-- {-# OPTIONS --show-implicit -v tc.cover.splittree:15 -v tc.cc:15 #-}

module OpenTerms where

open import Library
open import Term
open import Delay

-- Values and environments

mutual
  data Env : (Γ : Cxt) → Set where
    ε   : Env ε
    _,_ : ∀ {Γ a} (ρ : Env Γ) (v : Val a) → Env (Γ , a)

  data Val : (a : Ty) → Set where
    lam : ∀ {Γ a b} (t : Tm (Γ , a) b) (ρ : Env Γ) → Val (a ⇒ b)

lookup : {Γ : Cxt} {a : Ty} → Var Γ a → Env Γ → Val a
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

-- Call-by-value evaluation.

mutual
  〖_〗  : ∀ {i} {Γ : Cxt} {a : Ty} → Tm Γ a → Env Γ → Delay (Val a) i
  〖 var x   〗 ρ = now (lookup x ρ)
  〖 abs t   〗 ρ = now (lam t ρ)
  〖 app t u 〗 ρ = apply* (〖 t 〗 ρ) (〖 u 〗 ρ)

  apply* : ∀ {i a b} → Delay (Val (a ⇒ b)) i → Delay (Val a) i → Delay (Val b) i
  apply* f⊥ v⊥ = f⊥ >>= λ f → v⊥ >>= λ v → apply f v

  apply : ∀ {i a b} → Val (a ⇒ b) → Val a → Delay (Val b) i
  apply f v = later (∞apply f v)

  ∞apply : ∀ {i a b} → Val (a ⇒ b) → Val a → ∞Delay (Val b) i
  force (∞apply (lam t ρ) v) = 〖 t 〗 (ρ , v)

β-expand : ∀ {Γ a b} {t : Tm (Γ , a) b} {ρ : Env Γ} {u : Val a} {v : Val b} →
  (h : 〖 t 〗 (ρ , u) ⇓ v) → apply (lam t ρ) u ⇓ v
β-expand h = later⇓ h

-- Type interpretation

mutual
  V⟦_⟧_ : (a : Ty) → Val a → Set
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
