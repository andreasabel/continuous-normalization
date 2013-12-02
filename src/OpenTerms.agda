{-# OPTIONS --copatterns --sized-types #-}
-- {-# OPTIONS --show-implicit -v tc.cover.splittree:15 -v tc.cc:15 #-}

module OpenTerms where

open import Library
open import Term
open import Delay

-- Values and environments

mutual
  data Env (Δ : Cxt) : (Γ : Cxt) → Set where
    ε   : Env Δ ε
    _,_ : ∀ {Γ a} (ρ : Env Δ Γ) (v : Val Δ a) → Env Δ (Γ , a)

  data Val (Δ : Cxt) : (a : Ty) → Set where
    lam : ∀ {Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) → Val Δ (a ⇒ b)

lookup : {Γ Δ : Cxt} {a : Ty} → Var Γ a → Env Δ Γ → Val Δ a
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

-- Call-by-value evaluation.

mutual
  〖_〗  : ∀ {i}{Δ}{Γ : Cxt} {a : Ty} → Tm Γ a → Env Δ Γ → Delay (Val  Δ a) i
  〖 var x   〗 ρ = now (lookup x ρ)
  〖 abs t   〗 ρ = now (lam t ρ)
  〖 app t u 〗 ρ = apply* (〖 t 〗 ρ) (〖 u 〗 ρ)

  apply* : ∀ {Δ i a b} → Delay (Val Δ (a ⇒ b)) i → Delay (Val Δ a) i → Delay (Val Δ b) i
  apply* f⊥ v⊥ = f⊥ >>= λ f → v⊥ >>= λ v → apply f v

  apply : ∀ {Δ i a b} → Val Δ (a ⇒ b) → Val Δ a → Delay (Val Δ b) i
  apply f v = later (∞apply f v)

  ∞apply : ∀ {Δ i a b} → Val Δ (a ⇒ b) → Val Δ a → ∞Delay (Val Δ b) i
  force (∞apply (lam t ρ) v) = 〖 t 〗 (ρ , v)

β-expand : ∀ {Γ Δ a b} {t : Tm (Γ , a) b} {ρ : Env Δ Γ} {u : Val Δ a} {v : Val Δ b} →
  (h : 〖 t 〗 (ρ , u) ⇓ v) → apply (lam t ρ) u ⇓ v
β-expand h = later⇓ h

-- Type interpretation

mutual
  V⟦_⟧_ : ∀{Γ}(a : Ty) → Val Γ a → Set
  V⟦ ★     ⟧ v = ⊤
  V⟦ a ⇒ b ⟧ f = {u : Val _ a} (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (apply f u)

  C⟦_⟧_ : ∀{Γ}(a : Ty) → Delay (Val Γ a) ∞ → Set
  C⟦ a ⟧ x = ∃ λ v → x ⇓ v × V⟦ a ⟧ v


{-
  C⟦ ★     ⟧ v = v ⇓
  C⟦ a ⇒ b ⟧ f = (u : Delay (Val a) ∞) → ⟦ a ⟧ u → ⟦ b ⟧ (apply* f u)
-}


⟪_⟫_ : ∀{Δ}(Γ : Cxt) → Env Δ Γ → Set
⟪ ε ⟫     ε       = ⊤
⟪ Γ , a ⟫ (ρ , v) = ⟪ Γ ⟫ ρ × V⟦ a ⟧ v


-- Type soundness

〖var〗 : ∀ {Δ Γ a} (x : Var Γ a) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (now (lookup x ρ))
〖var〗 zero    (_ , v) (_ , v⇓) = v , now⇓ , v⇓
〖var〗 (suc x) (ρ , _) (θ , _ ) = 〖var〗 x ρ θ

sound-β : ∀ {Δ Γ a b} {t : Tm (Γ , a) b} {ρ : Env Δ Γ} {u : Val Δ a} →
          C⟦ b ⟧ (〖 t 〗 (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)
sound-β (v , v⇓ , ⟦v⟧) = v , β-expand v⇓ , ⟦v⟧

〖abs〗 : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) →
  ({u : Val Δ a} (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (〖 t 〗 (ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))
〖abs〗 t ρ θ ih = lam t ρ , now⇓ , λ u⇓ → sound-β (ih u⇓)

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
〖app〗 (f , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) = let v , v⇓                 , ⟦v⟧ = ⟦f⟧ ⟦u⟧
                                       in  v , sound-app f⇓ u⇓ v⇓ , ⟦v⟧

term : ∀ {Δ Γ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (〖 t 〗 ρ)
term (var x)   ρ θ = 〖var〗 x ρ θ
term (abs t)   ρ θ = 〖abs〗 t ρ θ (λ {u} u⇓ → term t (ρ , u) (θ , u⇓))
term (app t u) ρ θ = 〖app〗 (term t ρ θ) (term u ρ θ)

