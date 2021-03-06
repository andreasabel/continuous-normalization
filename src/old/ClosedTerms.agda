{-# OPTIONS --copatterns --sized-types #-}
-- {-# OPTIONS --show-implicit -v tc.cover.splittree:15 -v tc.cc:15 #-}

module ClosedTerms where

open import Library
open import Spine
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
  〖_〗  : ∀ {i} {Γ : Cxt} {a : Ty} → Tm Γ a → Env Γ → Delay i (Val a)
  〖 var x   〗 ρ = now (lookup x ρ)
  〖 abs t   〗 ρ = now (lam t ρ)
  〖 app t u 〗 ρ = apply* (〖 t 〗 ρ) (〖 u 〗 ρ)

  apply* : ∀ {i a b} → Delay i (Val (a ⇒ b)) → Delay i (Val a) → Delay i (Val b)
  apply* f⊥ v⊥ = f⊥ >>= λ f → v⊥ >>= λ v → apply f v

  apply : ∀ {i a b} → Val (a ⇒ b) → Val a → Delay i (Val b)
  apply f v = later (∞apply f v)

  ∞apply : ∀ {i a b} → Val (a ⇒ b) → Val a → ∞Delay i (Val b)
  force (∞apply (lam t ρ) v) = 〖 t 〗 (ρ , v)

β-expand : ∀ {Γ a b} {t : Tm (Γ , a) b} {ρ : Env Γ} {u : Val a} {v : Val b} →
  (h : 〖 t 〗 (ρ , u) ⇓ v) → apply (lam t ρ) u ⇓ v
β-expand h = later⇓ h

-- Type interpretation / strong computability

mutual
  -- strongly computable value
  V⟦_⟧_ : (a : Ty) → Val a → Set
  V⟦ ★     ⟧ v = ⊤
  V⟦ a ⇒ b ⟧ f = {u : Val a} (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (apply f u)

  -- strongly computable delayed value:
  -- x is strongly computable if there is exists a v such that x
  -- converges to v and v is strongly computable
  C⟦_⟧_ : (a : Ty) → Delay ∞ (Val a) → Set
  C⟦ a ⟧ x = ∃ λ v → x ⇓ v × V⟦ a ⟧ v

-- strongly computable environment
⟪_⟫_ : (Γ : Cxt) → Env Γ → Set
⟪ ε ⟫     ε       = ⊤
⟪ Γ , a ⟫ (ρ , v) = ⟪ Γ ⟫ ρ × V⟦ a ⟧ v

-- Type soundness / termination

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
             {u* : Delay _ (Val a)} {u : Val a} (u⇓ : u* ⇓ u) →
             {v : Val b} →  later (∞apply f u) ⇓ v → (u* >>= λ u → apply f u) ⇓ v
sound-app' f (later⇓ u⇓) h = later⇓ (sound-app' f u⇓ h)
sound-app' f  now⇓       h = h

sound-app : ∀ {a b} →
            {f* : Delay _ (Val (a ⇒ b))} {f : Val (a ⇒ b)} (f⇓ : f* ⇓ f) →
            {u* : Delay _ (Val a)      } {u : Val a}       (u⇓ : u* ⇓ u) →
            {v : Val b} →  later (∞apply f u) ⇓ v → apply* f* u* ⇓ v
sound-app  (later⇓ f⇓) u⇓ h = later⇓ (sound-app f⇓ u⇓ h)
sound-app {f = f} now⇓ u⇓ h = sound-app' f u⇓ h

〖app〗 : ∀ {a b} {f : Delay _ (Val (a ⇒ b))} {u : Delay _ (Val a)} →
          C⟦ a ⇒ b ⟧ f → C⟦ a ⟧ u → C⟦ b ⟧ (apply* f u)
〖app〗 (f , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) = let v , v⇓                 , ⟦v⟧ = ⟦f⟧ ⟦u⟧
                                       in  v , sound-app f⇓ u⇓ v⇓ , ⟦v⟧
-- termination
term : ∀ {Γ a} (t : Tm Γ a) (ρ : Env Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (〖 t 〗 ρ)
term (var x)   ρ θ = 〖var〗 x ρ θ
term (abs t)   ρ θ = 〖abs〗 t ρ θ (λ {u} u⇓ → term t (ρ , u) (θ , u⇓))
term (app t u) ρ θ = 〖app〗 (term t ρ θ) (term u ρ θ)

norm : ∀{Γ a} (t : Tm Γ a) (ρ : Env Γ) (θ : ⟪ Γ ⟫ ρ) → Val a
norm t ρ Θ = fst (term t ρ Θ)
