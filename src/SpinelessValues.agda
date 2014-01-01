{-# OPTIONS --copatterns --sized-types #-}

module SpinelessValues where

open import Library

open import Term hiding (Nf; module Nf)
open import Spine
open import Delay

data Ne (T : Cxt → Ty → Set)(Γ : Cxt) : Ty → Set where
  var : ∀{a} → Var Γ a → Ne T Γ a
  app : ∀{a b} → Ne T Γ (a ⇒ b) → T Γ a → Ne T Γ b

data Nf (Γ : Cxt) : Ty → Set where
  lam : ∀{a b}(n : Nf (Γ , a) b) → Nf Γ (a ⇒ b)
  ne  : Ne Nf Γ ★ → Nf Γ ★

-- Values and environments
mutual
  data Env (Δ : Cxt) : (Γ : Cxt) → Set where
    ε   : Env Δ ε
    _,_ : ∀ {Γ a} (ρ : Env Δ Γ) (v : Val Δ a) → Env Δ (Γ , a)

  data Val (Δ : Cxt) : (a : Ty) → Set where
    ne  : ∀{a} → Ne Val Δ a → Val Δ a
    lam : ∀{Γ a b}(t : Tm (Γ , a) b)(ρ : Env Δ Γ) → Val Δ (a ⇒ b)

lookup : ∀ {Γ Δ a} → Var Γ a → Env Δ Γ → Val Δ a
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ


mutual
  val≤ : ∀{Γ Δ} → Γ ≤ Δ → ∀{a} → Val Δ a → Val Γ a
  val≤ α (ne t) = ne (nev≤ α t)
  val≤ α (lam t ρ)  = lam t (env≤ α ρ)

  env≤ : ∀{Γ Δ E} →  Δ ≤ Γ → Env Γ E → Env Δ E
  env≤ α ε       = ε
  env≤ α (ρ , v) = env≤ α ρ , val≤ α v

  nev≤ : ∀{Γ Δ} → Γ ≤ Δ → ∀{a} → Ne Val Δ a → Ne Val Γ a
  nev≤ α (var x)   = var (var≤ α x)
  nev≤ α (app t u) = app (nev≤ α t) (val≤ α u)

weakVal : ∀ {Δ a c} → Val Δ c → Val (Δ , a) c
weakVal = val≤ (weak id)


mutual
  eval : ∀{i Γ Δ a} → Tm Γ a → Env Δ Γ → Delay (Val Δ a) i
  eval (var x)   γ = now (lookup x γ)
  eval (abs t)   γ = now (lam t γ)
  eval (app t u) γ = apply* (eval t γ) (eval u γ)

  apply* : ∀{i Γ a b} → 
    Delay (Val Γ (a ⇒ b)) (i) → Delay (Val Γ a) (i) → Delay (Val Γ b) (i)
  apply* f v = apply =<<2 f , v

  apply : ∀{i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay (Val Δ b) i
  apply f v = later (∞apply f v)

  ∞apply : ∀{i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → ∞Delay (Val Δ b) i
  force (∞apply (ne x)    v) = now (ne (app x v))
  force (∞apply (lam t ρ) v) = eval t (ρ , v)

mutual
  readback : ∀{i Γ} a → Val Γ a → Delay (Nf Γ a) i
  readback a v = later (∞readback a v)

  ∞readback : ∀{i Γ} a → Val Γ a → ∞Delay (Nf Γ a) i
  force (∞readback ★       (ne t)) = ne <$> nereadback t
  force (∞readback (a ⇒ b) v     ) = 
    lam <$> (readback b =<< apply (weakVal v) (ne (var zero)))

  nereadback : ∀{i Γ a} → Ne Val Γ a → Delay (Ne Nf Γ a) i
  nereadback t = later (∞nereadback t)

  ∞nereadback : ∀{i Γ a} → Ne Val Γ a → ∞Delay (Ne Nf Γ a) i
  force (∞nereadback (var x)  ) = now (var x)
  force (∞nereadback (app t u)) = 
    nereadback t >>= λ f → readback _ u >>= λ v → now (app f v) 

