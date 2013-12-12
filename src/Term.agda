{-# OPTIONS --sized-types #-}

-- Syntax: Types, terms and contexts.

module Term where

open import Library
open import Spine

-- Variables and terms.

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀ {Γ a}                 → Var (Γ , a) a
  suc  : ∀ {Γ a b} (x : Var Γ a) → Var (Γ , b) a

data Tm (Γ : Cxt) : (a : Ty) → Set where
  var : ∀ {a}   (x : Var Γ a)                   → Tm Γ a
  abs : ∀ {a b} (t : Tm (Γ , a) b)              → Tm Γ (a ⇒ b)
  app : ∀ {a b} (t : Tm Γ (a ⇒ b)) (u : Tm Γ a) → Tm Γ b

-- β-normal forms.

data βNf {i : Size} (Γ : Cxt) : Ty → Set where
  lam : ∀ {j : Size< i} {a b} (n : βNf {j} (Γ , a) b)                      → βNf Γ (a ⇒ b)
  ne  : ∀ {j : Size< i} {a b} (x : Var Γ a) (ns : RSpine (βNf {j} Γ) a b)  → βNf Γ b

-- η-long β-normal forms.

mutual
  data Nf {i : Size} (Γ : Cxt) : Ty → Set where
    lam : ∀ {j : Size< i} {a b} (n : Nf {j} (Γ , a) b)                  → Nf Γ (a ⇒ b)
    ne  : ∀ {j : Size< i} {a}   (x : Var Γ a) (ns : NfSpine {j} Γ a ★)  → Nf Γ ★

  NfSpine : {i : Size} (Γ : Cxt) (a c : Ty) → Set
  NfSpine {i} Γ a c = RSpine (Nf {i} Γ) a c

-- Additional stuff for contexts.
-- order preserving embeddings

data _≤_ : (Γ Δ : Cxt) → Set where
  id   : ∀ {Γ} → Γ ≤ Γ
  weak : ∀ {Γ Δ a} → Γ ≤ Δ → (Γ , a) ≤ Δ
  lift : ∀ {Γ Δ a} → Γ ≤ Δ → (Γ , a) ≤ (Δ , a)

-- Smart lift, preserves id.

lift' : ∀ {Γ Δ a} → Γ ≤ Δ → (Γ , a) ≤ (Δ , a)
lift' id = id
lift' η  = lift η

-- Composition

_•_ : ∀ {Γ Δ Δ'} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') → Γ ≤ Δ'
id     • η'      = η'
weak η • η'      = weak (η • η')
lift η • id      = lift η
lift η • weak η' = weak (η • η')
lift η • lift η' = lift (η • η')

η•id :  ∀ {Γ Δ} (η : Γ ≤ Δ) → η • id ≡ η
η•id id       = refl
η•id (weak η) = cong weak (η•id η)
η•id (lift η) = refl

lift'-• : ∀ {Γ Δ Δ' a} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') →
  lift' {a = a} η • lift' η' ≡ lift' (η • η')
lift'-• id       η'        = refl
lift'-• (weak η) id        = cong (lift ∘ weak) (sym (η•id η))
lift'-• (weak η) (weak η') = refl
lift'-• (weak η) (lift η') = refl
lift'-• (lift η) id        = refl
lift'-• (lift η) (weak η') = refl
lift'-• (lift η) (lift η') = refl

-- Monotonicity / map for variables

var≤ : ∀ {Γ Δ a} → (η : Γ ≤ Δ) (x : Var Δ a) → Var Γ a
var≤ id        x      = x
var≤ (weak η)  x      = suc (var≤ η x)
var≤ (lift η)  zero   = zero
var≤ (lift η) (suc x) = suc (var≤ η x)

-- First functor law.

var≤-id : ∀ {Γ a} (x : Var Γ a) → var≤ id x ≡ x
var≤-id x = refl

-- Second functor law.

var≤-• : ∀ {Γ₁ Γ₂ Γ₃ a} (η : Γ₁ ≤ Γ₂) (η' : Γ₂ ≤ Γ₃) (x : Var Γ₃ a) →
  var≤ η (var≤ η' x) ≡ var≤ (η • η') x
var≤-• id       η'        x       = refl
var≤-• (weak η) η'        x       = cong suc (var≤-• η η' x)
var≤-• (lift η) id        x       = refl
var≤-• (lift η) (weak η') x       = cong suc (var≤-• η η' x)
var≤-• (lift η) (lift η') zero    = refl
var≤-• (lift η) (lift η') (suc x) = cong suc (var≤-• η η' x)

-- Length.

len : Cxt → ℕ
len ε       = 0
len (Γ , _) = 1 + len Γ

-- Monotonicity for long normal forms.

mutual
  nf≤ : ∀ {i Γ Δ a} (η : Γ ≤ Δ) (t : Nf {i} Δ a) → Nf {i} Γ a
  nf≤ η (lam t)   = lam (nf≤ (lift' η) t)
  nf≤ η (ne x ts) = ne (var≤ η x) (nfSpine≤ η ts)

  nfSpine≤ : ∀ {i Γ Δ a c} (η : Γ ≤ Δ) (ts : NfSpine {i} Δ a c) → NfSpine {i} Γ a c
  nfSpine≤ η ts = mapRSp (nf≤ η) ts

mutual
  nf≤-id : ∀ {i Γ a} (n : Nf {i} Γ a) → nf≤ id n ≡ n
  nf≤-id (lam n)   = cong lam (nf≤-id n)
  nf≤-id (ne x ns) = cong₂ ne (var≤-id x) (nfSpine≤-id ns)

  nfSpine≤-id : ∀ {i Γ a c} (ns : NfSpine {i} Γ a c) → nfSpine≤ id ns ≡ ns
  nfSpine≤-id ε        = refl
  nfSpine≤-id (ns , n) = cong₂ _,_ (nfSpine≤-id ns) (nf≤-id n)

mutual
  nf≤-• : ∀ {i Γ₁ Γ₂ Γ₃ a} (η : Γ₁ ≤ Γ₂) (η' : Γ₂ ≤ Γ₃) (n : Nf {i} Γ₃ a) →

    nf≤ η (nf≤ η' n) ≡ nf≤ (η • η') n

  nf≤-• η η' (lam n)   = cong lam
    (subst (λ z → nf≤ (lift' η) (nf≤ (lift' η') n) ≡ nf≤ z n)
           (lift'-• η η')
           (nf≤-• (lift' η) (lift' η') n))
  nf≤-• η η' (ne x ns) = cong₂ ne (var≤-• η η' x) (nfSpine≤-• η η' ns)

  nfSpine≤-• : ∀ {i Γ₁ Γ₂ Γ₃ a c} (η : Γ₁ ≤ Γ₂) (η' : Γ₂ ≤ Γ₃) (ns : NfSpine {i} Γ₃ a c) →

    nfSpine≤ η (nfSpine≤ η' ns) ≡ nfSpine≤ (η • η') ns

  nfSpine≤-• η η' ε        = refl
  nfSpine≤-• η η' (ns , n) = cong₂ _,_ (nfSpine≤-• η η' ns) (nf≤-• η η' n)
