-- Syntax: Types, terms and contexts.

module Term where

open import Library

infixr 6 _⇒_
infixl 1 _,_

-- Types and contexts.

data Ty : Set where
  ★   : Ty
  _⇒_ : (a b : Ty) → Ty

data Cxt : Set where
  ε   : Cxt
  _,_ : (Γ : Cxt) (a : Ty) → Cxt

-- Generic reversed Spines (last application available first).

data RSpine (V : Ty → Set) (a : Ty) : (c : Ty) → Set where
  ε   : RSpine V a a
  _,_ : ∀ {b c} → RSpine V a (b ⇒ c) → V b → RSpine V a c

-- Variables and terms.

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀ {Γ a}                 → Var (Γ , a) a
  suc  : ∀ {Γ a b} (x : Var Γ a) → Var (Γ , b) a

data Tm (Γ : Cxt) : (a : Ty) → Set where
  var : ∀ {a}   (x : Var Γ a)                   → Tm Γ a
  abs : ∀ {a b} (t : Tm (Γ , a) b)              → Tm Γ (a ⇒ b)
  app : ∀ {a b} (t : Tm Γ (a ⇒ b)) (u : Tm Γ a) → Tm Γ b

-- β-normal forms.

data βNf (Γ : Cxt) : Ty → Set where
  lam : ∀ {a b}  (n : βNf (Γ , a) b)                      → βNf Γ (a ⇒ b)
  ne  : ∀ {a b}  (x : Var Γ a) (ns : RSpine (βNf Γ) a b)  → βNf Γ b

-- η-long β-normal forms.

data Nf (Γ : Cxt) : Ty → Set where
  lam : ∀ {a b}  (n : Nf (Γ , a) b)                      → Nf Γ (a ⇒ b)
  ne  : ∀ {a}    (x : Var Γ a) (ns : RSpine (Nf Γ) a ★)  → Nf Γ ★

-- Additional stuff for contexts.
-- order preserving embeddings

data _≤_ : (Γ Δ : Cxt) → Set where
  id   : ∀ {Γ} → Γ ≤ Γ
  weak : ∀ {Γ Δ a} → Γ ≤ Δ → (Γ , a) ≤ Δ
  lift : ∀ {Γ Δ a} → Γ ≤ Δ → (Γ , a) ≤ (Δ , a)

-- Composition

_•_ : ∀ {Γ Δ Δ'} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') → Γ ≤ Δ'
id     • η'      = η'
weak η • η'      = weak (η • η')
lift η • id      = lift η
lift η • weak η' = weak (η • η')
lift η • lift η' = lift (η • η')

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
