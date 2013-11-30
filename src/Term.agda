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

mutual
  Var : Cxt → Ty → Set
  Var Γ a = Var' a Γ

  data Var' (a : Ty) : (Γ : Cxt) → Set where
    zero : ∀ {Γ}                 → Var (Γ , a) a
    suc  : ∀ {Γ b} (x : Var Γ a) → Var (Γ , b) a

data Tm (Γ : Cxt) : (a : Ty) → Set where
  var : ∀ {a}   (x : Var Γ a)                   → Tm Γ a
  abs : ∀ {a b} (t : Tm (Γ , a) b)              → Tm Γ (a ⇒ b)
  app : ∀ {a b} (t : Tm Γ (a ⇒ b)) (u : Tm Γ a) → Tm Γ b

-- β-normal forms.

data βNf (Γ : Cxt) : Ty → Set where
  lam : ∀ {a b}  (n : βNf (Γ , a) b)                      → βNf Γ (a ⇒ b)
  ne  : ∀ {a b}  (x : Var Γ a) (ns : RSpine (βNf Γ) a b)  → βNf Γ b

-- Long normal forms.

data Nf (Γ : Cxt) : Ty → Set where
  lam : ∀ {a b}  (n : Nf (Γ , a) b)                      → Nf Γ (a ⇒ b)
  ne  : ∀ {a}    (x : Var Γ a) (ns : RSpine (Nf Γ) a ★)  → Nf Γ ★

-- Additional stuff for contexts.

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

-- Monotonicity.

var≤ : ∀ {Γ Δ a} → (η : Γ ≤ Δ) (x : Var Δ a) → Var Γ a
var≤ id        x      = x
var≤ (weak η)  x      = suc (var≤ η x)
var≤ (lift η)  zero   = zero
var≤ (lift η) (suc x) = suc (var≤ η x)

-- Length.

len : Cxt → ℕ
len ε       = 0
len (Γ , _) = 1 + len Γ
