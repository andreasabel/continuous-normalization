-- Syntax: Types, terms and contexts.

module Term where

infixr 4 _⇒_
infixl 1 _,_

-- Types and contexts.

data Ty : Set where
  ★   : Ty
  _⇒_ : (a b : Ty) → Ty

data Cxt : Set where
  ε   : Cxt
  _,_ : Cxt → Ty → Cxt

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
  lam : ∀ {σ τ}  (n : βNf (Γ , σ) τ)                      → βNf Γ (σ ⇒ τ)
  ne  : ∀ {σ τ}  (x : Var Γ σ) (ns : RSpine (βNf Γ) σ τ)  → βNf Γ τ

-- Long normal forms.

data Nf (Γ : Cxt) : Ty → Set where
  lam : ∀ {σ τ}  (n : Nf (Γ , σ) τ)                      → Nf Γ (σ ⇒ τ)
  ne  : ∀ {σ}    (x : Var Γ σ) (ns : RSpine (Nf Γ) σ ★)  → Nf Γ ★
