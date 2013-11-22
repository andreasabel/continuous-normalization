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

