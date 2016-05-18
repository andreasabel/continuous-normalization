{-# OPTIONS --sized-types --copatterns #-}

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

-- Variables and terms.

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀ {Γ a}                 → Var (Γ , a) a
  suc  : ∀ {Γ a b} (x : Var Γ a) → Var (Γ , b) a

data Tm (Γ : Cxt) : (a : Ty) → Set where
  var : ∀ {a}   (x : Var Γ a)                   → Tm Γ a
  abs : ∀ {a b} (t : Tm (Γ , a) b)              → Tm Γ (a ⇒ b)
  app : ∀ {a b} (t : Tm Γ (a ⇒ b)) (u : Tm Γ a) → Tm Γ b
