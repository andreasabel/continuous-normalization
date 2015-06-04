-- Syntax: Types, terms and contexts.

module Syntax where

open import Library

infixr 6 _⇒_
infixr 4 _,_

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

-- Generalized neutral terms.

data GNe (Arg : Cxt → Ty → Set) (Γ : Cxt) : Ty → Set where
  var : ∀{a}    (x : Var Γ a)                         → GNe Arg Γ a
  app : ∀{a b}  (n : GNe Arg Γ (a ⇒ b)) (o : Arg Γ a) → GNe Arg Γ b

-- β-normal forms.

mutual

  Ne = GNe Nf

  data Nf (Γ : Cxt) : Ty → Set where
    abs : ∀{a b}  (o : Nf (Γ , a) b)  → Nf Γ (a ⇒ b)
    ne  :         (n : Ne Γ ★)        → Nf Γ ★

mutual

  embNe : ∀{Γ a} → Ne Γ a → Tm Γ a
  embNe (var x) = var x
  embNe (app t u) = app (embNe t) (embNf u)

  embNf : ∀{Γ a} → Nf Γ a → Tm Γ a
  embNf (ne t) = embNe t
  embNf (abs t) = abs (embNf t)

-- Values and environments.

mutual

  data Env (i : Size) (Δ : Cxt) : (Γ : Cxt) → Set where
    ε   : Env i Δ ε
    _,_ : ∀ {Γ a} (ρ : Env i Δ Γ) (v : Val i Δ a) → Env i Δ (Γ , a)

  NeVal = λ i → GNe (Val i)

  data Val (i : Size) (Δ : Cxt) : (a : Ty) → Set where
    ne    : ∀{a}      (n : NeVal i Δ a)                   → Val i Δ a
    lam   : ∀{Γ a b}  (t : Tm (Γ , a) b) (ρ : Env i Δ Γ)  → Val i Δ (a ⇒ b)
    later : ∀{a}      (v∞ : ∞Val i Δ a)                   → Val i Δ a

  record ∞Val (i : Size) (Δ : Cxt) (a : Ty) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Val j Δ a


  -- Note: this is not the same thing as Delay i (Val i Δ a)
  -- because now the sizes are not uniform, but the size is
  -- the sum on the longest path

  -- ALT:
  -- data Delay (i : Size) (A : Size → Set) : Set where
  --   now : A i → Delay i A
  --   ...
  -- but we would need to tell Agda that A is antitone
  -- otherwise Delay i A is not antitone in i
