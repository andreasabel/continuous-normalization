module Term where

open import Level renaming (zero to lzero; suc to lsuc)
open import Coinduction

open import Category.Applicative
open import Category.Monad
open import Category.Monad.Partiality renaming (monad to delayMonad)

open RawMonad (delayMonad {f = lzero}) renaming (_⊛_ to _<*>_)

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

-- Values and environments

mutual
  data Env : (Γ : Cxt) → Set where
    ε   : Env ε
    _,_ : ∀ {Γ a} (ρ : Env Γ) (v : Val a) → Env (Γ , a)

  data Val : (a : Ty) → Set where
    lam : ∀ {Γ a b} (t : Tm (Γ , a) b) (ρ : Env Γ) → Val (a ⇒ b)

-- Notation for evaluation.

data VarTm : Set where
  var : VarTm
  tm  : VarTm

El : (vt : VarTm) (Γ : Cxt) (a : Ty) → Set
El var = Var
El tm  = Tm

-- Eval : VarTm → Set
-- Eval var = Var Γ a → Env Γ → Val a
-- Eval tm  = Tm  Γ a → Env Γ → Val a

lookup : {Γ : Cxt} {a : Ty} → Var Γ a → Env Γ → Val a
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

mutual
  ⟦_⟧  : {Γ : Cxt} {a : Ty} → Tm Γ a → Env Γ → Val a ⊥
  ⟦ var x   ⟧ ρ = now (lookup x ρ)
  ⟦ abs t   ⟧ ρ = now (lam t ρ)
  ⟦ app t u ⟧ ρ = ⟦ t ⟧ ρ >>= λ f →
                 ⟦ u ⟧ ρ >>= λ v → later (♯ apply f v)

  apply : ∀ {a b} → Val (a ⇒ b) → Val a → Val b ⊥
  apply (lam t ρ) v = later (♯ ⟦ t ⟧ (ρ , v))

{-
⟦_⟧ : {vt : VarTm}{Γ : Cxt}{a : Ty} →  El vt Γ a → Env Γ → Val a
⟦ zero    ⟧ (ρ , v) = v
⟦ suc x   ⟧ (ρ , v) = ρ
⟦ var x   ⟧ ρ       = ⟦ x ⟧ ρ
⟦ abs t   ⟧ ρ       = lam t ρ
⟦ app t s ⟧ ρ       = ?
-}
