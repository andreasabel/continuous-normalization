{-# OPTIONS --copatterns --sized-types #-}

module Term where

open import Level renaming (zero to lzero; suc to lsuc)
open import Size

open import Category.Applicative
open import Category.Monad

open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Delay

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i}) public renaming (_⊛_ to _<*>_)

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

lookup : {Γ : Cxt} {a : Ty} → Var Γ a → Env Γ → Val a
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

-- Call-by-value evaluation.

mutual
  〖_〗  : ∀ {i} {Γ : Cxt} {a : Ty} → Tm Γ a → Env Γ → Delay (Val a) i
  〖 var x   〗 ρ = now (lookup x ρ)
  〖 abs t   〗 ρ = now (lam t ρ)
  〖 app t u 〗 ρ = apply* (〖 t 〗 ρ) (〖 u 〗 ρ)

  apply* : ∀ {i a b} → Delay (Val (a ⇒ b)) i → Delay (Val a) i → Delay (Val b) i
  apply* f⊥ v⊥ = f⊥ >>= λ f → v⊥ >>= λ v → apply f v

  apply : ∀ {i a b} → Val (a ⇒ b) → Val a → Delay (Val b) i
  apply f v = later (∞apply f v)

  ∞apply : ∀ {i a b} → Val (a ⇒ b) → Val a → ∞Delay (Val b) i
  force (∞apply (lam t ρ) v) = 〖 t 〗 (ρ , v)

-- Type interpretation

mutual
  V⟦_⟧_ : (a : Ty) → Val a → Set
  V⟦ ★     ⟧ v = ⊤
  V⟦ a ⇒ b ⟧ f = (u : Val a) → V⟦ a ⟧ u → C⟦ b ⟧ (apply f u)

  C⟦_⟧_ : (a : Ty) → Delay (Val a) ∞ → Set
  C⟦ a ⟧ x = ∃ λ v → x ⇓ v × V⟦ a ⟧ v

{-
  C⟦ ★     ⟧ v = v ⇓
  C⟦ a ⇒ b ⟧ f = (u : Delay (Val a) ∞) → ⟦ a ⟧ u → ⟦ b ⟧ (apply* f u)
-}

⟪_⟫_ : (Γ : Cxt) → Env Γ → Set
⟪ ε ⟫     ε       = ⊤
⟪ Γ , a ⟫ (ρ , v) = ⟪ Γ ⟫ ρ × V⟦ a ⟧ v

-- Type soundness

norm : ∀ {Γ a} (t : Tm Γ a) {ρ : Env Γ} → ⟪ Γ ⟫ ρ → C⟦ a ⟧ (〖 t 〗 ρ)
norm (var x) θ = {!!}
norm (abs t) θ = {!!}
norm (app t u) θ = {!!}

