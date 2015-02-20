
module Soundness where

open import Library
open import Delay
open import WeakBisim
open import Syntax
open import RenamingAndSubstitution
open import Evaluation
open import EquationalTheory

-- UNUSED: implies termination.
record _~Ne_ {Γ}{a} (t : Tm Γ a) (u : NeVal Γ a) : Set where
  field
    nTm   : Ne Γ a
    nConv : nereadback u ⇓ nTm
    nEq   : t ≡βη embNe nTm

mutual

  -- Values v and v' are related at type a.

  _V∋_~_ : ∀{Γ}(a : Ty) (t : Tm Γ a) (v : Val Γ a) → Set
  -- ★ V∋ ne t ~ ne t' = nereadback t ~ nereadback t'
  _V∋_~_         ★       t (ne u)  = Delay₁ (λ n → t ≡βη (embNe n)) (nereadback u)
  _V∋_~_ {Γ = Γ} (a ⇒ b) t f       = ∀{Δ}(ρ : Ren Δ Γ)(s : Tm Δ a)(u : Val Δ a)
    (s~u : a V∋ s ~ u) → b C∋ (app (ren ρ t) s) ~ (apply (renval ρ f) u)

  VLR : ∀{Γ}(a : Ty) (t : Tm Γ a) (v : Val Γ a) → Set
  VLR a t v = _V∋_~_ a t v

  -- Value computations v? and w? are related at type a.

  _C∋_~_ : ∀{Γ}(a : Ty) (t : Tm Γ a) (v? : Delay ∞ (Val Γ a)) → Set
  a C∋ t ~ v? = Delay₁ (VLR a t) v?

_~E_ : ∀{Γ Δ} (σ : Sub Γ Δ) (ρ : Env Γ Δ) → Set
ε       ~E ε       = ⊤
(σ , t) ~E (ρ , v) = σ ~E ρ × _ V∋ t ~ v

looksound : ∀{Γ a} (x : Var Γ a) →
  ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env Δ Γ} (σ~ρ : σ ~E ρ) →
  a V∋ looks σ x ~ lookup x ρ
looksound zero    {σ = σ , t} {ρ , v} (_ , p) = p
looksound (suc x) {σ = σ , t} {ρ , v} (p , _) = looksound x p

-- Fundamental theorem.

soundness : ∀{Γ a} (t : Tm Γ a) →
  ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env Δ Γ} (σ~ρ : σ ~E ρ) →
  a C∋ sub σ t ~ eval t ρ
soundness (var x)   p = now₁ (looksound x p)
soundness (abs t)   p = {!!}
soundness (app t u) p = {!soundness t p !}
