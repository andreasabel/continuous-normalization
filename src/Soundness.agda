
module Soundness where

open import Library
open import Delay
open import WeakBisim
open import Syntax
open import RenamingAndSubstitution
open import Evaluation
open import EquationalTheory


record _~Ne_ {Γ}{a} (t : Tm Γ a) (u : NeVal Γ a) : Set where
  field
    nTm   : Ne Γ a
    nConv : nereadback u ⇓ nTm
    nEq   : t ≡βη embNe nTm

mutual

  -- Values v and v' are related at type a.

  _V∋_~_ : ∀{Γ}(a : Ty) (t : Tm Γ a) (v : Val Γ a) → Set
  -- ★ V∋ ne t ~ ne t' = nereadback t ~ nereadback t'
  _V∋_~_         ★       t (ne u)  = t ~Ne u
  _V∋_~_ {Γ = Γ} (a ⇒ b) t f       = ∀{Δ}(ρ : Ren Δ Γ)(s : Tm Δ a)(u : Val Δ a)
    (s~u : a V∋ s ~ u) → b C∋ (app (ren ρ t) s) ~ (apply (renval ρ f) u)

  VLR : ∀{Γ}(a : Ty) (t : Tm Γ a) (v : Val Γ a) → Set
  VLR a t v = _V∋_~_ a t v

  -- Value computations v? and w? are related at type a.

  _C∋_~_ : ∀{Γ}(a : Ty) (t : Tm Γ a) (v? : Delay ∞ (Val Γ a)) → Set
  a C∋ t ~ v? = ∃ λ v → v? ⇓ v × a V∋ t ~ v
