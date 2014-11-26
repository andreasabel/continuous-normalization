module EquationalTheory where

open import Term
open import Spine
open import RenamingAndSubstitution

sub<< : ∀{Γ Δ σ} → Sub Γ Δ → Tm Δ σ → Sub (Γ , σ) Δ
sub<< f t zero    = t
sub<< f t (suc x) = f x


sub1 : ∀{Γ σ τ} → Tm Γ σ → Tm (Γ , σ) τ → Tm Γ τ
sub1 {Γ}{σ}{τ} u t = sub (sub<< var u) t

data _≡v_ : ∀{Γ σ} → Var Γ σ → Var Γ σ → Set where
  zero : ∀{Γ σ} → zero {Γ}{σ} ≡v zero 
  suc  : ∀{Γ σ τ}{x x' : Var Γ σ} → x ≡v x' → suc {b = τ} x ≡v suc x'
  
data _≡_ {Γ : Cxt} : ∀{σ} → Tm Γ σ → Tm Γ σ → Set where
  var≡  : ∀{σ}{x x' : Var Γ σ} → x ≡v x' → var x ≡ var x' 
  abs≡  : ∀{σ τ}{t t' : Tm (Γ , σ) τ} → t ≡ t' → abs t ≡ abs t'
  app≡  : ∀{σ τ}{t t' : Tm Γ (σ ⇒ τ)}{u u' : Tm Γ σ} → t ≡ t' → u ≡ u' →
          app t u ≡ app t' u'
  beta≡ : ∀{σ τ}{t : Tm (Γ , σ) τ}{u : Tm Γ σ} →
          app (abs t) u ≡ sub (sub<< var u) t
  eta≡  : ∀{σ τ}{t : Tm Γ (σ ⇒ τ)} → abs (app (ren suc t) (var zero)) ≡ t
