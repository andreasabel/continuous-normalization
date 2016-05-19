module EquationalTheory where

open import Library
open import Syntax
open import RenamingAndSubstitution

-- Single collapsing substitution.

sub1 : ∀{Γ σ τ} → Tm Γ σ → Tm (Γ , σ) τ → Tm Γ τ
sub1 {Γ}{σ}{τ} u t = sub (subId , u) t

-- Typed β-η-equality.

data _≡βη_ {Γ : Cxt} : ∀{σ} → Tm Γ σ → Tm Γ σ → Set where

  -- Axioms.

  beta≡  : ∀{σ τ} {t : Tm (Γ , σ) τ} {u : Tm Γ σ} →

           --------------------------
           app (abs t) u ≡βη sub1 u t

  eta≡   : ∀{σ τ} (t : Tm Γ (σ ⇒ τ)) →

           -------------------------------------
           abs (app (weak _ t) (var zero)) ≡βη t

  -- Congruence rules.

  var≡   : ∀{σ} (x : Var Γ σ) →

           ---------------
           var x ≡βη var x

  abs≡   : ∀{σ τ}{t t' : Tm (Γ , σ) τ} →

           t ≡βη t' →
           ----------------
           abs t ≡βη abs t'

  app≡   : ∀{σ τ}{t t' : Tm Γ (σ ⇒ τ)}{u u' : Tm Γ σ} →

          t ≡βη t' → u ≡βη u' →
          ---------------------
          app t u ≡βη app t' u'

  -- Equivalence rules.

  refl≡  : ∀{a} (t : Tm Γ a) →

           -------
           t ≡βη t

  sym≡   : ∀{a}{t t' : Tm Γ a}

           (t'≡t : t' ≡βη t) →
           -----------------
           t ≡βη t'

  trans≡ : ∀{a}{t₁ t₂ t₃ : Tm Γ a}

           (t₁≡t₂ : t₁ ≡βη t₂) (t₂≡t₃ : t₂ ≡βη t₃) →
           ----------------------------------
           t₁ ≡βη t₃


≡to≡βη : ∀{Γ a}{t t' : Tm Γ a} → t ≡ t' → t ≡βη t'
≡to≡βη refl = refl≡ _

ren≡βη : ∀{Γ a} {t : Tm Γ a}{t' : Tm Γ a} → t ≡βη t' → ∀{Δ}(σ : Ren Δ Γ) →
        ren σ t ≡βη ren σ t'
ren≡βη (var≡ x)     σ = var≡ (lookr σ x)
ren≡βη (abs≡ p)     σ = abs≡ (ren≡βη p (liftr σ))
ren≡βη (app≡ p q)   σ = app≡ (ren≡βη p σ) (ren≡βη q σ)
ren≡βη (beta≡ {t = t}{u = u})        σ = trans≡ beta≡ $ ≡to≡βη $
  trans (subren (subId , ren σ u) (liftr σ) t)
        (trans (cong (λ xs → sub xs t)
                     (cong₂ Sub._,_
                            (trans (lemsr subId (ren σ u) σ)
                            (trans (sidl (ren2sub σ)) (sym $ sidr (ren2sub σ))))
                            (ren2subren σ u)))
               (sym $ rensub σ (subId , u) t))
ren≡βη (eta≡ t) σ = trans≡
  (abs≡ (app≡ (≡to≡βη
    (trans (sym $ rencomp (liftr σ) (wkr renId) t)
           (trans (cong (λ xs → ren xs t)
                        (trans (lemrr (wkr σ) zero renId)
                               (trans (ridr (wkr σ))
                                      (trans (cong wkr (sym (lidr σ)))
                                             (sym (wkrcomp renId σ))))))
                  (rencomp (wkr renId) σ t))))
    (refl≡ _)))
  (eta≡ _)
ren≡βη (refl≡ t)        σ = refl≡ _
ren≡βη (sym≡ p)     σ = sym≡ (ren≡βη p σ)
ren≡βη (trans≡ p q) σ = trans≡ (ren≡βη p σ) (ren≡βη q σ)
