{-# OPTIONS --copatterns #-}

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
  _V∋_~_         ★       t (ne u)  = Delay₁ ∞ (λ n → t ≡βη (embNe n)) (nereadback u)
  _V∋_~_ {Γ = Γ} (a ⇒ b) t f       = ∀{Δ}(ρ : Ren Δ Γ)(s : Tm Δ a)(u : Val Δ a)
    (s~u : a V∋ s ~ u) → b C∋ (app (ren ρ t) s) ~ (apply (renval ρ f) u)

  VLR : ∀{Γ}(a : Ty) (t : Tm Γ a) (v : Val Γ a) → Set
  VLR a t v = _V∋_~_ a t v

  -- Value computations v? and w? are related at type a.

  _C∋_~_ : ∀{Γ}(a : Ty) (t : Tm Γ a) (v? : Delay ∞ (Val Γ a)) → Set
  a C∋ t ~ v? = Delay₁ ∞ (VLR a t) v?

_~E_ : ∀{Γ Δ} (σ : Sub Γ Δ) (ρ : Env Γ Δ) → Set
ε       ~E ε       = ⊤
(σ , t) ~E (ρ , v) = σ ~E ρ × _ V∋ t ~ v

V∋subst : ∀{Γ}{a : Ty}{t t' : Tm Γ a}{v : Val Γ a} → a V∋ t ~ v → t ≡ t' →
          a V∋ t' ~ v
V∋subst p refl = p    

≡to≡βη : ∀{Γ a}{t t' : Tm Γ a} → t ≡ t' → t ≡βη t'
≡to≡βη refl = refl≡

ren≡βη : ∀{Γ a} {t : Tm Γ a}{t' : Tm Γ a} → t ≡βη t' → ∀{Δ}(σ : Ren Δ Γ) →
        ren σ t ≡βη ren σ t'
ren≡βη (var≡ p)     σ = var≡ (cong (lookr σ) p)
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
ren≡βη (eta≡ {t = t}) σ = trans≡ (abs≡ (app≡ (≡to≡βη (trans (sym $ rencomp (liftr σ) (wkr renId) t) (trans (cong (λ xs → ren xs t) (trans (lemrr (wkr σ) zero renId) (trans (ridr (wkr σ)) (trans (cong wkr (sym $ lidr σ)) (sym $ wkrcomp renId σ))))) (rencomp (wkr renId) σ t)))) refl≡)) eta≡
ren≡βη refl≡        σ = refl≡
ren≡βη (sym≡ p)     σ = sym≡ (ren≡βη p σ)
ren≡βη (trans≡ p q) σ = trans≡ (ren≡βη p σ) (ren≡βη q σ)

V∋subst' : ∀{Γ}(a : Ty){t t' : Tm Γ a}{v : Val Γ a} → a V∋ t ~ v → t ≡βη t' →
          a V∋ t' ~ v
V∋subst' ★ {t}{t'}{ne n} p q = transD
  (λ n₁ → t' ≡βη embNe n₁)
  (≈sym $ bind-now _)
  (transPD
    (λ n₁ → t ≡βη embNe n₁)
    (λ n₁ → t' ≡βη embNe n₁)
    id
    (λ r → trans≡ (sym≡ q) r) p)
V∋subst' (a ⇒ b) {t}{t'} p q ρ s u r = transD
  (λ v → b V∋ app (ren ρ t') s ~ v)
  (≈sym $ bind-now _)
  (transPD
    (λ v → b V∋ app (ren ρ t) s ~ v)
    (λ v → b V∋ app (ren ρ t') s ~ v)
    id
    (λ {v} r → V∋subst' b r (app≡ (ren≡βη q ρ) refl≡)) (p ρ s u r)) 

renV∋ : ∀{Γ} a {t : Tm Γ a}{v :  Val Γ a} → a V∋ t ~ v →
           ∀{Δ}(σ : Ren Δ Γ) → a V∋ ren σ t ~ renval σ v
renV∋ ★       {t}{ne u} p σ = transD
  (λ n → ren σ t ≡βη embNe n)
  (rennereadback σ u)
  (transPD (λ n → t ≡βη embNe n)
           (λ n → ren σ t ≡βη embNe n)
           (rennen σ)
           (λ p → trans≡ (ren≡βη p σ) (≡to≡βη (renembNe _ σ)))
           p)
renV∋ (a ⇒ b){t}{v} p σ ρ s u s~u =
  transD (λ v₁ → b V∋ app (ren ρ (ren σ t)) s ~ v₁)
         (≈trans (≈sym $ bind-now (apply (renval (renComp ρ σ) v) u))
                 (subst (λ x → apply x u ≈ apply (renval ρ (renval σ v)) u)
                        (renvalcomp ρ σ v)
                        (≈refl _)))
         (transPD
           (λ v₁ → b V∋ app (ren (renComp ρ σ) t) s ~ v₁)
           (λ v₁ → b V∋ app (ren ρ (ren σ t)) s ~ v₁)
           {(apply (renval (renComp ρ σ) v) u)}
           id
           (λ p → V∋subst p (cong (λ t → app t s) (rencomp ρ σ t)))
           (p (renComp ρ σ) s u s~u)) 

ren~E : ∀{Γ Δ}{σ : Sub Δ Γ}{ρ : Env Δ Γ} (σ~ρ : σ ~E ρ) →
        ∀{Δ'}(σ' : Ren Δ' Δ) → subComp (ren2sub σ') σ ~E renenv σ' ρ
ren~E {σ = ε}    {ε}     p σ' = _
ren~E {σ = σ , s}{ρ , v} (p , p') σ' =
  ren~E p σ' , V∋subst (renV∋ _ p' σ') (ren2subren σ' s)        

-- Fundamental theorem.

soundvar : ∀{Γ a} (x : Var Γ a) →
  ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env Δ Γ} (σ~ρ : σ ~E ρ) →
  a V∋ looks σ x ~ lookup x ρ
soundvar zero    {σ = σ , t} {ρ , v} (_ , p) = p
soundvar (suc x) {σ = σ , t} {ρ , v} (p , _) = soundvar x p

soundapp : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{f : Val Γ (a ⇒ b)} → 
         (a ⇒ b) V∋ t ~ f → 
         {u : Tm Γ a}{v : Val Γ a}  →
         a V∋ u ~ v →
         b C∋ app t u ~ apply f v
soundapp {Γ}{a}{b}{t}{f} p {u}{v} q = transD
  (VLR b (app t u))
  (≈sym $ bind-now (apply f v))
  (transPD
    (VLR b (app (ren renId t) u))
    (VLR b (app t u))
    id
    (λ p → V∋subst p (cong (λ t → app t u) (renid t)))
    (transD (VLR b (app (ren renId t) u))
            (subst (λ x → apply x v ≈ apply f v) (sym $ renvalid f)  (≈refl _))
            (p renId u v q)))

mutual
  soundness : ∀{Γ a} (t : Tm Γ a) →
    ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env Δ Γ} (σ~ρ : σ ~E ρ) →
    a C∋ sub σ t ~ eval t ρ
  soundness (var x)   p = now₁ (soundvar x p)
  soundness {a = a ⇒ b} (abs t){Δ} {σ}{ρ}   p = now₁ λ {Δ'} ρ' s u p' → later₁ $
    ∞transD
      (VLR b (app (ren ρ' (sub σ (abs t))) s))
      (∞≈sym $ ∞bind-now _)
      (∞transPD
        (VLR b (sub (subComp (ren2sub ρ') σ , s) t))
        (VLR b (app (ren ρ' (sub σ (abs t))) s))
        id
        (λ {v} p → V∋subst' b p (trans≡ (≡to≡βη (trans
          (trans (cong (λ xs → sub xs t)
                       (cong (λ xs → xs Sub., s)
                             (trans (trans (sym $ sidl (subComp (ren2sub ρ') σ))
                                           (sym $ lemss subId s (subComp (ren2sub ρ') σ)))
                                    (cong (subComp (subId Sub., s))
                                          (trans (sym $ wkrscomp ρ' σ)
                                                 (sym $ lemss (ren2sub (wkr ρ'))
                                                              (var zero)
                                                              σ))))))
                 (subcomp (subId , s) (subComp (ren2sub (liftr ρ')) (lifts σ)) t))
          (cong (sub (subId , s)) (sym $ rensub (liftr ρ') (lifts σ) t) ))) (sym≡ beta≡)))
        (∞beta t (ren~E p ρ') p'))
  soundness (app t u) p = {!soundness t p !}

  ∞beta : ∀{Γ a b} (t : Tm (Γ , a) b) →
    ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env Δ Γ} (σ~ρ : σ ~E ρ) →
    {s : Tm Δ a}{v : Val Δ a} → a V∋ s ~ v →
    ∞Delay₁ ∞ (VLR b (sub (σ , s) t)) (beta t ρ v)
  force₁ (∞beta t p p') = soundness t (p , p')

