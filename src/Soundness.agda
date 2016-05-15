module Soundness where

open import Library
open import Delay
open import Syntax
open import RenamingAndSubstitution
open import Evaluation
open import EquationalTheory

infix 8 _V∋_~_ -- _C∋_~_ _~E_

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

_V∋_~_ : ∀{Γ}(a : Ty) (t : Tm Γ a) (v : Val ∞ Γ a) → Set
_V∋_~_         ★       t u  =
  Delay₁ ∞ (λ n → t ≡βη (embNf n)) (readback u)
_V∋_~_ {Γ = Γ} (a ⇒ b) t f       =
  ∀{Δ}(ρ : Ren Δ Γ)(s : Tm Δ a)(u : Val ∞ Δ a)
   (s~u : a V∋ s ~ u) → b V∋ (app (ren ρ t) s) ~ (apply (renval ρ f) u)

_~E_ : ∀{Γ Δ} (σ : Sub Γ Δ) (ρ : Env ∞ Γ Δ) → Set
ε       ~E ε       = ⊤
(σ , t) ~E (ρ , v) = σ ~E ρ × _ V∋ t ~ v


V∋subst : ∀{Γ}{a : Ty}{t t' : Tm Γ a}{v : Val ∞ Γ a} → a V∋ t ~ v → t ≡ t' →
          a V∋ t' ~ v
V∋subst p refl = p

mutual
  Dsubstβη : ∀{Γ a}{t t' : Tm Γ a}{v : Delay ∞ (Nf Γ a)} →
             Delay₁ ∞ (λ n → t ≡βη embNf n) v → t ≡βη t' →
             Delay₁ ∞ (λ n → t' ≡βη embNf n) v
  Dsubstβη (now₁ p)   q = now₁ $ trans≡ (sym≡ q) p 
  Dsubstβη (later₁ x) q = later₁ (∞Dsubstβη x q)

  ∞Dsubstβη : ∀{Γ a} {t t' : Tm Γ a}{v : ∞Delay ∞ (Nf Γ a)} →
             ∞Delay₁ ∞ (λ n → t ≡βη embNf n) v → t ≡βη t' →
             ∞Delay₁ ∞ (λ n → t' ≡βη embNf n) v
  ∞Delay₁.force₁ (∞Dsubstβη p q) = Dsubstβη (∞Delay₁.force₁ p) q

V∋substβη : ∀{Γ} a {t t' : Tm Γ a}{v : Val ∞ Γ a} → a V∋ t ~ v → t ≡βη t' →
          a V∋ t' ~ v
V∋substβη ★       p q = Dsubstβη p q  
V∋substβη (a ⇒ b) p q ρ s u s~u =
  V∋substβη b (p ρ s u s~u) (app≡ (ren≡βη q ρ) (refl≡ s))

  
V∋subst' : ∀{Γ} a {t  : Tm Γ a}{v v' :  Val ∞ Γ a} →
            Val∋ v ≈ v' → a V∋ t ~ v → a V∋ t ~ v'
V∋subst' ★       p q = transD (λ n → _ ≡βη embNf n) (readback-cong _ p) q
V∋subst' (a ⇒ b) p q ρ s u s~u =
  V∋subst' b (apply-cong (renval-cong ρ p) (≈reflVal u)) (q ρ s u s~u)

V∋step : ∀{Γ} a {t  : Tm Γ a}{v : ∞Val ∞ Γ a} →
         a V∋ t ~ ∞Val.force v → a V∋ t ~ later v
V∋step ★ p = later₁ (delay₁ p)
V∋step (a ⇒ b) p ρ s u s~u = V∋step b (p ρ s u s~u)

renV∋ : ∀{Γ} a {t : Tm Γ a}{v :  Val ∞ Γ a} → a V∋ t ~ v →
           ∀{Δ}(σ : Ren Δ Γ) → a V∋ ren σ t ~ renval σ v
renV∋ ★       {t}{u} p σ =
 transD
  (λ n → ren σ t ≡βη embNf n)
  (renreadback _ σ u)
  (mapD    (λ n → t ≡βη embNf n)
           (λ n → ren σ t ≡βη embNf n)
           (rennf σ)
           (λ {n} p -> trans≡ (ren≡βη p σ) (≡to≡βη (renembNf n σ)))
           p)
renV∋ (a ⇒ b){t}{v} p σ ρ s u s~u = V∋subst'
  b
  (apply-cong (≈symVal (renvalcomp ρ σ v)) (≈reflVal u))
  (V∋subst (p (renComp ρ σ) s u s~u) (cong (λ f → app f s) (rencomp ρ σ t)))  

ren~E : ∀{Γ Δ}{σ : Sub Δ Γ}{ρ : Env ∞ Δ Γ} (σ~ρ : σ ~E ρ) →
        ∀{Δ'}(σ' : Ren Δ' Δ) → subComp (ren2sub σ') σ ~E renenv σ' ρ
ren~E {σ = ε}    {ε}     p σ' = _
ren~E {σ = σ , s}{ρ , v} (p , p') σ' =
  ren~E p σ' , V∋subst (renV∋ _ p' σ') (ren2subren σ' s)

-- Fundamental theorem
fundvar : ∀{Γ a} (x : Var Γ a) →
  ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env ∞ Δ Γ} (σ~ρ : σ ~E ρ) →
  a V∋ looks σ x ~ lookup x ρ
fundvar zero    {σ = σ , t} {ρ , v} (_ , p) = p
fundvar (suc x) {σ = σ , t} {ρ , v} (p , _) = fundvar x p

fundapp : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{f : Val ∞ Γ (a ⇒ b)} →
         (a ⇒ b) V∋ t ~ f →
         {u : Tm Γ a}{v : Val ∞ Γ a}  →
         a V∋ u ~ v →
         b V∋ app t u ~ apply f v
fundapp {Γ}{a}{b}{t}{f} p {u}{v} q =
  V∋subst (V∋subst' b
                    (apply-cong (renvalid f) (≈reflVal v))
                    (p renId u v q))
          (cong (λ t → app t u) (renid t))

fund : ∀{Γ a} (t : Tm Γ a) →
    ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env ∞ Δ Γ} (σ~ρ : σ ~E ρ) →
    a V∋ sub σ t ~ eval t ρ
fund (var x)   p = fundvar x p
fund {a = a ⇒ b} (abs t){Δ} {σ}{ρ}   p ρ' s u s~u = V∋substβη 
  b 
  (V∋step b (fund 
    t
    {σ = subComp (ren2sub ρ') σ , s}
    {ρ = renenv ρ' ρ , u}
    (ren~E p ρ' , s~u)))
  (trans≡ (≡to≡βη (trans 
    (trans 
      (cong 
        (λ f → sub f t) 
        (cong (_, s) 
              (trans (sym $ sidl (subComp (ren2sub ρ') σ))
                     (sym $ lemss subId s (subComp (ren2sub ρ') σ)))))
      (subcomp (subId , s) (lifts (subComp (ren2sub ρ') σ)) t))
    (cong (sub (subId , s))
          (trans (cong (λ f → sub f t) (sym $ liftrscomp ρ' σ)) 
                 (sym (rensub (liftr ρ') (lifts σ) t)))))) 
          (sym≡ beta≡))

fund (app t u) p =
    V∋subst (V∋subst' _
                      (apply-cong (renvalid (eval t _)) (≈reflVal (eval u _)))
                      (fund t p renId _ _ (fund u p)))
            (cong (λ f → app f (sub _ u)) (renid _))

lemma : ∀{Γ a b}
        {t : Tm Γ (a ⇒ b)}
        {s : Tm Γ a}
        {f : NeVal ∞ Γ (a ⇒ b)}
        {u : Val ∞ Γ a} →
        Delay₁ ∞ (λ n → t ≡βη embNe n) (nereadback f) →
        Delay₁ ∞ (λ n → s ≡βη embNf n) (readback u) →
        Delay₁ ∞ (λ n → app t s ≡βη embNe n) (nereadback (app f u))
lemma {t = t}{s}{f}{u} p q = mapD2
  (λ n → t ≡βη embNe n)
  (λ n → s ≡βη embNf n)
  (λ n → app t s ≡βη embNe n)
  GNe.app
  app≡
  p
  q

mutual
  reify : ∀{Γ} a {t : Tm Γ a}{v : Val ∞ Γ a} →
          a V∋ t ~ v → Delay₁ ∞ (λ n → t ≡βη embNf n) (readback v)
  reify ★      {t}{u} p = p
  reify (a ⇒ b){t}       p = later₁
    (reify-eta
      (reify b
             (p (wkr renId)
                (var zero)
                (ne (var zero))
                (reflect a (now₁ (var≡ zero))))))
  reify-eta : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{v : Val ∞ Γ (a ⇒ b)} →
             Delay₁
               ∞
               (λ n → app (ren (wkr renId) t) (var zero) ≡βη embNf n)
               (readback (apply (renval (wkr renId) v) (ne (var zero)))) →
             ∞Delay₁ ∞ (λ n → t ≡βη embNf n) (eta v ∞>>= (λ x' → now (abs x')))
  force₁ (reify-eta {a = a}{b}{t}{v} p) =
    mapD (λ n → app (ren (wkr renId) t) (var zero) ≡βη embNf n)
         (λ n → t ≡βη embNf n)
         Nf.abs
         (λ p → trans≡ (sym≡ (eta≡ t)) (abs≡ p))
         p

  reflect : ∀{Γ} a {t : Tm Γ a}{u : NeVal ∞ Γ a} →
            Delay₁ ∞ (λ n → t ≡βη embNe n) (nereadback u) → a V∋ t ~ (ne u)
  reflect ★       p         =
    mapD (λ n → _ ≡βη embNe n) (λ n → _ ≡βη embNf n) ne id p
  reflect (a ⇒ b){t}{f} p ρ s u q = reflect b  $ lemma
    {t = ren ρ t}
    {s}
    {rennev ρ f}
    (transD
      (λ n → ren ρ t ≡βη embNe n)
      (rennereadback ρ f)
      (mapD
        (λ n → t ≡βη embNe n)
        (λ n → ren ρ t ≡βη embNe n)
        (rennen ρ)
        (λ {n} p → trans≡ (ren≡βη p ρ) (≡to≡βη (renembNe n ρ)))
        p) )
    (reify a {s}{u} q) 


~var : ∀{Γ a}(x : Var Γ a) → a V∋ var x ~ ne (var x)
~var x = reflect _ (now₁ (var≡ x))

ide~E : ∀ Γ → subId {Γ} ~E ide Γ
ide~E ε       = _
ide~E (Γ , a) =
  subst (λ x → x ~E renenv (wkr renId) (ide Γ))
        (trans (wkrscomp renId subId)
               (cong wks (trans (sidr (ren2sub renId)) (sym $ ren2subid ))))
        (ren~E (ide~E  Γ) (wkr renId))
  ,
  ~var zero

soundness : ∀ Γ a (t : Tm Γ a) → Delay₁ ∞ (λ n → t ≡βη embNf n) (nf t)
soundness Γ a t = reify a (V∋subst (fund t (ide~E Γ)) (subid t))
