{-# OPTIONS --copatterns #-}

module Soundness where

open import Library
open import Delay
open import Syntax
open import RenamingAndSubstitution
open import Evaluation
open import EquationalTheory

infix 8 _V∋_~_ _C∋_~_ _~E_

mutual
  _V∋_~_ : ∀{Γ}(a : Ty) (t : Tm Γ a) (v : Val Γ a) → Set
  _V∋_~_         ★       t (ne u)  =
    Delay₁ ∞ (λ n → t ≡βη (embNe n)) (nereadback u)
  _V∋_~_ {Γ = Γ} (a ⇒ b) t f       = ∀{Δ}(ρ : Ren Δ Γ)(s : Tm Δ a)(u : Val Δ a)
    (s~u : a V∋ s ~ u) → b C∋ (app (ren ρ t) s) ~ (apply (renval ρ f) u)

  VLR : ∀{Γ}(a : Ty) (t : Tm Γ a) (v : Val Γ a) → Set
  VLR a t v = _V∋_~_ a t v

  _C∋_~_ : ∀{Γ}(a : Ty) (t : Tm Γ a) (v? : Delay ∞ (Val Γ a)) → Set
  a C∋ t ~ v? = Delay₁ ∞ (VLR a t) v?

_~E_ : ∀{Γ Δ} (σ : Sub Γ Δ) (ρ : Env Γ Δ) → Set
ε       ~E ε       = ⊤
(σ , t) ~E (ρ , v) = σ ~E ρ × _ V∋ t ~ v

V∋subst : ∀{Γ}{a : Ty}{t t' : Tm Γ a}{v : Val Γ a} → a V∋ t ~ v → t ≡ t' →
          a V∋ t' ~ v
V∋subst p refl = p

≡to≡βη : ∀{Γ a}{t t' : Tm Γ a} → t ≡ t' → t ≡βη t'
≡to≡βη refl = refl≡ _

ren≡βη : ∀{Γ a} {t : Tm Γ a}{t' : Tm Γ a} → t ≡βη t' → ∀{Δ}(σ : Ren Δ Γ) →
        ren σ t ≡βη ren σ t'
ren≡βη (var≡ p)     σ = var≡ _
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
ren≡βη (eta≡ t) σ = trans≡ (abs≡ (app≡ (≡to≡βη (trans (sym $ rencomp (liftr σ) (wkr renId) t) (trans (cong (λ xs → ren xs t) (trans (lemrr (wkr σ) zero renId) (trans (ridr (wkr σ)) (trans (cong wkr (sym $ lidr σ)) (sym $ wkrcomp renId σ))))) (rencomp (wkr renId) σ t)))) (refl≡ _))) (eta≡ _)
ren≡βη (refl≡ t)        σ = refl≡ _
ren≡βη (sym≡ p)     σ = sym≡ (ren≡βη p σ)
ren≡βη (trans≡ p q) σ = trans≡ (ren≡βη p σ) (ren≡βη q σ)

-- do we need this?
V∋subst' : ∀{Γ}(a : Ty){t t' : Tm Γ a}{v : Val Γ a} → a V∋ t ~ v → t ≡βη t' →
          a V∋ t' ~ v
V∋subst' ★ {t}{t'}{ne n} p q = transD
  (λ n₁ → t' ≡βη embNe n₁)
  (≈sym $ bind-now _)
  (mapD
    (λ n₁ → t ≡βη embNe n₁)
    (λ n₁ → t' ≡βη embNe n₁)
    id
    (λ r → trans≡ (sym≡ q) r) p)
V∋subst' (a ⇒ b) {t}{t'} p q ρ s u r = transD
  (λ v → b V∋ app (ren ρ t') s ~ v)
  (≈sym $ bind-now _)
  (mapD
    (λ v → b V∋ app (ren ρ t) s ~ v)
    (λ v → b V∋ app (ren ρ t') s ~ v)
    id
    (λ {v} r → V∋subst' b r (app≡ (ren≡βη q ρ) (refl≡ _))) (p ρ s u r))

renV∋ : ∀{Γ} a {t : Tm Γ a}{v :  Val Γ a} → a V∋ t ~ v →
           ∀{Δ}(σ : Ren Δ Γ) → a V∋ ren σ t ~ renval σ v
renV∋ ★       {t}{ne u} p σ = transD
  (λ n → ren σ t ≡βη embNe n)
  (rennereadback σ u)
  (mapD    (λ n → t ≡βη embNe n)
           (λ n → ren σ t ≡βη embNe n)
           (rennen σ)
           (λ p → trans≡ (ren≡βη p σ) (≡to≡βη (renembNe _ σ)))
           p)
renV∋ (a ⇒ b){t}{v} p σ ρ s u s~u =
  transD (λ v₁ → b V∋ app (ren ρ (ren σ t)) s ~ v₁)
         (≈trans (≈sym $ bind-now (apply (renval (renComp ρ σ) v) u))
                 (subst (λ x → apply x u ≈ apply (renval ρ (renval σ v)) u)
                        (renvalcomp ρ σ v)
                        (≈refl refl _)))
         (mapD
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

fundvar : ∀{Γ a} (x : Var Γ a) →
  ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env Δ Γ} (σ~ρ : σ ~E ρ) →
  a V∋ looks σ x ~ lookup x ρ
fundvar zero    {σ = σ , t} {ρ , v} (_ , p) = p
fundvar (suc x) {σ = σ , t} {ρ , v} (p , _) = fundvar x p

fundapp : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{f : Val Γ (a ⇒ b)} →
         (a ⇒ b) V∋ t ~ f →
         {u : Tm Γ a}{v : Val Γ a}  →
         a V∋ u ~ v →
         b C∋ app t u ~ apply f v
fundapp {Γ}{a}{b}{t}{f} p {u}{v} q = transD
  (VLR b (app t u))
  (≈sym $ bind-now (apply f v))
  (mapD
    (VLR b (app (ren renId t) u))
    (VLR b (app t u))
    id
    (λ p → V∋subst p (cong (λ t → app t u) (renid t)))
    (transD (VLR b (app (ren renId t) u))
            (subst (λ x → apply x v ≈ apply f v) (sym $ renvalid f)  (≈refl refl _))
            (p renId u v q)))

-- do we need this?
mutual
  C∋map : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{f : Val Γ (a ⇒ b)} →
          (a ⇒ b) V∋ t ~ f →
          {u : Tm Γ a}{v : Delay ∞ (Val Γ a)}  →
          a C∋ u ~ v →
          b C∋ app t u ~ (v >>= apply f)
  C∋map f (now₁ p)   = fundapp f p
  C∋map f (later₁ p) = later₁ (∞C∋map f p)

  ∞C∋map : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{f : Val Γ (a ⇒ b)} →
           (a ⇒ b) V∋ t ~ f →
           {u : Tm Γ a}{v : ∞Delay ∞ (Val Γ a)}  →
           ∞Delay₁ ∞ (VLR a u) v →
           ∞Delay₁ ∞ (VLR b (app t u)) (v ∞>>= apply f)
  force₁ (∞C∋map f v) = C∋map f (force₁ v)

-- do we need this?
mutual
  _C∋<*>_ : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{f : Delay ∞ (Val Γ (a ⇒ b))} →
            (a ⇒ b) C∋ t ~ f →
            {u : Tm Γ a}{v : Delay ∞ (Val Γ a)}  →
            a C∋ u ~ v →
            b C∋ app t u ~ (f >>= λ f → v >>= apply f)
  now₁   f C∋<*> v = C∋map f v
  later₁ f C∋<*> v = later₁ (f ∞C∋<*> v)

  _∞C∋<*>_ : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{f : ∞Delay ∞ (Val Γ (a ⇒ b))} →
             ∞Delay₁ ∞ (VLR (a ⇒ b) t) f →
             {u : Tm Γ a}{v : Delay ∞ (Val Γ a)}  →
             a C∋ u ~ v →
             ∞Delay₁ ∞ (VLR b (app t u)) (f ∞>>= λ f → v >>= apply f)
  force₁ (f ∞C∋<*> v) = force₁ f C∋<*> v

mutual
  fund : ∀{Γ a} (t : Tm Γ a) →
    ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env Δ Γ} (σ~ρ : σ ~E ρ) →
    a C∋ sub σ t ~ eval t ρ
  fund (var x)   p = now₁ (fundvar x p)
  fund {a = a ⇒ b} (abs t){Δ} {σ}{ρ}   p = now₁ λ {Δ'} ρ' s u p' → later₁ $
    ∞transD
      (VLR b (app (ren ρ' (sub σ (abs t))) s))
      (∞≈sym $ ∞bind-now _)
      (∞mapD
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
  fund (app t u) p = fund t p C∋<*> fund u p

  ∞beta : ∀{Γ a b} (t : Tm (Γ , a) b) →
    ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env Δ Γ} (σ~ρ : σ ~E ρ) →
    {s : Tm Δ a}{v : Val Δ a} → a V∋ s ~ v →
    ∞Delay₁ ∞ (VLR b (sub (σ , s) t)) (beta t ρ v)
  force₁ (∞beta t p p') = fund t (p , p')

lemma : ∀{Γ a b}
        {t : Tm Γ (a ⇒ b)}{s : Tm Γ a}{f : NeVal Γ (a ⇒ b)}{u : Val Γ a} →
        Delay₁ ∞ (λ n → t ≡βη embNe n) (nereadback f) →
        Delay₁ ∞ (λ n → s ≡βη embNf n) (readback u) →
        Delay₁ ∞ (λ n → app t s ≡βη embNe n) (nereadback (app f u))
lemma {t = t}{s}{f}{u} p q = bindD
    (λ n → t ≡βη embNe n)
    (λ n → app t s ≡βη embNe n)
    (λ f → readback u >>= (λ u → now (app f u)))
    (λ f p → bindD (λ n → s ≡βη embNf n)
                   (λ n → app t s ≡βη embNe n)
                   (λ a → now (app f a))
                   (λ a q → now₁ (app≡ p q)) q )
    p

mutual
  reify : ∀{Γ} a {t : Tm Γ a}{v : Val Γ a} →
          a V∋ t ~ v → Delay₁ ∞ (λ n → t ≡βη embNf n) (readback v)
  reify ★      {t}{ne u} p =
    mapD (λ n → t ≡βη embNe n) (λ n → t ≡βη embNf n) ne id p
  reify (a ⇒ b){t}       p = later₁ $ reify-eta $
    bindD
      (VLR b (app (ren (wkr renId) t) (var zero)))
      (λ n → app (ren (wkr renId) t) (var zero) ≡βη embNf n)
      readback
      (λ v → reify b {v = v})
      (p (wkr renId) (var zero) (ne (var zero))
      (reflect a {t = var zero}{var zero} (now₁ (refl≡ _))))

  reify-eta : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{v : Val Γ (a ⇒ b)} →
             Delay₁
               ∞
               (λ n → app (ren (wkr renId) t) (var zero) ≡βη embNf n)
               (apply (renval (wkr renId) v) (ne (var zero)) >>= readback) →
             ∞Delay₁ ∞ (λ n → t ≡βη embNf n) (eta v ∞>>= (λ x' → now (abs x')))
  force₁ (reify-eta {a = a}{b}{t}{v} p) =
    mapD (λ n → app (ren (wkr renId) t) (var zero) ≡βη embNf n)
         (λ n → t ≡βη embNf n)
         Nf.abs
         (λ p → trans≡ (sym≡ (eta≡ _)) (abs≡ p))
         p

  reflect : ∀{Γ} a {t : Tm Γ a}{u : NeVal Γ a} →
            Delay₁ ∞ (λ n → t ≡βη embNe n) (nereadback u) → a V∋ t ~ (ne u)
  reflect ★       p         = p
  reflect (a ⇒ b){t}{f} p ρ s u q = now₁ $ reflect b $ lemma
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
~var x = reflect _ (now₁ (refl≡ _))

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
soundness Γ a t = bindD
  (VLR a (sub subId t))
  (λ n → t ≡βη embNf n )
  readback
  (λ v p → transP (λ n → sub subId t ≡βη embNf n)
                  (λ n → t ≡βη embNf n)
                  (trans≡ (≡to≡βη (sym $ subid t)))
                  (reify a p))
  (fund t (ide~E Γ))
-- -}
