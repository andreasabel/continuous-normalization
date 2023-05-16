-- This module shows soundness of the evaluator without relying on
-- Termination.

-- We show that readback after evaluation gives, if it terminates, a
-- normal form that is βη-equal to the term we started with.

module Soundness where

open import Library
open import Delay
open import Syntax
open import RenamingAndSubstitution
open import Evaluation
open import EquationalTheory

infix 8 _V∋_~_

-- Conditional βη-equality between a term and a delayed normal form.
-- Classically: If the nf terminates, it is equal to the term.

_≡βη⟨_⟩?_ : ∀{Γ a} (t : Tm Γ a) (i : Size) (n? : Delay ∞ (Nf Γ a)) → Set
t ≡βη⟨ i ⟩? n? = Delay₁ i (λ n → t ≡βη (embNf n)) n?

_≡βη?_ : ∀{Γ a} (t : Tm Γ a) (n? : Delay ∞ (Nf Γ a)) → Set
t ≡βη? n? = t ≡βη⟨ ∞ ⟩? n?

_≡βη⟨_⟩?∞_ : ∀{Γ a} (t : Tm Γ a) (i : Size) (n∞ : ∞Delay ∞ (Nf Γ a)) → Set
t ≡βη⟨ i ⟩?∞ n∞ = ∞Delay₁ i (λ n → t ≡βη (embNf n)) n∞

_≡βη?∞_ : ∀{Γ a} (t : Tm Γ a) (n∞ : ∞Delay ∞ (Nf Γ a)) → Set
t ≡βη?∞ n? = t ≡βη⟨ ∞ ⟩?∞ n?

_≡βη?ne_ : ∀{Γ a} (t : Tm Γ a) (n? : Delay ∞ (Ne Γ a)) → Set
t ≡βη?ne n? = Delay₁ ∞ (λ n → t ≡βη (embNe n)) n?

-- Logical relation t ~ v  for  t ≡βη readback v

_V∋_~_ : ∀{Γ}(a : Ty) (t : Tm Γ a) (v : Val ∞ Γ a) → Set

-- At base type: put it what we want to harvest.
_V∋_~_         ★       t u  =

  t ≡βη⟨ ∞ ⟩?  (readback u)

-- Function type: the usual Krikpe function space.
_V∋_~_ {Γ = Γ} (a ⇒ b) t f =

  ∀{Δ} (ρ : Ren Δ Γ) (s : Tm Δ a) (u : Val ∞ Δ a)
   (s~u : a V∋ s ~ u) → b V∋ (app (ren ρ t) s) ~ (apply (renval ρ f) u)

-- Pointwise lifting of logical relation to substitutions and environments.

_~E_ : ∀{Γ Δ} (σ : Sub Γ Δ) (ρ : Env ∞ Γ Δ) → Set
ε       ~E ε       = ⊤
(σ , t) ~E (ρ , v) = σ ~E ρ × _ V∋ t ~ v

-- Trivial lemma: LR is closed under propositional equality of terms.

V∋subst : ∀{Γ}{a : Ty}{t t' : Tm Γ a}{v : Val ∞ Γ a} → a V∋ t ~ v → t ≡ t' →
          a V∋ t' ~ v
V∋subst p refl = p

-- Conditional βη-equality is closed under βη-equality of terms.

mutual
  Dsubstβη : ∀{i Γ a}{t t' : Tm Γ a}{v : Delay ∞ (Nf Γ a)} →
             t ≡βη⟨ i ⟩? v → t ≡βη t' →
             t' ≡βη⟨ i ⟩? v
  Dsubstβη (now₁ p)   q = now₁ $ trans≡ (sym≡ q) p
  Dsubstβη (later₁ x) q = later₁ (∞Dsubstβη x q)

  ∞Dsubstβη : ∀{i Γ a} {t t' : Tm Γ a}{v : ∞Delay ∞ (Nf Γ a)} →
             t ≡βη⟨ i ⟩?∞ v → t ≡βη t' →
             t' ≡βη⟨ i ⟩?∞ v
  force₁ (∞Dsubstβη p q) = Dsubstβη (force₁ p) q

-- LR is closed under βη-equality of terms.

V∋substβη : ∀{Γ} a {t t' : Tm Γ a}{v : Val ∞ Γ a} → a V∋ t ~ v → t ≡βη t' →
          a V∋ t' ~ v
V∋substβη ★       p q = Dsubstβη p q
V∋substβη (a ⇒ b) p q ρ s u s~u =
  V∋substβη b (p ρ s u s~u) (app≡ (ren≡βη q ρ) (refl≡ s refl))

-- LR is closed under strong bisimilarity of values.

V∋subst' : ∀{Γ} a {t  : Tm Γ a}{v v' :  Val ∞ Γ a} →
            Val∋ v ≈ v' → a V∋ t ~ v → a V∋ t ~ v'
V∋subst' ★       p q = transD (λ n → _ ≡βη embNf n) (readback-cong _ p) q
V∋subst' (a ⇒ b) p q ρ s u s~u =
  V∋subst' b (apply-cong (renval-cong ρ p) (≈reflVal u)) (q ρ s u s~u)

-- LR is closed under "later".

V∋step : ∀{Γ} a {t  : Tm Γ a}{v : ∞Val ∞ Γ a} →
         a V∋ t ~ force v → a V∋ t ~ later v
V∋step ★ p = later₁ (delay₁ p)
V∋step (a ⇒ b) p ρ s u s~u = V∋step b (p ρ s u s~u)

-- LR is closed under renaming.

renV∋ : ∀{Γ} a {t : Tm Γ a}{v :  Val ∞ Γ a} → a V∋ t ~ v →
           ∀{Δ}(σ : Ren Δ Γ) → a V∋ ren σ t ~ renval σ v
renV∋ ★       {t}{u} p σ =
 transD
  (λ n → ren σ t ≡βη embNf n)
  (renreadback _ σ u)
  (mapD    (λ n → t ≡βη embNf n)
           (λ n → ren σ t ≡βη embNf n)
           (rennf σ)
           (λ {n} p -> trans≡ (ren≡βη p σ) (refl≡ _ (renembNf n σ)))
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

-- Lemmata for fundamental theorem

fundvar : ∀{Γ a} (x : Var Γ a) →
  ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env ∞ Δ Γ} (σ~ρ : σ ~E ρ) →
  a V∋ looks σ x ~ lookup x ρ
fundvar zero    {σ = σ , t} {ρ , v} (_ , p) = p
fundvar (suc x) {σ = σ , t} {ρ , v} (p , _) = fundvar x p

fundapp : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{f : Val ∞ Γ (a ⇒ b)} →
         {u : Tm Γ a}{v : Val ∞ Γ a}  →

         (a ⇒ b) V∋ t ~ f →
         a       V∋ u ~ v →
         ------------------------
         b V∋ app t u ~ apply f v

fundapp {Γ}{a}{b}{t}{f}{u}{v} p q =
  V∋subst (V∋subst' b
                    (apply-cong (renvalid f) (≈reflVal v))
                    (p renId u v q))
          (cong (λ t → app t u) (renid t))

-- Fundamental theorem, proving soundness of evaluation.

fund : ∀{Γ a} (t : Tm Γ a) →
    ∀ {Δ} {σ : Sub Δ Γ} {ρ : Env ∞ Δ Γ} (σ~ρ : σ ~E ρ) →
    a V∋ sub σ t ~ eval t ρ

-- Case: variable.
fund (var x)   p = fundvar x p

-- Case: abstraction.
fund {a = a ⇒ b} (abs t){Δ} {σ}{ρ}   p ρ' s u s~u = V∋substβη
  b
  (V∋step b (fund
    t
    {σ = subComp (ren2sub ρ') σ , s}
    {ρ = renenv ρ' ρ , u}
    (ren~E p ρ' , s~u)))
  (trans≡ (refl≡ _ (trans
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

-- Case: application.
fund (app t u) p =
    V∋subst (V∋subst' _
                      (apply-cong (renvalid (eval t _)) (≈reflVal (eval u _)))
                      (fund t p renId _ _ (fund u p)))
            (cong (λ f → app f (sub _ u)) (renid _))


-- Conditional βη-equality is closed under application.

reflect-app : ∀{Γ a b}
        {t : Tm Γ (a ⇒ b)}
        {s : Tm Γ a}
        {f : NeVal ∞ Γ (a ⇒ b)}
        {u : Val ∞ Γ a} →
        t ≡βη?ne (nereadback f) →
        s ≡βη? (readback u) →
        app t s ≡βη?ne (nereadback (app f u))
reflect-app {t = t}{s}{f}{u} p q = mapD2
  (λ n → t ≡βη embNe n)
  (λ n → s ≡βη embNf n)
  (λ n → app t s ≡βη embNe n)
  GNe.app
  app≡
  p
  q

-- Reflection and reification.

mutual

  -- Reification.

  reify : ∀{Γ} a {t : Tm Γ a}{v : Val ∞ Γ a} →

          a V∋ t ~ v →
          -------------------
          t ≡βη? (readback v)

  reify ★      {t}{u} p = p
  reify (a ⇒ b){t}       p = later₁
    (reify-eta
      (reify b
             (p (wkr renId)
                (var zero)
                (ne (var zero))
                (reflect a (now₁ (var≡ zero))))))

  reify-eta : ∀{Γ a b}{t : Tm Γ (a ⇒ b)}{v : Val ∞ Γ (a ⇒ b)} →

             app (weak _ t) (var zero) ≡βη?
               (readback (apply (renval (wkr renId) v) (ne (var zero)))) →
             -----------------------------------------------------------
             t ≡βη?∞ (abs ∞<$> eta v)

  force₁ (reify-eta {t = t}{v} p) =
    mapD (λ n → app (weak _ t) (var zero) ≡βη embNf n)
         (λ n → t ≡βη embNf n)
         Nf.abs
         (λ p → trans≡ (sym≡ (eta≡ t)) (abs≡ p))
         p

  -- Reflection.

  reflect : ∀{Γ} a {t : Tm Γ a}{u : NeVal ∞ Γ a} →

            t ≡βη?ne (nereadback u) →
            -----------------------
            a V∋ t ~ ne u

  reflect ★       p         =
    mapD (λ n → _ ≡βη embNe n) (λ n → _ ≡βη embNf n) ne id p

  reflect (a ⇒ b){t}{f} p ρ s u q = reflect b  $ reflect-app
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
        (λ {n} p → trans≡ (ren≡βη p ρ) (refl≡ _ (renembNe n ρ)))
        p) )
    (reify a {s}{u} q)

-- Reflection of variables.

~var : ∀{Γ a}(x : Var Γ a) → a V∋ var x ~ ne (var x)
~var x = reflect _ (now₁ (var≡ x))

-- Identity substitution is related to identity environment.

ide~E : ∀ Γ → subId {Γ} ~E ide Γ
ide~E ε       = _
ide~E (Γ , a) =
  subst (λ x → x ~E renenv (wkr renId) (ide Γ))
        (trans (wkrscomp renId subId)
               (cong wks (trans (sidr (ren2sub renId)) (sym $ ren2subid ))))
        (ren~E (ide~E  Γ) (wkr renId))
  ,
  ~var zero

-- Soundness of normalization.
-- If normal form exists it is βη-equal to original term.

soundness : ∀ Γ a (t : Tm Γ a) → t ≡βη? nf t
soundness Γ a t = reify a (V∋subst (fund t (ide~E Γ)) (subid t))
