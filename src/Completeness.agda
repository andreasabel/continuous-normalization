{-# OPTIONS --copatterns --sized-types --rewriting #-}

module Completeness where

open import Library
open import Delay
open import WeakBisim
open import Syntax
open import RenamingAndSubstitution
open import Evaluation
open import EquationalTheory
--open import Termination using (rennereadback⇓)

{-# BUILTIN REWRITE _≡_ #-}

mutual

  -- Values v and v' are related at type a.
  _V∋_≃_ : ∀{Γ}(a : Ty) (v v' : Val ∞ Γ a) → Set
  _V∋_≃_     ★        v v' = 
    Delay_∋_~_ _≡_
               (readback v) 
               (readback v')
  _V∋_≃_ {Γ} (a ⇒ b) f f' = ∀{Δ}(η : Ren Δ Γ)(u u' : Val ∞ Δ a)
    (u≃u' : a V∋ u ≃ u') → 
    b V∋ (apply (renval η f) u) ≃ (apply (renval η f') u')

  VLR : ∀{Γ}(a : Ty) (v v' : Val ∞ Γ a) → Set
  VLR a v v' = _V∋_≃_ a v v'

-- Environments ρ and ρ' are related.
_≃E_ : ∀{Γ Δ} (ρ ρ' : Env ∞ Δ Γ) → Set
ε       ≃E ε         = ⊤
(ρ , v) ≃E (ρ' , v') = (ρ ≃E ρ') × (VLR _ v v')

-- subst by strong bisim for val
substVLR-l : ∀{Γ} a {v v' v'' : Val ∞ Γ a} →
             VLR a v v' →  Val∋ v'' ≈⟨ ∞ ⟩≈ v → VLR a v'' v'
substVLR-l ★       p q = ~trans trans (≈→~ $ readback-cong ★ q) p
substVLR-l (a ⇒ b) p q η u u' u≃u' =
  substVLR-l b (p η u u' u≃u') (apply-cong (renval-cong η q) (≈reflVal u))

substVLR-r : ∀{Γ} a {v v' v'' : Val ∞ Γ a} →
             VLR a v v' →  Val∋ v' ≈⟨ ∞ ⟩≈ v'' → VLR a v v''
substVLR-r ★       p q = ~trans trans p (≈→~ $ readback-cong ★ q)
substVLR-r (a ⇒ b) p q η u u' u≃u' = 
   substVLR-r b (p η u u' u≃u') (apply-cong (renval-cong η q) (≈reflVal u'))

subst≃E-l : ∀{Γ Δ}{ρ ρ' ρ'' : Env ∞ Γ Δ} →
             ρ ≃E ρ' →  Env∋ ρ'' ≈⟨ ∞ ⟩≈ ρ → ρ'' ≃E ρ'
subst≃E-l {Δ = ε}  {ρ' = ε}{ρ'' = ε} p q = _
subst≃E-l {Δ = Δ , a} {ρ , v}{ ρ' , v'} {ρ'' , v''} (p , p') (q ≈, q') = 
  subst≃E-l p q , substVLR-l _ p' q'

subst≃E-r : ∀{Γ Δ}{ρ ρ' ρ'' : Env ∞ Γ Δ} →
             ρ ≃E ρ' →  Env∋ ρ' ≈⟨ ∞ ⟩≈ ρ'' → ρ ≃E ρ''
subst≃E-r {Δ = ε}  {ρ = ε}{ρ'' = ε} p q = _
subst≃E-r {Δ = Δ , a} {ρ , v}{ ρ' , v'} {ρ'' , v''} (p , p') (q ≈, q') = 
  subst≃E-r p q , substVLR-r _ p' q'

VLR-sym : ∀{Γ} a {v v' : Val ∞ Γ a} → VLR a v v' → VLR a v' v
VLR-sym ★       p = ~sym sym p
VLR-sym (a ⇒ b) p η u u' u≃u' = VLR-sym b (p η u' u (VLR-sym a u≃u'))

VLR-trans : ∀{Γ} a {v v' v'' : Val ∞ Γ a} →
            VLR a v v' → VLR a v' v'' → VLR a v v''
VLR-trans ★       p q = ~trans trans p q
VLR-trans (a ⇒ b) p q η u u' u≃u' =
  VLR-trans b (p η u u (VLR-trans a u≃u' (VLR-sym a u≃u'))) (q η u u' u≃u')

VLR-refl : ∀{Γ} a {v v' : Val ∞ Γ a} → VLR a v v' → VLR a v v
VLR-refl a p = VLR-trans a p (VLR-sym a p)

≃Esym : ∀{Γ Δ}{ρ ρ' : Env ∞ Δ Γ} → ρ ≃E ρ' → ρ' ≃E ρ
≃Esym {ρ = ε}    {ε}       _        = _
≃Esym {ρ = ρ , v}{ρ' , v'} (p , p') = ≃Esym p  , VLR-sym _ p'

≃Etrans : ∀{Γ Δ}{ρ ρ' ρ'' : Env ∞ Δ Γ} → ρ ≃E ρ' → ρ' ≃E ρ'' → ρ ≃E ρ''
≃Etrans {ρ = ε}    {ε}       {ε}         _         _        = _
≃Etrans {ρ = ρ , v}{ρ' , v'} {ρ'' , v''} (p , q)  (p' , q') =
  ≃Etrans p p' , VLR-trans _ q q'

≃Erefl : ∀{Γ Δ}{ρ ρ' : Env ∞ Δ Γ} → ρ ≃E ρ' → ρ ≃E ρ
≃Erefl p = ≃Etrans p (≃Esym p)

-- Closure under renaming

renV≃ : ∀{Δ Δ′} a (η : Ren Δ′ Δ) {v v' : Val ∞ Δ a} (v≃v' : VLR a v v') →
        VLR a (renval η v) (renval η v')
renV≃ ★       η {n}{n'} p    = ~trans
  trans
  (≈→~ (≈sym $ renreadback ★ η n))
  (~trans trans
          (map~ (rennf η) (λ _ _ → cong (rennf η)) p)
          (≈→~ $ renreadback ★ η n'))
renV≃ (a ⇒ b) η {f}{f'} p ρ u u' q =
  substVLR-r b
             (substVLR-l b
                         (p (renComp ρ η) u u' q)
                         (apply-cong (renvalcomp ρ η f) (≈reflVal u)))
             (apply-cong (≈symVal (renvalcomp ρ η f')) (≈reflVal u'))

renE≃ : ∀{Γ Δ Δ′} (η : Ren Δ′ Δ) {ρ ρ' : Env ∞ Δ Γ}
        (ρ≃ρ' : ρ ≃E ρ') → (renenv η ρ) ≃E (renenv η ρ')
renE≃ η {ε} {ε} ρ≃ρ' = _
renE≃ η {ρ , v} {ρ' , v'} (ρ≃ρ' , v≃v') = (renE≃ η ρ≃ρ') , (renV≃ _ η v≃v')

-- closure under 2 laters
laterV≃ : ∀{Γ} a {v v' : ∞Val ∞ Γ a} → VLR a (∞Val.force v) (∞Val.force v') →
          VLR a (later v) (later v')
laterV≃ ★       p = ~later (~delay p)
laterV≃ (a ⇒ b) p η u u' u≃u' = laterV≃ b (p η u u' u≃u')

laterV≃-l : ∀{Γ} a {v : ∞Val ∞ Γ a}{v' : Val ∞ Γ a} →
            VLR a (∞Val.force v) v' →
            VLR a (later v) v'
laterV≃-l ★ p = ~laterl p
laterV≃-l (a ⇒ b) p η u u' u≃u' = laterV≃-l b (p η u u' u≃u')

id-ext-var : ∀{Γ Δ a}(x : Var Δ a){ρ ρ' : Env ∞ Γ Δ} → ρ ≃E ρ' →
             a V∋ lookup x ρ ≃ lookup x ρ'
id-ext-var zero    {ρ , v}{ρ' , v'} (p , p') = p'
id-ext-var (suc x) {ρ , v}{ρ' , v'} (p , p') = id-ext-var x p

lookupR-cong : ∀{Γ Γ' Δ}(σ : Ren Γ Γ'){ρ ρ' : Env ∞ Δ Γ} → ρ ≃E ρ' → 
               lookupR σ ρ ≃E lookupR σ ρ'
lookupR-cong ε       p = _
lookupR-cong (σ , x) p = lookupR-cong σ p , id-ext-var x p

id-ext : ∀{Γ Δ a}(t : Tm Δ a){ρ ρ' : Env ∞ Γ Δ} → ρ ≃E ρ' →
         a V∋ eval t ρ ≃ eval t ρ'
id-ext (var x)   p = id-ext-var x p
id-ext (abs t)  {ρ}{ρ'} p η u u' u≃u' =
  laterV≃ _ (id-ext t {renenv η ρ , u}{renenv η ρ' , u'}(renE≃ η p , u≃u'))
id-ext (app t u) p =
  substVLR-r _
             (substVLR-l _
                         (id-ext t p renId _ _ (id-ext u p))
                         (apply-cong (≈symVal (renvalid (eval t _)))
                                     (eval-cong u (≈reflEnv _))))
             ((apply-cong (renvalid (eval t _))
                                     (eval-cong u (≈reflEnv _))))

reneval' : ∀ {Γ Γ' Δ a}(t : Tm Γ a)(σ : Ren Γ' Γ)(ρ : Env ∞ Δ Γ') → 
           ρ ≃E ρ → 
           VLR a (eval (ren σ t) ρ) (eval t (lookupR σ ρ))
reneval' (var x)   σ ρ p = substVLR-l _ (id-ext-var x (lookupR-cong σ p)) (lookuplookr ρ σ x)
reneval' (abs t)   σ ρ p η u u' q = laterV≃ _ (VLR-trans _ (reneval' t (liftr σ) (renenv η ρ , u) (renE≃ η p , VLR-refl _ q)) (id-ext t (subst≃E-l (subst≃E-l (renE≃ η (lookupR-cong σ p)) (≈symEnv (renlookupR η σ ρ)) ) (≈symEnv (lookupRwkr u σ (renenv η ρ)))  , q)) )
reneval' (app t u) σ ρ p = substVLR-r _ (substVLR-l _ (reneval' t σ ρ p renId _ _ (reneval' u σ ρ p)) ( apply-cong (≈symVal (renvalid (eval (ren σ t) ρ))) (≈reflVal (eval (ren σ u) ρ)) )) (apply-cong (renvalid (eval t (lookupR σ ρ))) (≈reflVal (eval u (lookupR σ ρ))))

evalSwks : ∀{Γ Δ Δ′ a}
           (u : Val ∞ Δ′ a)(ρ : Env ∞ Δ′ Δ)(σ : Sub Δ Γ) →
           ρ ≃E ρ → VLR a u u → evalS σ ρ ≃E evalS (wks σ) (ρ , u)
evalSwks u ρ ε       p q = _
evalSwks u ρ (σ , t) p q =
  evalSwks u ρ σ p q , VLR-trans _ (id-ext t (subst≃E-r p (≈transEnv (≈symEnv (lookupRrenId ρ)) (lookupRwkr u renId ρ)) )) (VLR-sym _ (reneval' t (wkr renId) (ρ , u) (p , q)))

-- this should go away
evalSwks' : ∀{Γ Δ Δ₁ Δ′ a}
           (u : Val ∞ Δ₁ a)(η : Ren Δ₁ Δ′)(ρ : Env ∞ Δ′ Δ)(σ : Sub Δ Γ) →
           ρ ≃E ρ → VLR a u u →  renenv η (evalS σ ρ) ≃E evalS (wks σ) (renenv η ρ , u)
evalSwks' u η ρ ε p q = _
evalSwks' u η ρ (σ , t) p q =  evalSwks' u η ρ σ p q , VLR-trans _ (substVLR-l _ (id-ext t (subst≃E-r (subst≃E-r (renE≃ η p) (≈symEnv (lookupRrenId (renenv η ρ)))) (lookupRwkr u renId (renenv η ρ)))) (reneval t ρ η)) (VLR-sym _ (reneval' t (wkr renId) (renenv η ρ , u) (renE≃ η p , q)))   

evalSsubId : ∀{Γ Δ}(ρ : Env ∞ Γ Δ) → ρ ≃E ρ → ρ ≃E evalS subId ρ
evalSsubId ε       _       = _
evalSsubId (ρ , v) (p , q) =
  ≃Etrans (evalSsubId ρ p) (evalSwks v ρ subId p q) , q

substitution-var : ∀{Γ Δ Δ′ a} (x : Var Γ a) (σ : Sub Δ Γ) (ρ : Env ∞ Δ′ Δ) →
  ρ ≃E  ρ → a V∋ (lookup x (evalS σ ρ)) ≃ eval (looks σ x) ρ
substitution-var zero    (σ , t) ρ p = id-ext t p
substitution-var (suc x) (σ , t) ρ p = substitution-var x σ ρ p

-- the reflexive equation for ρ could be reduced to knowing that after
-- infinite delay the reading back the values in ρ will converge, or
-- perhaps the substitution lemma should take two different related
-- environments.
substitution : ∀{Γ Δ Δ′ a} (t : Tm Γ a) (σ : Sub Δ Γ) (ρ : Env ∞ Δ′ Δ) →
  ρ ≃E  ρ →  a V∋ (eval t (evalS σ ρ)) ≃ eval (sub σ t) ρ
substitution (var x) σ ρ p = substitution-var x σ ρ p
substitution (abs t) σ ρ p η u u' u≃u' = laterV≃ _ (VLR-trans _ (id-ext t (evalSwks' u' η ρ σ p (VLR-refl _ (VLR-sym _ u≃u')) , u≃u')) (substitution t (lifts σ) (renenv η ρ , u') (renE≃ η p , VLR-refl _ (VLR-sym _ u≃u'))))
substitution (app t u) σ ρ p = substVLR-r _ (substVLR-l _ (substitution t σ ρ p renId _ _ (substitution u σ ρ p)) (apply-cong (≈symVal (renvalid (eval t (evalS σ ρ)))) (≈reflVal (eval u (evalS σ ρ))))) ((apply-cong (renvalid (eval (sub σ t) ρ))) (≈reflVal (eval (sub σ u) ρ))) 

fund : ∀{Γ Δ a}{t t' : Tm Δ a} → t ≡βη t' → {ρ ρ' : Env ∞ Γ Δ} → ρ ≃E ρ' →
         a V∋ eval t ρ ≃ eval t' ρ'
fund (var≡ x) q = id-ext-var x q
fund (abs≡ p) q η u u' u≃u' = laterV≃ _ (fund p (renE≃ η q , u≃u'))
fund (app≡ {t = t}{t'}{u}{u'} p p') q = substVLR-r _ (substVLR-l _ (fund p q renId _ _ (fund p' q)) (apply-cong (≈symVal (renvalid (eval t _))) (≈reflVal (eval u _)))) (apply-cong (renvalid (eval t' _)) (≈reflVal (eval u' _)))
fund (beta≡ {t = t}{u = u}){ρ}{ρ'} q = laterV≃-l _ (VLR-trans _ (id-ext t {ρ , eval u ρ}{ρ' , eval u ρ'} (q , id-ext u q)) (VLR-trans _ (id-ext t (evalSsubId ρ' (≃Erefl (≃Esym q)) , (id-ext u (≃Erefl (≃Esym q))))) (substitution t (subId , u) ρ' (≃Erefl (≃Esym q)))))
fund (eta≡ t') {ρ}{ρ'} q η u u' u≃u' = laterV≃-l _ (substVLR-l _ (VLR-trans _ (reneval' t' (wkr renId) (renenv η ρ , u) ((renE≃ η (≃Erefl q)) , (VLR-refl _ u≃u')) renId u u' u≃u') (substVLR-l _ (substVLR-l _ (substVLR-l _ (id-ext t' q η u' u' (VLR-refl _ (VLR-sym _ u≃u'))) (apply-cong (≈symVal (reneval t' ρ η)) (≈reflVal u'))) (≈symVal (apply-cong (eval-cong t' (≈transEnv (≈symEnv (lookupRrenId (renenv η ρ))) (lookupRwkr u renId (renenv η ρ)))) (≈reflVal u')))) (apply-cong (renvalid (eval t' (lookupR (wkr renId) (renenv η ρ , u)))) (≈reflVal u')))) (≈symVal (apply-cong (renvalid (eval (ren (wkr renId) t') (renenv η ρ , u))) (≈reflVal u))) )
fund (refl≡ t') q = id-ext t' q
fund (sym≡ p) q = VLR-sym _ (fund p (≃Esym q))
fund (trans≡ p p') q = VLR-trans _ (fund p (≃Erefl q)) (fund p' q)

-- reify, reflect
mutual
  reify : ∀{Γ} a {v v' : Val ∞ Γ a} →
          a V∋ v ≃ v' →     Delay_∋_~_ _≡_ (readback v) (readback v')
  reify ★       p = p
  reify (a ⇒ b) p = ~later (~delay (map~ abs (λ _ _ → cong abs) (reify b (p (wkr renId) _ _ (reflect a {var zero}{var zero}(~now now⇓ now⇓ refl))))))

  reflect : ∀{Γ} a {n n' : NeVal ∞ Γ a} →
            Delay_∋_~_ _≡_ (nereadback n) (nereadback n') → a V∋ ne n ≃ ne n'
  reflect ★                    p = map~ ne (λ _ _ → cong ne) p
  reflect (a ⇒ b) {n}{n'} p η u u' u≃u' = reflect b (map2~ app (λ _ _ p _ _ q → cong₂ app p q)
                                               (~trans trans (≈→~ (≈sym (rennereadback η n)))
                                                (~trans trans (map~ (rennen η) (λ _ _ → cong (rennen η)) p) (≈→~ (rennereadback η n'))))
                                               (reify a u≃u'))
idecomp : ∀ Γ → ide Γ ≃E ide Γ
idecomp ε       = _
idecomp (Γ , a) = renE≃ (wkr renId) (idecomp Γ) , reflect a (~now now⇓ now⇓ refl)

completeness : ∀ Γ a {t t' : Tm Γ a} → t ≡βη t' → Delay_∋_~_ _≡_ (nf t) (nf t')
completeness Γ a p = reify a (fund p (idecomp Γ))
