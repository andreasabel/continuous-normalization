module Completeness where

open import Library
open import Delay
open import WeakBisim
open import Syntax
open import RenamingAndSubstitution
open import Evaluation
open import EquationalTheory

-- Values v and v' are related at type a.
_V∋_≃_ : ∀{Γ}(a : Ty) (v v' : Val ∞ Γ a) → Set
★       V∋ v ≃ v' = Delay _≡_ ∋ readback v ~ readback v'
(a ⇒ b) V∋ f ≃ f' = ∀{Δ}(η : Ren Δ _)(u u' : Val ∞ Δ a)(u≃u' : a V∋ u ≃ u') → 
  b V∋ (apply (renval η f) u) ≃ (apply (renval η f') u')

VLR : ∀{Γ}(a : Ty) (v v' : Val ∞ Γ a) → Set
VLR a v v' = _V∋_≃_ a v v'

-- Environments ρ and ρ' are related.
ELR : ∀{Γ Δ} (ρ ρ' : Env ∞ Δ Γ) → Set
ELR ε ε         = ⊤
ELR (ρ , v) (ρ' , v') = ELR ρ ρ' × VLR _ v v'

-- subst by strong bisim
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

substELR-l : ∀{Γ Δ}{ρ ρ' ρ'' : Env ∞ Γ Δ} →
             ELR ρ ρ' →  Env∋ ρ'' ≈⟨ ∞ ⟩≈ ρ → ELR ρ'' ρ'
substELR-l {Δ = ε}  {ρ' = ε}{ρ'' = ε} p q = _
substELR-l {Δ = Δ , a} {ρ , v}{ ρ' , v'} {ρ'' , v''} (p , p') (q ≈, q') = 
  substELR-l p q , substVLR-l _ p' q'

substELR-r : ∀{Γ Δ}{ρ ρ' ρ'' : Env ∞ Γ Δ} →
             ELR ρ ρ' →  Env∋ ρ' ≈⟨ ∞ ⟩≈ ρ'' → ELR ρ ρ''
substELR-r {Δ = ε}  {ρ = ε}{ρ'' = ε} p q = _
substELR-r {Δ = Δ , a} {ρ , v}{ ρ' , v'} {ρ'' , v''} (p , p') (q ≈, q') = 
  substELR-r p q , substVLR-r _ p' q'

-- sym, trans and refl
symVLR : ∀{Γ} a {v v' : Val ∞ Γ a} → VLR a v v' → VLR a v' v
symVLR ★       p = ~sym sym p
symVLR (a ⇒ b) p η u u' u≃u' = symVLR b (p η u' u (symVLR a u≃u'))

transVLR : ∀{Γ} a {v v' v'' : Val ∞ Γ a} →
            VLR a v v' → VLR a v' v'' → VLR a v v''
transVLR ★       p q = ~trans trans p q
transVLR (a ⇒ b) p q η u u' u≃u' =
  transVLR b (p η u u (transVLR a u≃u' (symVLR a u≃u'))) (q η u u' u≃u')

reflVLR : ∀{Γ} a {v v' : Val ∞ Γ a} → VLR a v v' → VLR a v v
reflVLR a p = transVLR a p (symVLR a p)

symELR : ∀{Γ Δ}{ρ ρ' : Env ∞ Δ Γ} → ELR ρ ρ' → ELR ρ' ρ
symELR {ρ = ε}    {ε}       _        = _
symELR {ρ = ρ , v}{ρ' , v'} (p , p') = symELR p  , symVLR _ p'

transELR : ∀{Γ Δ}{ρ ρ' ρ'' : Env ∞ Δ Γ} → ELR ρ ρ' → ELR ρ' ρ'' → ELR ρ ρ''
transELR {ρ = ε}    {ε}       {ε}         _         _        = _
transELR {ρ = ρ , v}{ρ' , v'} {ρ'' , v''} (p , q)  (p' , q') =
  transELR p p' , transVLR _ q q'

reflELR : ∀{Γ Δ}{ρ ρ' : Env ∞ Δ Γ} → ELR ρ ρ' → ELR ρ ρ
reflELR p = transELR p (symELR p)

-- Closure under renaming
renVLR : ∀{Δ Δ′} a (η : Ren Δ′ Δ) {v v' : Val ∞ Δ a} (v≃v' : VLR a v v') →
         VLR a (renval η v) (renval η v')
renVLR ★       η {n}{n'} p    = ~trans
  trans
  (≈→~ (≈sym $ renreadback ★ η n))
  (~trans trans
          (map~ (rennf η) (rennf η) (λ _ _ → cong (rennf η)) p)
          (≈→~ $ renreadback ★ η n'))
renVLR (a ⇒ b) η {f}{f'} p ρ u u' q =
  substVLR-r b
             (substVLR-l b
                         (p (renComp ρ η) u u' q)
                         (apply-cong (renvalcomp ρ η f) (≈reflVal u)))
             (apply-cong (≈symVal (renvalcomp ρ η f')) (≈reflVal u'))

renELR : ∀{Γ Δ Δ′} (η : Ren Δ′ Δ) {ρ ρ' : Env ∞ Δ Γ}
         (ρ≃ρ' : ELR ρ ρ') → ELR (renenv η ρ) (renenv η ρ')
renELR η {ε} {ε} ρ≃ρ' = _
renELR η {ρ , v} {ρ' , v'} (ρ≃ρ' , v≃v') = (renELR η ρ≃ρ') , (renVLR _ η v≃v')

-- later-cong
laterVLR : ∀{Γ} a {v v' : ∞Val ∞ Γ a} → VLR a (∞Val.force v) (∞Val.force v') →
           VLR a (later v) (later v')
laterVLR ★       p = ~later (~delay p)
laterVLR (a ⇒ b) p η u u' u≃u' = laterVLR b (p η u u' u≃u')

-- later on the left cong
laterVLR-l : ∀{Γ} a {v : ∞Val ∞ Γ a}{v' : Val ∞ Γ a} →
             VLR a (∞Val.force v) v' →
             VLR a (later v) v'
laterVLR-l ★ p = ~laterl p
laterVLR-l (a ⇒ b) p η u u' u≃u' = laterVLR-l b (p η u u' u≃u')

-- id extension for variables
id-ext-var : ∀{Γ Δ a}(x : Var Δ a){ρ ρ' : Env ∞ Γ Δ} → ELR ρ ρ' →
             a V∋ lookup x ρ ≃ lookup x ρ'
id-ext-var zero    {ρ , v}{ρ' , v'} (p , p') = p'
id-ext-var (suc x) {ρ , v}{ρ' , v'} (p , p') = id-ext-var x p

-- lookupR cong
lookupR-cong : ∀{Γ Γ' Δ}(σ : Ren Γ Γ'){ρ ρ' : Env ∞ Δ Γ} → ELR ρ ρ' → 
               ELR (lookupR σ ρ) (lookupR σ ρ')
lookupR-cong ε       p = _
lookupR-cong (σ , x) p = lookupR-cong σ p , id-ext-var x p

-- identity extension lemma
id-ext : ∀{Γ Δ a}(t : Tm Δ a){ρ ρ' : Env ∞ Γ Δ} → ELR ρ ρ' →
         a V∋ eval t ρ ≃ eval t ρ'
id-ext (var x)   p = id-ext-var x p
id-ext (abs t)  {ρ}{ρ'} p η u u' u≃u' =
  laterVLR _ (id-ext t {renenv η ρ , u}{renenv η ρ' , u'}(renELR η p , u≃u'))
id-ext (app t u) p =
  substVLR-r _
             (substVLR-l _
                         (id-ext t p renId _ _ (id-ext u p))
                         (apply-cong (≈symVal (renvalid (eval t _)))
                                     (eval-cong u (≈reflEnv _))))
             ((apply-cong (renvalid (eval t _))
                                     (eval-cong u (≈reflEnv _))))

-- pre-renaming lemma
reneval' : ∀ {Γ Γ' Δ a}(t : Tm Γ a)(σ : Ren Γ' Γ)(ρ : Env ∞ Δ Γ') → ELR ρ ρ → 
           VLR a (eval (ren σ t) ρ) (eval t (lookupR σ ρ))
reneval' (var x)   σ ρ p = substVLR-l _ (id-ext-var x (lookupR-cong σ p)) (lookuplookr ρ σ x)
reneval' (abs t)   σ ρ p η u u' q = laterVLR _ (transVLR _ (reneval' t (liftr σ) (renenv η ρ , u) (renELR η p , reflVLR _ q)) (id-ext t (substELR-l (substELR-l (renELR η (lookupR-cong σ p)) (≈symEnv (renlookupR η σ ρ)) ) (≈symEnv (lookupRwkr u σ (renenv η ρ)))  , q)) )
reneval' (app t u) σ ρ p = substVLR-r _ (substVLR-l _ (reneval' t σ ρ p renId _ _ (reneval' u σ ρ p)) ( apply-cong (≈symVal (renvalid (eval (ren σ t) ρ))) (≈reflVal (eval (ren σ u) ρ)) )) (apply-cong (renvalid (eval t (lookupR σ ρ))) (≈reflVal (eval u (lookupR σ ρ))))

-- evaluationg a weakened sub
evalSwks : ∀{Γ Δ Δ′ a}(u : Val ∞ Δ′ a)(ρ : Env ∞ Δ′ Δ)(σ : Sub Δ Γ) →
           ELR ρ ρ → VLR a u u → ELR (evalS σ ρ) (evalS (wks σ) (ρ , u))
evalSwks u ρ ε       p q = _
evalSwks u ρ (σ , t) p q =
  evalSwks u ρ σ p q , transVLR _ (id-ext t (substELR-r p (≈transEnv (≈symEnv (lookupRrenId ρ)) (lookupRwkr u renId ρ)) )) (symVLR _ (reneval' t (wkr renId) (ρ , u) (p , q)))

-- this should go away/ be proven in terms of evalSwks
evalSwks' : ∀{Γ Δ Δ₁ Δ′ a}
            (u : Val ∞ Δ₁ a)(η : Ren Δ₁ Δ′)(ρ : Env ∞ Δ′ Δ)(σ : Sub Δ Γ) →
            ELR ρ ρ → VLR a u u →
            ELR (renenv η (evalS σ ρ)) (evalS (wks σ) (renenv η ρ , u))
evalSwks' u η ρ ε p q = _
evalSwks' u η ρ (σ , t) p q =  evalSwks' u η ρ σ p q , transVLR _ (substVLR-l _ (id-ext t (substELR-r (substELR-r (renELR η p) (≈symEnv (lookupRrenId (renenv η ρ)))) (lookupRwkr u renId (renenv η ρ)))) (reneval t ρ η)) (symVLR _ (reneval' t (wkr renId) (renenv η ρ , u) (renELR η p , q)))   

-- evaluating the identity sub
evalSsubId : ∀{Γ Δ}(ρ : Env ∞ Γ Δ) → ELR ρ ρ → ELR ρ (evalS subId ρ)
evalSsubId ε       _       = _
evalSsubId (ρ , v) (p , q) =
  transELR (evalSsubId ρ p) (evalSwks v ρ subId p q) , q

-- lookup and then eval is the same as eval and then lookup
substitution-var : ∀{Γ Δ Δ′ a} (x : Var Γ a) (σ : Sub Δ Γ) (ρ : Env ∞ Δ′ Δ) →
  ELR ρ ρ → a V∋ (lookup x (evalS σ ρ)) ≃ eval (looks σ x) ρ
substitution-var zero    (σ , t) ρ p = id-ext t p
substitution-var (suc x) (σ , t) ρ p = substitution-var x σ ρ p


-- substitution lemma

-- the reflexive equation for ρ could be reduced to knowing that after
-- infinite delay the reading back the values in ρ will converge, or
-- perhaps the substitution lemma should take two different related
-- environments.
substitution : ∀{Γ Δ Δ′ a} (t : Tm Γ a) (σ : Sub Δ Γ) (ρ : Env ∞ Δ′ Δ) →
  ELR ρ ρ →  a V∋ (eval t (evalS σ ρ)) ≃ eval (sub σ t) ρ
substitution (var x) σ ρ p = substitution-var x σ ρ p
substitution (abs t) σ ρ p η u u' u≃u' = laterVLR _ (transVLR _ (id-ext t (evalSwks' u' η ρ σ p (reflVLR _ (symVLR _ u≃u')) , u≃u')) (substitution t (lifts σ) (renenv η ρ , u') (renELR η p , reflVLR _ (symVLR _ u≃u'))))
substitution (app t u) σ ρ p = substVLR-r _ (substVLR-l _ (substitution t σ ρ p renId _ _ (substitution u σ ρ p)) (apply-cong (≈symVal (renvalid (eval t (evalS σ ρ)))) (≈reflVal (eval u (evalS σ ρ))))) ((apply-cong (renvalid (eval (sub σ t) ρ))) (≈reflVal (eval (sub σ u) ρ))) 

-- fundamental theorem of logical relations
fund : ∀{Γ Δ a}{t t' : Tm Δ a} → t ≡βη t' → {ρ ρ' : Env ∞ Γ Δ} → ELR ρ ρ' →
       a V∋ eval t ρ ≃ eval t' ρ'
fund (var≡ x) q = id-ext-var x q
fund (abs≡ p) q η u u' u≃u' = laterVLR _ (fund p (renELR η q , u≃u'))
fund (app≡ {t = t}{t'}{u}{u'} p p') q = substVLR-r _ (substVLR-l _ (fund p q renId _ _ (fund p' q)) (apply-cong (≈symVal (renvalid (eval t _))) (≈reflVal (eval u _)))) (apply-cong (renvalid (eval t' _)) (≈reflVal (eval u' _)))
fund (beta≡ {t = t}{u = u}){ρ}{ρ'} q = laterVLR-l _ (transVLR _ (id-ext t {ρ , eval u ρ}{ρ' , eval u ρ'} (q , id-ext u q)) (transVLR _ (id-ext t (evalSsubId ρ' (reflELR (symELR q)) , (id-ext u (reflELR (symELR q))))) (substitution t (subId , u) ρ' (reflELR (symELR q)))))
fund (eta≡ t') {ρ}{ρ'} q η u u' u≃u' = laterVLR-l _ (substVLR-l _ (transVLR _ (reneval' t' (wkr renId) (renenv η ρ , u) ((renELR η (reflELR q)) , (reflVLR _ u≃u')) renId u u' u≃u') (substVLR-l _ (substVLR-l _ (substVLR-l _ (id-ext t' q η u' u' (reflVLR _ (symVLR _ u≃u'))) (apply-cong (≈symVal (reneval t' ρ η)) (≈reflVal u'))) (≈symVal (apply-cong (eval-cong t' (≈transEnv (≈symEnv (lookupRrenId (renenv η ρ))) (lookupRwkr u renId (renenv η ρ)))) (≈reflVal u')))) (apply-cong (renvalid (eval t' (lookupR (wkr renId) (renenv η ρ , u)))) (≈reflVal u')))) (≈symVal (apply-cong (renvalid (eval (ren (wkr renId) t') (renenv η ρ , u))) (≈reflVal u))) )
fund (refl≡ t') q = id-ext t' q
fund (sym≡ p) q = symVLR _ (fund p (symELR q))
fund (trans≡ p p') q = transVLR _ (fund p (reflELR q)) (fund p' q)

-- reify, reflect
mutual
  reify : ∀{Γ} a {v v' : Val ∞ Γ a} →
          a V∋ v ≃ v' → Delay _≡_ ∋ readback v ~ readback v'
  reify ★       p = p
  reify (a ⇒ b) p = ~later (~delay (map~ abs abs (λ _ _ → cong abs) (reify b (p (wkr renId) _ _ (reflect a {var zero}{var zero}(~now now⇓ now⇓ refl))))))

  reflect : ∀{Γ} a {n n' : NeVal ∞ Γ a} →
            Delay _≡_ ∋ nereadback n ~ nereadback n' → a V∋ ne n ≃ ne n'
  reflect ★                    p = map~ ne ne (λ _ _ → cong ne) p
  reflect (a ⇒ b) {n}{n'} p η u u' u≃u' = reflect b (map2~ app (λ _ _ p _ _ q → cong₂ app p q) (λ _ → refl) sym trans
                                               (~trans trans (≈→~ (≈sym (rennereadback η n)))
                                                (~trans trans (map~ (rennen η) (rennen η) (λ _ _ → cong (rennen η)) p) (≈→~ (rennereadback η n'))))
                                               (reify a u≃u'))

-- the identity environment is related to itself
idecomp : ∀ Γ → ELR (ide Γ) (ide Γ)
idecomp ε       = _
idecomp (Γ , a) =
  renELR (wkr renId) (idecomp Γ) , reflect a (~now now⇓ now⇓ refl)

-- completeness theorem
completeness : ∀ Γ a {t t' : Tm Γ a} → t ≡βη t' → Delay _≡_ ∋ nf t ~ nf t'
completeness Γ a p = reify a (fund p (idecomp Γ))
