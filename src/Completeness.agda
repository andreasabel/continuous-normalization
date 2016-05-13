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


{- old
  -- Value computations v? and w? are related at type a.

  _C∋_≃_ : ∀{Γ}(a : Ty) (v? w? : Delay ∞ (Val Γ a)) → Set
  a C∋ v? ≃ w? = ? -- Delay (VLR a) ∋ v? ≃ w?



record Delay_∋_≃_ {A} (R : A → A → Set) (a? b? : Delay ∞ A) : Set where
  constructor delay≃
  field
    a   : A
    a⇓  : a? ⇓ a
    b   : A
    b⇓  : b? ⇓ b
    rab : R a b

-- Symmetry

D≃sym : ∀ {A R} {a? b? : Delay ∞ A}
     → (sym : ∀ {a b} → R a b → R b a)
     → (r : Delay R ∋ a? ≃ b?) → Delay R ∋ b? ≃ a?
D≃sym sym (delay≃ a a⇓ b b⇓ rab) = delay≃ b b⇓ a a⇓ (sym rab)

D≃trans : ∀ {A R} {a? b? c? : Delay ∞ A}
     → (trans : ∀ {a b c} → R a b → R b c → R a c)
     → (r : Delay R ∋ a? ≃ b?) (s : Delay R ∋ b? ≃ c?) → Delay R ∋ a? ≃ c?
D≃trans trans (delay≃ a a⇓ b b⇓ rab) (delay≃ b′ b⇓′ c c⇓ rbc) with uniq⇓ b⇓ b⇓′
D≃trans trans (delay≃ a a⇓ b b⇓ rab) (delay≃ .b b⇓′ c c⇓ rbc) | refl = delay≃ a a⇓ c c⇓ (trans rab rbc)

D≃bind⇓ : ∀{A B}{R : B → B → Set} {a : A} {a? : Delay ∞ A}  {b? : Delay ∞ B}
  → (f : A → Delay ∞ B)
  → (a⇓ : a? ⇓ a)
  → (r  : Delay R ∋ f a ≃ b?)
  → Delay R ∋ (a? >>= f) ≃ b?
D≃bind⇓ f a⇓ (delay≃ fa fa⇓ b b⇓ rab) =  delay≃ fa (bind⇓ f a⇓ fa⇓) b b⇓ rab

D≃now : ∀{A}{R : A → A → Set} {a : A} {a? b? : Delay ∞ A}
  → (a⇓ : a? ⇓ a)
  → (r  : Delay R ∋ a? ≃ b?)
  → Delay R ∋ now a ≃ b?
D≃now a⇓ (delay≃ a′ a′⇓ b b⇓ rab) with uniq⇓ a⇓ a′⇓
D≃now a⇓ (delay≃ a a′⇓ b b⇓ rab) | refl = delay≃ a now⇓ b b⇓ rab
-- delay≃ fa (bind⇓ f a⇓ fa⇓) b b⇓ rab

-- D≃bind-cong : ∀{Γ a} {v? v?' : Delay ∞ (Val Γ a}
--   → (v≃v' : a C∋ v? ≅ v'?)
--   → (∀ (v : Val Δ a

-- _≃_ : ∀{Γ} (v v' : Val Γ ★) → Set
-- ne v ≃ ne v' = ∃ λ n → nereadback v ⇓ n × nereadback v' ⇓ n

record _≃_ {Γ a} (n n' : NeVal Γ a) : Set where
  constructor ne≃
  field
    read : Ne Γ a
    fst⇓ : nereadback n  ⇓ read
    snd⇓ : nereadback n' ⇓ read

≃sym : ∀ {Γ a} {n n' : NeVal Γ a} (r : n ≃ n') → n' ≃ n
≃sym (ne≃ n fst⇓ snd⇓) = ne≃ n snd⇓ fst⇓

≃trans : ∀ {Γ a} {n m l : NeVal Γ a} (r : n ≃ m) (s : m ≃ l) → n ≃ l
≃trans (ne≃ z n⇓ m⇓) (ne≃ z′ m⇓′ l⇓) with uniq⇓ m⇓ m⇓′
≃trans (ne≃ z n⇓ m⇓) (ne≃ .z m⇓′ l⇓) | refl = ne≃ z n⇓ l⇓

ren≃ : ∀ {Γ Δ a} (η : Ren Δ Γ) {v v' : NeVal Γ a} (r : v ≃ v') → rennev η v ≃ rennev η v'
ren≃ η {v} {v'} (ne≃ n v⇓n v'⇓n) =
  ne≃ (rennen η n) (rennereadback⇓ η v v⇓n) (rennereadback⇓ η v' v'⇓n)

mutual

  -- Values v and v' are related at type a.

  _V∋_≃_ : ∀{Γ}(a : Ty) (v v' : Val Γ a) → Set
  _V∋_≃_         ★       (ne n) (ne n') = n ≃ n'
  _V∋_≃_ {Γ = Γ} (a ⇒ b) f     f'       = ∀{Δ}(η : Ren Δ Γ)(u u' : Val Δ a)
    (u≃u' : a V∋ u ≃ u') → b C∋ (apply (renval η f) u) ≃ (apply (renval η f') u')

  VLR : ∀{Γ}(a : Ty) (v v' : Val Γ a) → Set
  VLR a v v' = _V∋_≃_ a v v'

  -- Value computations v? and w? are related at type a.

  _C∋_≃_ : ∀{Γ}(a : Ty) (v? w? : Delay ∞ (Val Γ a)) → Set
  a C∋ v? ≃ w? = Delay (VLR a) ∋ v? ≃ w?

mutual

  V∋≃sym : ∀{Γ a} {v v' : Val Γ a} →
             a V∋ v ≃ v' → a V∋ v' ≃ v
  V∋≃sym {a = ★}       {ne _}{ne _} p          = ≃sym p
  V∋≃sym {a = a ⇒ b}              p ρ u u' q =
    C∋≃sym (p ρ u' u (V∋≃sym q))

  C∋≃sym : ∀{Γ a} {v v' : Delay ∞ (Val Γ a)} →
             a C∋ v ≃ v' → a C∋ v' ≃ v
  C∋≃sym p = D≃sym V∋≃sym p

mutual

  V∋≃trans : ∀{Γ a} {v v' v'' : Val Γ a} →
             a V∋ v ≃ v' → a V∋ v' ≃ v'' → a V∋ v ≃ v''
  V∋≃trans {a = ★}{ne n}{ne n'}{ne n''} p q = ≃trans p q
  V∋≃trans {a = a ⇒ b} p q ρ u u' r         = C∋≃trans
    (p ρ u u (V∋≃trans r (V∋≃sym r)))
    (q ρ u u' r)

  C∋≃trans : ∀{Γ a} {v v' v'' : Delay ∞ (Val Γ a)} →
             a C∋ v ≃ v' → a C∋ v' ≃ v'' → a C∋ v ≃ v''
  C∋≃trans p q = D≃trans V∋≃trans p q

V∋≃refl : ∀{Γ a} {v v' : Val Γ a} →
           a V∋ v ≃ v' → a V∋ v ≃ v
V∋≃refl p = V∋≃trans p (V∋≃sym p)

C∋≃refl : ∀{Γ a} {v v' : Delay ∞ (Val Γ a)} →
           a C∋ v ≃ v' → a C∋ v ≃ v
C∋≃refl (delay≃ v v⇓ v' v'⇓ r) = delay≃ v v⇓ v v⇓ (V∋≃refl r)

-- Strongly bisimilar values can be swapped out.

V∋≃bisim-l : ∀{Γ a} {v₀? v₁? v₂? : Delay ∞ (Val Γ a)}
  → (p : v₀? ≈ v₁?)
  → (q : a C∋ v₁? ≃ v₂?)
  → a C∋ v₀? ≃ v₂?
C∋≃bisim-l p (delay≃ v₁ v₁⇓ v₂ v₂⇓ r) = delay≃ v₁ (subst≈⇓ v₁⇓ (≈sym p)) v₂ v₂⇓ r

C∋≃bisim-r : ∀{Γ a} {v₀? v₁? v₂? : Delay ∞ (Val Γ a)}
  → (p : a C∋ v₀? ≃ v₁?)
  → (q : v₁? ≈ v₂?)
  → a C∋ v₀? ≃ v₂?
C∋≃bisim-r (delay≃ v₀ v₀⇓ v₁ v₁⇓ r) q = delay≃ v₀ v₀⇓ v₁ (subst≈⇓ v₁⇓ q) r

C∋≃converg-l : ∀{Γ a} {v₀? v₁? v₂? : Delay ∞ (Val Γ a)} → 
  (p : a C∋ v₀? ≃ v₁?) →
  v₂? ⇓ Delay_∋_≃_.a p → a C∋ v₂? ≃ v₁?
C∋≃converg-l (delay≃ a₁ a⇓ b b⇓ rab) q = delay≃ _ q b b⇓ rab

C∋≃converg-r : ∀{Γ a} {v₀? v₁? v₂? : Delay ∞ (Val Γ a)} → 
  (p : a C∋ v₀? ≃ v₁?) →
  v₂? ⇓ Delay_∋_≃_.b p → a C∋ v₀? ≃ v₂?
C∋≃converg-r (delay≃ a₁ a⇓ b b⇓ rab) q = delay≃ a₁ a⇓ _ q rab
-}
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

{- old

-- Extensional equality of typed terms (evaluate to bisimilar values).

_≃T_ : ∀{Γ a} (t t' : Tm Γ a) → Set
_≃T_ {Γ} {a} t t' =
  ∀ {Δ} {ρ ρ' : Env Δ Γ} (ρ≃ρ' : ρ ≃E ρ')
  → a C∋ (eval t ρ) ≃ (eval t' ρ')


-- Variables are related.


⟦var⟧ : ∀{Γ a} (x : Var Γ a) → var x ≃T var x
⟦var⟧ zero    {Δ} {ρ , v} {ρ' , v'} (ρ≃ρ' , v≃v') =
  delay≃ v now⇓ v' now⇓ v≃v'
⟦var⟧ (suc x) {Δ} {ρ , v} {ρ' , v'} (ρ≃ρ' , v≃v') = ⟦var⟧ x ρ≃ρ'


beta-later-l :  ∀ {Δ Γ a b} (t : Tm (Γ , a) b)
       {ρ : Env Δ Γ} {u : Val Δ a} {v? : Delay ∞ (Val Δ b)} →
       (r : Delay (b V∋_≃_) ∋ later (beta t ρ u) ≃ v?) →
       Delay (b V∋_≃_) ∋ eval t (ρ , u) ≃ v?
beta-later-l t (delay≃ w (later⇓ tρu⇓) v v⇓ rab) = delay≃ w tρu⇓ v v⇓ rab

later-beta-l :  ∀ {Δ Γ a b} (t : Tm (Γ , a) b)
       {ρ : Env Δ Γ} {u : Val Δ a} {v? : Delay ∞ (Val Δ b)} →
       (r : Delay (b V∋_≃_) ∋ eval t (ρ , u) ≃ v?) →
       Delay (b V∋_≃_) ∋ later (beta t ρ u) ≃ v?
later-beta-l t (delay≃ a a⇓ b b⇓ rab) = delay≃ a (later⇓ a⇓) b b⇓ rab

-- something more generic might be useful...
later-beta : ∀ {Δ Γ a b} {t t' : Tm (Γ , a) b}
       {ρ ρ' : Env Δ Γ} {u u' : Val Δ a} →
       (Delay (b V∋_≃_) ∋ eval t (ρ , u) ≃ eval t' (ρ' , u')) →
       (Delay (b V∋_≃_) ∋ later (beta t ρ u) ≃ later (beta t' ρ' u'))
later-beta (delay≃ a a⇓ b b⇓ rab) = delay≃ a (later⇓ a⇓) b (later⇓ b⇓) rab

≃later : ∀{A}{R : A → A → Set}{a∞ b∞ : ∞Delay ∞ A}
  → Delay R ∋ force a∞ ≃ force b∞
  → Delay R ∋ later a∞ ≃ later b∞
≃later (delay≃ a a⇓ b b⇓ rab) = delay≃ a (later⇓ a⇓) b (later⇓ b⇓) rab

⟦abs⟧ : ∀ {Δ Γ a b} (t t' : Tm (Γ , a) b) -- (t≡t' : t ≡βη t')
  {ρ ρ' : Env Δ Γ} (ρ≃ρ' : ρ ≃E ρ') →
  (∀{Δ′}(η : Ren Δ′ Δ){u u' : Val Δ′ a}(u≃u' : VLR a u u')
   → b C∋ (eval t (renenv η ρ , u)) ≃ (eval t' (renenv η ρ' , u'))) →
  (a ⇒ b) C∋ (now (lam t ρ)) ≃ (now (lam t' ρ'))
⟦abs⟧ t t' {ρ}{ρ'} ρ≃ρ' ih =
  delay≃ (lam t ρ) now⇓ (lam t' ρ') now⇓ (λ η u u' u≃u' → later-beta (ih η u≃u'))

{-
⟦abs⟧' : ∀ {Γ a b} {t t' : Tm (Γ , a) b} → t ≃T t' → abs t ≃T abs t'
⟦abs⟧' {t = t}{t'} t≃t' ρ≃ρ' = ⟦abs⟧ t t' ρ≃ρ' (λ η u≃u' → t≃t' (renE≃ η ρ≃ρ' , u≃u'))

⟦app⟧'' : ∀{Γ a b}{f f' : Val Γ (a ⇒ b)}{v v' : Val Γ a} →
       (a ⇒ b) V∋ f ≃ f' → a V∋ v ≃ v' → b C∋ apply f v ≃ apply f' v'
⟦app⟧'' {Γ}{a}{b}{f}{f'}{v}{v'} p q =
  subst (λ X → b C∋ apply f v ≃ apply X v')
        (renvalid f')
        (subst (λ X → b C∋ apply X v ≃ apply (renval renId f') v')
               (renvalid f)
               (p renId _ _ q))

mutual
  ⟦app⟧' : ∀{Γ a b}{f f' : Val Γ (a ⇒ b)}{v v' : Delay ∞ (Val Γ a)} →
          (a ⇒ b) V∋ f ≃ f' → a C∋ v ≃ v' →
          b C∋ v >>= apply f ≃ (v' >>= apply f')
  ⟦app⟧' p (≃now a⇓ b⇓ aRb) =
    ≃trans (V∋≃trans _)
           (bindlem (C∋≃refl _ (⟦app⟧'' p aRb)) a⇓) (≃trans (V∋≃trans _) (⟦app⟧'' p aRb) (≃sym (V∋≃sym _) (bindlem (C∋≃refl _ (≃sym (V∋≃sym _) (⟦app⟧'' p aRb))) b⇓)))
  ⟦app⟧' p (≃later ∞p) = ≃later (∞⟦app⟧' p ∞p)

  ∞⟦app⟧' : ∀{Γ a b}{f f' : Val Γ (a ⇒ b)}{v v' : ∞Delay ∞ (Val Γ a)} →
       (a ⇒ b) V∋ f ≃ f' → ∞Delay VLR a ∋ v ≃ v' →
       ∞Delay VLR b ∋ v ∞>>= apply f ≃ (v' ∞>>= apply f')
  ≃force (∞⟦app⟧' f p) = ⟦app⟧' f (≃force p)

mutual
  ⟦app⟧ : ∀{Γ a b}{f f' : Delay ∞ (Val Γ (a ⇒ b))}{v v' : Delay ∞ (Val Γ a)} →
          (a ⇒ b) C∋ f ≃ f' → a C∋ v ≃ v' →
          b C∋ (f >>= λ f → v >>= apply f) ≃ (f' >>= λ f' → v' >>= apply f')
  ⟦app⟧ (≃now a⇓ b⇓ aRb) q = ≃trans (V∋≃trans _) (bindlem (C∋≃refl _ (⟦app⟧' aRb q)) a⇓) (≃trans (V∋≃trans _) (⟦app⟧' aRb q) (≃sym (V∋≃sym _) (bindlem (C∋≃refl _ (≃sym (V∋≃sym _) (⟦app⟧' aRb q))) b⇓) ))
  ⟦app⟧ (≃later ∞p) q = ≃later (∞⟦app⟧ ∞p q)

  ∞⟦app⟧ : ∀{Γ a b}{f f' : ∞Delay ∞ (Val Γ (a ⇒ b))}{v v' : Delay ∞ (Val Γ a)} →
          ∞Delay VLR (a ⇒ b) ∋ f ≃ f' → Delay VLR a ∋ v ≃ v' →
          ∞Delay VLR b ∋ (f ∞>>= λ f → v >>= apply f) ≃ (f' ∞>>= λ f' → v' >>= apply f')
  ≃force (∞⟦app⟧ p q) = ⟦app⟧ (≃force p) q

-- did Andreas say not to do it this way?
-}

⟦app⟧ : ∀{Γ a b}{f f' : Delay ∞ (Val Γ (a ⇒ b))}{v v' : Delay ∞ (Val Γ a)} →
        (a ⇒ b) C∋ f ≃ f' → a C∋ v ≃ v' →
        b C∋ (f >>= λ f → v >>= apply f) ≃ (f' >>= λ f' → v' >>= apply f')
⟦app⟧ {v = u}{v' = u'} (delay≃ f f⇓ f' f'⇓ rff') (delay≃ v v⇓ v' v'⇓ rvv') =
  let delay≃ x x⇓ x' x'⇓ rxx' = rff' renId v v' rvv'
  in  delay≃ x
             (bind⇓ (λ f -> u >>= apply f) f⇓ (bind⇓ (apply f) v⇓ (subst (λ X -> apply X v ⇓ x) (renvalid f) x⇓)))
             x'
             (bind⇓ (λ f' -> u' >>= apply f') f'⇓ (bind⇓ (apply f') v'⇓ (subst (λ X -> apply X v' ⇓ x') (renvalid f') x'⇓)))
             rxx'

idext : ∀{Γ a}(t : Tm Γ a) → t ≃T t
idext (var x)   p = ⟦var⟧ x p
idext (abs t)   p = ⟦abs⟧ _ _ p (λ η q → idext t (renE≃ η p , q))
idext (app t u) p = ⟦app⟧ (idext t p) (idext u p)

evalR : ∀{Γ Δ Δ'} (η : Ren Δ Γ) (ρ : Env Δ' Δ) → Env Δ' Γ
evalR ε       ρ = ε
evalR (η , x) ρ = evalR η ρ , lookup x ρ

ren-evalR : ∀{Γ Δ Δ' Δ''} (η : Ren Δ Γ) (ρ : Env Δ' Δ) (η' : Ren Δ'' Δ') →
  renenv η' (evalR η ρ) ≡ evalR η (renenv η' ρ)
ren-evalR ε ρ η' = refl
ren-evalR (η , x) ρ η' rewrite ren-evalR η ρ η' | lookup≤ x ρ η' = refl
-- {-# REWRITE ren-evalR #-} -- does not fire

ren-evalS' : ∀{Γ Δ Δ' Δ''} (η : Sub Δ Γ) (ρ : Env Δ' Δ) (η' : Ren Δ'' Δ'){ρ' : DEnv Δ'' Γ} →
  rendenv η' (evalS₀ η ρ) ≃D ρ' →
  evalS₀ η (renenv η' ρ) ≃D ρ'
ren-evalS' ε ρ η' p = p
ren-evalS' (η , t) ρ η' {ρ' , v} (p , p') = (ren-evalS' η ρ η' p) , C∋≃bisim-l (≈sym (reneval t ρ η' )) p'

evalR-wkr : ∀{Γ Δ Δ' a} (η : Ren Δ Γ) (ρ : Env Δ' Δ) (v : Val Δ' a) →
  evalR (wkr η) (ρ , v) ≡ evalR η ρ
evalR-wkr ε _ _ = refl
evalR-wkr (η , x) ρ v rewrite evalR-wkr η ρ v = refl
-- {-# REWRITE evalR-wkr #-}

evalR-id : ∀{Γ Δ} (ρ : Env Δ Γ) →
  evalR renId ρ ≡ ρ
evalR-id ε       = refl
evalR-id (ρ , v) = cong (_, v) (trans (evalR-wkr renId ρ v) (evalR-id ρ))

lookup-ren :  ∀{Γ Δ Δ' a} (x : Var Γ a) (η : Ren Δ Γ) (ρ : Env Δ' Δ)
  → lookup (lookr η x) ρ ≡ lookup x (evalR η ρ)
lookup-ren zero (η , x) ρ = refl
lookup-ren (suc x) (η , ()) ε
lookup-ren (suc x) (η , _) ρ = lookup-ren x η ρ

≃lookup :  ∀{Γ Δ a} (x : Var Γ a) {ρ ρ' : Env Δ Γ}
  → (ρ≃ρ' : ρ ≃E ρ')
  → a V∋ lookup x ρ ≃ lookup x ρ'
≃lookup zero    {ρ , v} {ρ' , v'} (ρ≃ρ' , v≃v') = v≃v'
≃lookup (suc x) {ρ , v} {ρ' , v'} (ρ≃ρ' , v≃v') = ≃lookup x ρ≃ρ'

≃evalR : ∀{Γ Δ Δ'} (η : Ren Δ Γ) {ρ ρ' : Env Δ' Δ}
  → (ρ≃ρ' : ρ ≃E ρ')
  → evalR η ρ ≃E evalR η ρ'
≃evalR ε ρ≃ρ' = _
≃evalR (η , x) ρ≃ρ' = ≃evalR η ρ≃ρ' , ≃lookup x ρ≃ρ'

fundr : ∀{Γ Δ Δ' a} (t : Tm Γ a) (η : Ren Δ Γ) {ρ ρ' : Env Δ' Δ}
  → (ρ≃ρ' : ρ ≃E ρ')
  → a C∋ eval (ren η t) ρ ≃ eval t (evalR η ρ')
fundr (var x) η {ρ} ρ≃ρ' rewrite lookup-ren x η ρ = ⟦var⟧ x (≃evalR η ρ≃ρ')
fundr (abs t) η {ρ} {ρ'} ρ≃ρ' = delay≃ _ now⇓ _ now⇓ (λ η' u u' u≃u' →
  ≃later
  (subst (λ z → _ C∋ eval (ren (liftr η) t) (renenv η' ρ , u) ≃ eval t (z , u')) (sym (ren-evalR _ _ η'))
  (subst (λ z → _ C∋ eval (ren (liftr η) t) (renenv η' ρ , u) ≃ eval t (z , u')) (evalR-wkr η _ u')
  (fundr t (liftr η) {renenv η' ρ , u} {renenv η' ρ' , u'} (renE≃ η' ρ≃ρ' , u≃u')))))
fundr (app t u) η ρ≃ρ' = ⟦app⟧ (fundr t η ρ≃ρ') (fundr u η ρ≃ρ')

evalS-wks :
  ∀{Γ a Δ₁ Δ} {σ : Sub Δ₁ Γ} {ρ : Env Δ Δ₁} (ρ≃ρ : ρ ≃E ρ)
  → {v : Val Δ a} (v≃v : a V∋ v ≃ v) {ρ' : DEnv Δ Γ}
  → (σρ≃σ'ρ' : evalS₀ σ ρ ≃D ρ')
  → evalS₀ (wks σ) (ρ , v) ≃D ρ'
evalS-wks {σ = ε}     ρ≃ρ         v≃v       σρ≃σ'ρ'          = σρ≃σ'ρ'
evalS-wks {σ = σ , t} {ρ} ρ≃ρ {v} v≃v {ρ' = ρ' , v'} (σρ≃σ'ρ' , v≃v') =
  evalS-wks ρ≃ρ v≃v σρ≃σ'ρ' ,
  C∋≃trans (fundr t (wkr renId) {ρ , v} {ρ , v} (ρ≃ρ , v≃v))
  (subst (λ z → _ C∋ eval t z ≃ v') (sym (evalR-wkr renId ρ v))
  (subst (λ z → _ C∋ eval t z ≃ v') (sym (evalR-id ρ))
  v≃v'))

subevalS₀ : ∀{Γ Δ}{ρ ρ' : Env Γ Δ} → ρ ≃E ρ' → evalS₀ subId ρ ≃D evalS₀ subId ρ'
subevalS₀ {ρ = ε}    {ε}       _        = _
subevalS₀ {ρ = ρ , v}{ρ' , v'} (p , p') =
  evalS-wks (≃Erefl p)
            (V∋≃refl p')
            (≃Dsym (evalS-wks (≃Erefl (≃Esym p))
                              (V∋≃refl (V∋≃sym p'))
                              (≃Dsym (subevalS₀ p))))
  ,
  delay≃ _ now⇓ _ now⇓ p'



lemma : ∀{Γ a Δ₁ Δ₂ Δ} {σ : Sub Δ₁ Γ} {σ' : Sub Δ₂ Γ}
  → ∀{ρ : Env Δ Δ₁} (ρ≃ρ : ρ ≃E ρ) {ρ' : Env Δ Δ₂}
  → (σρ≃σ'ρ' : evalS₀ σ ρ ≃D evalS₀ σ' ρ')
  → (u : Tm Γ a) {uσρ : Val Δ a}
  → (u⇓ : eval (sub σ u) ρ ⇓ uσρ)
  → (u≃u : a C∋ eval (sub σ u) ρ  ≃  eval (sub σ' u) ρ')
  → evalS₀ (lifts σ) (ρ , uσρ) ≃D evalS₀ (σ' , sub σ' u) ρ'
lemma ρ≃ρ σρ≃σ'ρ' u u⇓ (delay≃ v uσρ⇓v v' uσ'ρ'⇓v' r) with uniq⇓ u⇓ uσρ⇓v
lemma ρ≃ρ σρ≃σ'ρ' u u⇓ (delay≃ uσρ uσρ⇓v v' uσ'ρ'⇓v' r) | refl =
  evalS-wks ρ≃ρ (V∋≃refl r) σρ≃σ'ρ' ,
  D≃now u⇓ (delay≃ uσρ uσρ⇓v v' uσ'ρ'⇓v' r)

{-
-- Candidate for trash:
lemma' : ∀{Γ a}
  → ∀{Δ₁ Δ₂ Δ} (σ : Sub Δ₁ Γ) (σ' : Sub Δ₂ Γ) (ρ : Env Δ Δ₁) (ρ' : Env Δ Δ₂)
  → (σρ≃σ'ρ' : Delay _≃E_ ∋ evalS σ ρ ≃ evalS σ' ρ')
  → ∀ {u : Tm Γ a} {uσρ : Val Δ a}
  → (u⇓ : eval (sub σ u) ρ ⇓ uσρ)
  → Delay _≃E_ ∋ evalS (lifts σ) (ρ , uσρ) ≃ evalS (σ' , sub σ' u) ρ'
lemma' σ σ' ρ ρ' σρ≃σ'ρ' u⇓ = {!!}
-}
fundvar : ∀{Γ a} (x : Var Γ a)
  → ∀{Δ₁ Δ₂ Δ} (σ : Sub Δ₁ Γ) (σ' : Sub Δ₂ Γ)
  → ∀{ρ : Env Δ Δ₁}{ρ' : Env Δ Δ₂}
  → (σρ≃σ'ρ' : evalS₀ σ ρ ≃D evalS₀ σ' ρ')
  → a C∋ eval (looks σ x) ρ ≃ eval (looks σ' x) ρ'
fundvar zero    (σ , v) (σ' , v') (_    , v≃v') = v≃v'
fundvar (suc x) (σ , v) (σ' , v') (σρ≃σ'ρ' , _) = fundvar x σ σ' σρ≃σ'ρ'

fundt : ∀{Γ a} (t : Tm Γ a)
  → ∀{Δ₁ Δ₂ Δ} (σ : Sub Δ₁ Γ) (σ' : Sub Δ₂ Γ)
  → ∀{ρ : Env Δ Δ₁} (ρ≃ρ : ρ ≃E ρ)
  → ∀{ρ' : Env Δ Δ₂}(ρ'≃ρ' : ρ' ≃E ρ')
  → (σρ≃σ'ρ' : evalS₀ σ ρ ≃D evalS₀ σ' ρ')
  → a C∋ eval (sub σ t) ρ  ≃  eval (sub σ' t) ρ'
fundt (var x) σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' = fundvar x σ σ' σρ≃σ'ρ'
fundt {a = a ⇒ b} (abs t) σ σ' ρ≃ρ ρ'≃ρ' p =
  delay≃ _ now⇓ _ now⇓
    λ η u u' u≃u' → ≃later $
        fundt t (lifts σ)
              (lifts σ')
              (renE≃ η ρ≃ρ , V∋≃refl u≃u' )
              (renE≃ η ρ'≃ρ' , V∋≃refl (V∋≃sym u≃u') )
              (evalS-wks (renE≃ η ρ≃ρ) (V∋≃refl u≃u') (≃Dsym (evalS-wks (renE≃ η ρ'≃ρ') (V∋≃refl (V∋≃sym u≃u')) (ren-evalS' σ' _ η (≃Dsym (ren-evalS' σ _ η (renD≃ η p)))))) , delay≃ _ now⇓ _ now⇓ u≃u')

fundt (app t u) σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' =
  ⟦app⟧ (fundt t σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ')
        (fundt u σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ')


fundeta : ∀ {Γ Δ₁ Δ₂ Δ Δ₃ a b} (t : Tm Γ (a ⇒ b))
  → (σ : Sub Δ₁ Γ) (σ' : Sub Δ₂ Γ)
  → {ρ  : Env Δ Δ₁} (ρ≃ρ   : ρ  ≃E ρ )
  → {ρ' : Env Δ Δ₂} (ρ'≃ρ' : ρ' ≃E ρ')
  → (σρ≃σ'ρ' : evalS₀ σ ρ ≃D evalS₀ σ' ρ')
  → (η : Ren Δ₃ Δ)
  → (t≃t : (a ⇒ b) C∋ eval (sub σ t) ρ ≃ eval (sub σ' t) ρ')
  → {u u' : Val Δ₃ a} (u≃u' : a V∋ u ≃ u')
  → b C∋ eval (sub (lifts σ) (ren (wkr renId) t)) (renenv η ρ , u)
            >>= (λ f → apply f u)
       ≃  apply (renval η (Delay_∋_≃_.b t≃t)) u'
fundeta {a = a} t σ σ' {ρ} ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' η (delay≃ a1 a2 a3 a4 a5) {u} u≃u'
  rewrite liftSubRen {a = a} σ t =
   let delay≃ b1 b2 b3 b4 b5 = fundt t (wks σ) σ {renenv η ρ , u} ((renE≃ η ρ≃ρ) , (V∋≃refl u≃u')) {renenv η ρ} (renE≃ η ρ≃ρ) (evalS-wks (renE≃ η ρ≃ρ) (V∋≃refl u≃u') (≃Drefl (renD≃' η σρ≃σ'ρ')))
       delay≃ c1 c2 c3 c4 c5 = b5 renId u _ (V∋≃refl u≃u')

   in
     C∋≃trans
      (delay≃ c1
              (bind⇓ (λ f → apply f u)
                     b2
                     (subst (λ f → apply f u ⇓ c1) (renvalid b1) c2))
              c3
              (⇓bind (λ f → apply f u)
                 (subst≈⇓ (map⇓ (renval η) a2) (reneval (sub σ t) ρ η)) (bind⇓ (λ f → apply f u) b4 (subst (λ f → apply f u ⇓ c3) (renvalid b3) c4)))
              c5)
      (a5 η _ _ u≃u')


fund' : ∀{Γ a}{t t' : Tm Γ a} (t≡t' : t ≡βη t')
  → ∀{Δ₁ Δ₂ Δ} (σ : Sub Δ₁ Γ) (σ' : Sub Δ₂ Γ)
  → ∀{ρ : Env Δ Δ₁} (ρ≃ρ : ρ ≃E ρ)
  → ∀{ρ' : Env Δ Δ₂}(ρ'≃ρ' : ρ' ≃E ρ')
  → (σρ≃σ'ρ' : evalS₀ σ ρ ≃D evalS₀ σ' ρ')
  → a C∋ eval (sub σ t) ρ  ≃  eval (sub σ' t') ρ'
fund' (var≡ x) σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' = fundvar x σ σ' σρ≃σ'ρ'
fund' (abs≡ t≡t') σ σ' {ρ} ρ≃ρ {ρ'} ρ'≃ρ' σρ≃σ'ρ' = -- the same as abs case of fundt, should make a lemma!
  delay≃ _ now⇓ _ now⇓ (λ η u u' u≃u' → ≃later $ fund' t≡t' (lifts σ) (lifts σ') (renE≃ η ρ≃ρ , V∋≃refl u≃u' ) (renE≃ η ρ'≃ρ' , V∋≃refl (V∋≃sym u≃u') ) ((evalS-wks (renE≃ η ρ≃ρ) (V∋≃refl u≃u') (≃Dsym (evalS-wks (renE≃ η ρ'≃ρ') (V∋≃refl (V∋≃sym u≃u')) (ren-evalS' σ' _ η (≃Dsym (ren-evalS' σ _ η (renD≃ η σρ≃σ'ρ')))))) , delay≃ _ now⇓ _ now⇓ u≃u')))
fund' (app≡ t≡t' u≡u') σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' =
  ⟦app⟧ (fund' t≡t' σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ')
        (fund' u≡u' σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ')
fund' (beta≡ {t = t}{u = u}) σ σ' {ρ} ρ≃ρ ρ'≃ρ' σρ≃σ'ρ'
  rewrite sym (subcomp σ' (subId , u) t) | sidr σ' =
  let u≃u = fundt u σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' in
  let uσρ⇓ = Delay_∋_≃_.a⇓ u≃u in
  D≃bind⇓ (λ v → later (beta (sub (wks σ , var zero) t) ρ v)) uσρ⇓
  (later-beta-l _
   (fundt t (lifts σ) (σ' , sub σ' u) (ρ≃ρ , Delay_∋_≃_.rab (C∋≃refl u≃u)) ρ'≃ρ' (lemma ρ≃ρ σρ≃σ'ρ' u uσρ⇓ u≃u)))
fund' (eta≡ t) σ σ' {ρ} ρ≃ρ {ρ'} ρ'≃ρ' σρ≃σ'ρ' =
  let t≃t = fundt t σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' in
  let delay≃ tσρ tσρ⇓ tσ'ρ' tσ'ρ'⇓ r = t≃t in
  delay≃ _ now⇓ _ tσ'ρ'⇓ (λ η u u' u≃u' → later-beta-l _
   (fundeta t σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' η t≃t u≃u'))
fund' (refl≡ t)   σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' = fundt t σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ'
fund' (sym≡ t'≡t) σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' = C∋≃sym (fund' t'≡t σ' σ ρ'≃ρ' ρ≃ρ (≃Dsym σρ≃σ'ρ'))
fund' (trans≡ t₁≡t₂ t₂≡t₃) σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ' =
  C∋≃trans
    (fund' t₁≡t₂ σ σ  ρ≃ρ ρ≃ρ  (≃Drefl σρ≃σ'ρ'))
    (fund' t₂≡t₃ σ σ' ρ≃ρ ρ'≃ρ' σρ≃σ'ρ')


-- Equal terms evaluate to equal values.
fund : ∀{Γ a}{t t' : Tm Γ a} →
  (t≡t' : t ≡βη t') → t ≃T t'
fund {a = a}{t}{t'} p {Δ}{ρ}{ρ'} q =
  subst
    (λ t' → a C∋ eval t ρ ≃ eval t' ρ')
    (subid t')
    (subst
      (λ t → a C∋ eval t ρ ≃ eval (sub subId t') ρ')
      (subid t)
      (fund' p subId subId (≃Erefl q) (≃Erefl (≃Esym q)) (subevalS₀ q)))
-}
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
