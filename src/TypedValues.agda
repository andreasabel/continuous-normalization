{-# OPTIONS --copatterns --sized-types #-}

module TypedValues where

open import Library

open import Term
open import Delay
open import Spine

-- Values and environments
mutual
  data Env {i : Size} (Δ : Cxt) : (Γ : Cxt) → Set where
    ε   : Env Δ ε
    _,_ : ∀ {Γ a} (ρ : Env {i = i} Δ Γ) (v : Val {i = i} Δ a) → Env Δ (Γ , a)

  data Val {i : Size} (Δ : Cxt) : (a : Ty) → Set where
    ne  : ∀{j : Size< i}{a c}(x : Var Δ a)(vs : ValSpine {i = j} Δ a c) → 
          Val Δ c
    lam : ∀{Γ a b}(t : Tm (Γ , a) b)(ρ : Env {i = i} Δ Γ) → Val Δ (a ⇒ b)

  ValSpine : {i : Size} (Δ : Cxt) (a c : Ty) → Set
  ValSpine {i = i} Δ = RSpine (Val {i = i} Δ)

lookup : ∀ {i Γ Δ a} → Var Γ a → Env {i = i} Δ Γ → Val {i = i} Δ a
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

mutual
  val≤ : ∀{i Γ Δ} → Γ ≤ Δ → ∀{σ} → Val {i} Δ σ → Val {i} Γ σ
  val≤ α (ne  x vs) = ne  (var≤ α x) (valSpine≤ α vs)
  val≤ α (lam t ρ)  = lam t (env≤ α ρ)

  env≤ : ∀{i Γ Δ E} →  Δ ≤ Γ → Env {i} Γ E → Env {i} Δ E
  env≤ α ε       = ε
  env≤ α (ρ , v) = env≤ α ρ , val≤ α v

  valSpine≤ : ∀ {i Γ Δ a c} (η : Γ ≤ Δ) (ts : ValSpine {i} Δ a c) → 
             ValSpine {i} Γ a c
  valSpine≤ η ts = mapRSp (val≤ η) ts


-- Weakening.
weakVal : ∀ {i Δ a c} → Val {i} Δ c → Val {i} (Δ , a) c
weakVal = val≤ (weak id)

-- Lifting.
var0 : ∀ {Δ a} → Val (Δ , a) a
var0 = ne zero ε

liftEnv : ∀ {Γ Δ a} → Env Δ Γ → Env (Δ , a) (Γ , a)
liftEnv ρ = env≤ (weak id) ρ , var0

-- identity Env
ide : ∀ Γ → Env Γ Γ
ide ε = ε
ide (Γ , a) = liftEnv (ide Γ)

-- Call-by-value evaluation.

mutual
  eval  : ∀{i}{Γ : Cxt} {a : Ty} → Tm Γ a → {Δ : Cxt} → 
           Env Δ Γ → Delay (Val Δ a) i
  eval (var x) ρ = now (lookup x ρ)
  eval (abs t) ρ = now (lam t ρ)
  eval (app t u) ρ = apply* (eval t ρ) (eval u ρ)

  apply* : ∀{i Δ a b} → Delay (Val Δ (a ⇒ b)) i → Delay (Val Δ a) i → 
           Delay (Val Δ b) i
  apply* f⊥ v⊥ = apply =<<2 f⊥ , v⊥

  apply : ∀{i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay (Val Δ b) i
  apply f v = later (∞apply f v)

  ∞apply : ∀{i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → ∞Delay (Val Δ b) i
  force (∞apply (lam t ρ) v) = eval t (ρ , v)
  force (∞apply (ne x sp) v) = now (ne x (sp , v))

β-expand : ∀{Γ Δ a b}{t : Tm (Γ , a) b}{ρ : Env Δ Γ}{u : Val Δ a}{v : Val Δ b}
           (h : eval t (ρ , u) ⇓ v) → apply (lam t ρ) u ⇓ v
β-expand h = later⇓ h


-- beta quote
mutual
  β-readback : ∀{i Γ a} → Val Γ a → Delay (βNf Γ a) i
  β-readback v = later (∞β-readback v)

  ∞β-readback : ∀{i Γ a} → Val Γ a → ∞Delay (βNf Γ a) i
  force (∞β-readback (lam t ρ)) = lam  <$> (β-readback =<< eval t  (liftEnv ρ))
  force (∞β-readback (ne x rs)) = ne x <$> mapRSpM β-readback rs


-- beta-eta quote
mutual
  readback : ∀{i Γ a} → Val Γ a → Delay (Nf Γ a) i
  readback v = later (∞readback v)

  ∞readback : ∀{i Γ a} → Val Γ a → ∞Delay (Nf Γ a) i
  force (∞readback {a = ★}    (ne x vs)) = ne x <$> mapRSpM readback vs
  force (∞readback {a = a ⇒ b} v) = 
    lam <$> (readback {a = b} =<< apply (weakVal v) (ne zero ε))

-- should this be a lemma, or perhaps built into V⟦⟧?
readback≤ : ∀{Γ Δ}(α : Δ ≤ Γ){a}(v : Val Γ a) → readback v ⇓ → 
            readback (val≤ α v) ⇓
readback≤ α {a = ★}     v (n , p) = (nf≤ α n) , {!!}
readback≤ α {a = a ⇒ b} v (n , p) = {!p!}

-- Type interpretation
mutual
  V⟦_⟧_ : ∀{Γ}(a : Ty) → Val Γ a → Set
  V⟦ ★     ⟧ v = readback v ⇓
  V⟦_⟧_ {Γ = Γ} (a ⇒ b) f = ∀{Δ}(ρ : Δ ≤ Γ)(u : Val Δ a) 
    (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (apply (val≤ ρ f) u)

  C⟦_⟧_ : ∀{Γ}(a : Ty) → Delay (Val Γ a) ∞ → Set
  C⟦ a ⟧ x = ∃ λ v → x ⇓ v × V⟦ a ⟧ v

mutual
  env≤-id : ∀ {i Γ Δ} (ρ : Env {i} Δ Γ) → env≤ id ρ ≡ ρ
  env≤-id ε         = refl
  env≤-id (ρ , v)   = cong₂ _,_ (env≤-id ρ) (val≤-id v)

  val≤-id : ∀ {i Δ a} (v : Val {i} Δ a) → val≤ id v ≡ v
  val≤-id (ne x vs) = cong₂ ne refl (valSpine≤-id vs)
  val≤-id (lam t ρ) = cong (lam t) (env≤-id ρ)

  valSpine≤-id : ∀ {i Δ a c} (vs : ValSpine {i} Δ a c) → valSpine≤ id vs ≡ vs
  valSpine≤-id = mapRSp-id val≤-id

mutual
  env≤-• : ∀ {i Γ Δ₁ Δ₂ Δ₃} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (ρ : Env {i} Δ₃ Γ) →
           env≤ η (env≤ η' ρ) ≡ env≤ (η • η') ρ
  env≤-• η η' ε       = refl
  env≤-• η η' (ρ , v) = cong₂ _,_ (env≤-• η η' ρ) (val≤-• η η' v)

  val≤-• : ∀ {i Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (v : Val {i} Δ₃ a) →
           val≤ η (val≤ η' v) ≡ val≤ (η • η') v
  val≤-• η η' (ne x vs) = cong₂ ne (var≤-• η η' x) (valSpine≤-• η η' vs)
  val≤-• η η' (lam t ρ) = cong (lam t) (env≤-• η η' ρ)

  valSpine≤-• : ∀{i Δ₁ Δ₂ Δ₃ a c}(η : Δ₁ ≤ Δ₂)(η' : Δ₂ ≤ Δ₃)
                (vs : ValSpine {i} Δ₃ a c) →
                valSpine≤ η (valSpine≤ η' vs) ≡ valSpine≤ (η • η') vs
  valSpine≤-• η η' = mapRSp-∘ (val≤-• η η')

V≤ : ∀{Δ Δ′ a}(η : Δ′ ≤ Δ)(v : Val Δ a)(〖v〗 : V⟦ a ⟧ v) → V⟦ a ⟧ (val≤ η v)
V≤ {a = ★}     η v p  = readback≤ η v p
V≤ {a = a ⇒ b} η v p {Δ'} ρ u u⇓ = 
  let v' , p' , p'' = p (ρ • η) u u⇓ in 
      v' , subst (λ X → apply X u ⇓ fst (p (ρ • η) u u⇓)) 
                 ((sym (val≤-• ρ η v))) 
                 p' 
         , p''

⟪_⟫_ : ∀{Δ}(Γ : Cxt) → Env Δ Γ → Set
⟪ ε ⟫     ε       = ⊤
⟪ Γ , a ⟫ (ρ , v) = ⟪ Γ ⟫ ρ × V⟦ a ⟧ v


⟪⟫≤ : ∀ {Γ Δ Δ′} (η : Δ′ ≤ Δ) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → ⟪ Γ ⟫ (env≤ η ρ)
⟪⟫≤ η ε       θ        = _
⟪⟫≤ η (ρ , v) (θ , 〖v〗) = ⟪⟫≤ η ρ θ , V≤ η v 〖v〗


-- Type soundness
⟦var⟧ : ∀{Δ Γ a}(x : Var Γ a)(ρ : Env Δ Γ)(θ : ⟪ Γ ⟫ ρ) → 
            C⟦ a ⟧ (now (lookup x ρ))
⟦var⟧ zero   (_ , v) (_ , v⇓) = v , now⇓ , v⇓
⟦var⟧(suc x) (ρ , _) (θ , _ ) = ⟦var⟧ x ρ θ

sound-β : ∀ {Δ Γ a b} {t : Tm (Γ , a) b} {ρ : Env Δ Γ} {u : Val Δ a} →
          C⟦ b ⟧ (eval t  (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)
sound-β (v , v⇓ , ⟦v⟧) = v , β-expand v⇓ , ⟦v⟧


⟦abs⟧ : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) →
  (∀{Δ'}(α : Δ' ≤ Δ){u : Val Δ' a}(u⇓ : V⟦ a ⟧ u) → 
    C⟦ b ⟧ (eval t  (env≤ α ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))
⟦abs⟧ t ρ θ ih = (lam t ρ) , now⇓ , (λ α u p → 
  sound-β {t = t} {ρ = env≤ α ρ} {u = u} (ih α p))

sound-app' : ∀ {Δ a b} (f : Val Δ (a ⇒ b)) →
  {u* : Delay (Val Δ a) _} {u : Val Δ a} (u⇓ : u* ⇓ u) →
  {v : Val Δ b} →  later (∞apply f u) ⇓ v → (u* >>= λ u → apply f u) ⇓ v
sound-app' f (later⇓ u⇓) h = later⇓ (sound-app' f u⇓ h)
sound-app' f  now⇓       h = h

sound-app : ∀ {Δ a b} →
  {f* : Delay (Val Δ (a ⇒ b)) _} {f : Val Δ (a ⇒ b)} (f⇓ : f* ⇓ f) →
  {u* : Delay (Val Δ a)       _} {u : Val Δ a}       (u⇓ : u* ⇓ u) →
  {v : Val Δ b} →  later (∞apply f u) ⇓ v → apply* f* u* ⇓ v
sound-app  (later⇓ f⇓) u⇓ h = later⇓ (sound-app f⇓ u⇓ h)
sound-app {f = f} now⇓ u⇓ h = sound-app' f u⇓ h

⟦app⟧ : ∀ {Δ a b} {f : Delay (Val Δ (a ⇒ b)) _} {u : Delay (Val Δ a) _} →
          C⟦ a ⇒ b ⟧ f → C⟦ a ⟧ u → C⟦ b ⟧ (apply* f u)
⟦app⟧ (f , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) = 
  let v , v⇓ , ⟦v⟧ = ⟦f⟧ id u ⟦u⟧ in
  v , 
  sound-app f⇓ u⇓ (subst (λ X → apply X u ⇓ fst (⟦f⟧ id u ⟦u⟧)) 
                         (val≤-id f) 
                         v⇓) ,
  ⟦v⟧

-- termination of eval
term : ∀ {Δ Γ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (eval t ρ)
term (var x)   ρ θ = ⟦var⟧ x ρ θ
term (abs t)   ρ θ = ⟦abs⟧ t ρ θ λ α {u} u⇓ → term t (env≤ α ρ , u) 
                                                     (⟪⟫≤ α ρ θ , u⇓)
term (app t u) ρ θ = ⟦app⟧ (term t ρ θ) (term u ρ θ)

--termination of readback
{-
β-rterm : ∀{Γ a}(v : Val Γ a) →   V⟦ a ⟧ v → β-readback v ⇓
β-rterm {a = ★}     v q = q
β-rterm {Γ}{a = a ⇒ b} v q = {!β-readback v !}
-}

{-
-- I'm expecting these two lemmas which are like reify and reflect here
mutual
  rterm : ∀{Γ a}(v : Val Γ a) →   V⟦ a ⟧ v → readback v ⇓
  rterm {a = ★}     v q = q
  rterm {Γ}{a = a ⇒ b} v q = {!lam (fst y)!} , {! {- uses snd y -}!}
    where
    x = q {{!Val.ne (zero {Γ}{a}) ε!}} {! call to rterm'!} 
        -- need Kripke V⟦⟧ here
    y = rterm (fst x) (snd (snd x))
    
  rterm' : ∀{Γ a}(x : Var Γ a) (vs : RSpine (Val Γ) a ★) → 
           readback (ne x vs) ⇓ → V⟦ ★ ⟧ (ne x vs)
  rterm' x vs = {!!}
-}