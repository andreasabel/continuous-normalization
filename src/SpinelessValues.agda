{-# OPTIONS --copatterns --sized-types #-}

module SpinelessValues where

open import Library
open import Term hiding (Nf; module Nf; nf≤)
open import Spine
open import Delay

data Ne (T : Cxt → Ty → Set)(Γ : Cxt) : Ty → Set where
  var : ∀{a} → Var Γ a → Ne T Γ a
  app : ∀{a b} → Ne T Γ (a ⇒ b) → T Γ a → Ne T Γ b

data Nf (Γ : Cxt) : Ty → Set where
  lam : ∀{a b}(n : Nf (Γ , a) b) → Nf Γ (a ⇒ b)
  ne  : Ne Nf Γ ★ → Nf Γ ★

mutual
  nf≤ : ∀{Γ Δ} → Γ ≤ Δ → ∀{a} → Nf Δ a → Nf Γ a
  nf≤ α (ne t)   = ne (nen≤ α t)
  nf≤ α (lam t)  = lam (nf≤ (lift α) t)

  nen≤ : ∀{Γ Δ} → Γ ≤ Δ → ∀{a} → Ne Nf Δ a → Ne Nf Γ a
  nen≤ α (var x)   = var (var≤ α x)
  nen≤ α (app t u) = app (nen≤ α t) (nf≤ α u)

mutual


  nen≤-• : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (t : Ne Nf Δ₃ a) →
           nen≤ η (nen≤ η' t) ≡ nen≤ (η • η') t
  nen≤-• = {!!}

-- Values and environments
mutual
  data Env (Δ : Cxt) : (Γ : Cxt) → Set where
    ε   : Env Δ ε
    _,_ : ∀ {Γ a} (ρ : Env Δ Γ) (v : Val Δ a) → Env Δ (Γ , a)

  data Val (Δ : Cxt) : (a : Ty) → Set where
    ne  : ∀{a} → Ne Val Δ a → Val Δ a
    lam : ∀{Γ a b}(t : Tm (Γ , a) b)(ρ : Env Δ Γ) → Val Δ (a ⇒ b)

lookup : ∀ {Γ Δ a} → Var Γ a → Env Δ Γ → Val Δ a
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

mutual
  val≤ : ∀{Γ Δ} → Γ ≤ Δ → ∀{a} → Val Δ a → Val Γ a
  val≤ α (ne t) = ne (nev≤ α t)
  val≤ α (lam t ρ)  = lam t (env≤ α ρ)

  env≤ : ∀{Γ Δ E} →  Δ ≤ Γ → Env Γ E → Env Δ E
  env≤ α ε       = ε
  env≤ α (ρ , v) = env≤ α ρ , val≤ α v

  nev≤ : ∀{Γ Δ} → Γ ≤ Δ → ∀{a} → Ne Val Δ a → Ne Val Γ a
  nev≤ α (var x)   = var (var≤ α x)
  nev≤ α (app t u) = app (nev≤ α t) (val≤ α u)

mutual
  env≤-id : ∀ {Γ Δ} (ρ : Env Δ Γ) → env≤ id ρ ≡ ρ
  env≤-id ε         = refl
  env≤-id (ρ , v)   = cong₂ _,_ (env≤-id ρ) (val≤-id v)

  val≤-id : ∀ {Δ a} (v : Val Δ a) → val≤ id v ≡ v
  val≤-id (ne t) = cong ne (nev≤-id t)
  val≤-id (lam t ρ) = cong (lam t) (env≤-id ρ)

  nev≤-id : ∀ {Δ a} (t : Ne Val Δ a) → nev≤ id t ≡ t
  nev≤-id (var x)   = refl
  nev≤-id (app t u) = cong₂ app (nev≤-id t) (val≤-id u)

mutual
  env≤-• : ∀ {Γ Δ₁ Δ₂ Δ₃} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (ρ : Env Δ₃ Γ) →
           env≤ η (env≤ η' ρ) ≡ env≤ (η • η') ρ
  env≤-• η η' ε       = refl
  env≤-• η η' (ρ , v) = cong₂ _,_ (env≤-• η η' ρ) (val≤-• η η' v)

  val≤-• : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (v : Val Δ₃ a) →
           val≤ η (val≤ η' v) ≡ val≤ (η • η') v
  val≤-• η η' (ne t) = cong ne (nev≤-• η η' t)
  val≤-• η η' (lam t ρ) = cong (lam t) (env≤-• η η' ρ)

  nev≤-• : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (t : Ne Val Δ₃ a) →
           nev≤ η (nev≤ η' t) ≡ nev≤ (η • η') t
  nev≤-• η η' (var x)   = cong var (var≤-• η η' x)
  nev≤-• η η' (app t u) = cong₂ app (nev≤-• η η' t) (val≤-• η η' u)

weakVal : ∀ {Δ a c} → Val Δ c → Val (Δ , a) c
weakVal = val≤ (weak id)

mutual
  eval : ∀{i Γ Δ a} → Tm Γ a → Env Δ Γ → Delay (Val Δ a) i
  eval (var x)   γ = now (lookup x γ)
  eval (abs t)   γ = now (lam t γ)
  eval (app t u) γ = apply* (eval t γ) (eval u γ)

  apply* : ∀{i Γ a b} → 
    Delay (Val Γ (a ⇒ b)) (i) → Delay (Val Γ a) i → Delay (Val Γ b) i
  apply* f v = apply =<<2 f , v

  apply : ∀{i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay (Val Δ b) i
  apply f v = later (∞apply f v)

  ∞apply : ∀{i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → ∞Delay (Val Δ b) i
  force (∞apply (ne x)    v) = now (ne (app x v))
  force (∞apply (lam t ρ) v) = eval t (ρ , v)


mutual
  readback : ∀{i Γ} a → Val Γ a → Delay (Nf Γ a) i
  readback a v = later (∞readback a v)

  ∞readback : ∀{i Γ} a → Val Γ a → ∞Delay (Nf Γ a) i
  force (∞readback ★       (ne t)) = ne <$> nereadback t
  force (∞readback (a ⇒ b) v     ) = 
    lam <$> (readback b =<< apply (weakVal v) (ne (var zero)))

  nereadback : ∀{i Γ a} → Ne Val Γ a → Delay (Ne Nf Γ a) i
  nereadback (var x)   = now (var x)
  nereadback (app t v) = 
    nereadback t >>= (λ t → readback _ v >>= (λ n → now (app t n)))

postulate nereadback≤ : ∀{Γ Δ a}(α : Δ ≤ Γ)(t : Ne Val Γ a){n : Ne Nf Γ a} → 
                nereadback t ⇓ n → nereadback (nev≤ α t) ⇓ nen≤ α n



Read : ∀ {Δ a} (v : Val Δ a) (n : Nf Δ a) → Set
Read {Δ}{a} v n = {Γ : Cxt} (η : Γ ≤ Δ) → readback a (val≤ η v) ⇓ (nf≤ η n)

CanRead : ∀ {Δ a} (v : Val Δ a) → Set
CanRead v = ∃ λ n → Read v n

NRead : ∀ {Δ a} (v : Ne Val Δ a) (n : Ne Nf Δ a) → Set
NRead {Δ}{a} v n = {Γ : Cxt} (η : Γ ≤ Δ) → nereadback (nev≤ η v) ⇓ (nen≤ η n)

NCanRead : ∀ {Δ a} (v : Ne Val Δ a) → Set
NCanRead v = ∃ λ n → NRead v n


mutual
  V⟦_⟧_ : ∀{Γ}(a : Ty) → Val Γ a → Set
  V⟦ ★ ⟧ ne t = NCanRead t
  V⟦ a ⇒ b ⟧ f = ∀{Δ}(ρ : Δ ≤ _)(u : Val Δ a) 
    (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (apply (val≤ ρ f) u)

  C⟦_⟧_ : ∀{Γ}(a : Ty) → Delay (Val Γ a) ∞ → Set
  C⟦ a ⟧ x = ∃ λ v → x ⇓ v × V⟦ a ⟧ v

V≤ : ∀{Δ Δ′} a (η : Δ′ ≤ Δ)(v : Val Δ a)(〖v〗 : V⟦ a ⟧ v) → V⟦ a ⟧ (val≤ η v)
V≤ ★ η (ne t) (n , p) = 
  nen≤ η n , 
  λ ρ → subst (λ X → nereadback X ⇓ nen≤ ρ (nen≤ η n)) 
              (sym (nev≤-• ρ η t))
              (subst (λ Y → nereadback (nev≤ (ρ • η) t) ⇓ Y) 
                     (sym (nen≤-• ρ η n)) 
                     (p (ρ • η)))
V≤ (a ⇒ b) η v      p       ρ u u⇓ =   
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
⟪⟫≤ η (ρ , v) (θ , 〖v〗) = ⟪⟫≤ η ρ θ , V≤ _ η v 〖v〗

⟦var⟧ : ∀{Δ Γ a}(x : Var Γ a)(ρ : Env Δ Γ)(θ : ⟪ Γ ⟫ ρ) → 
            C⟦ a ⟧ (now (lookup x ρ))
⟦var⟧ zero   (_ , v) (_ , v⇓) = v , now⇓ , v⇓
⟦var⟧(suc x) (ρ , _) (θ , _ ) = ⟦var⟧ x ρ θ

β-expand : ∀{Γ Δ a b}{t : Tm (Γ , a) b}{ρ : Env Δ Γ}{u : Val Δ a}{v : Val Δ b}
           (h : eval t (ρ , u) ⇓ v) → apply (lam t ρ) u ⇓ v
β-expand h = later⇓ h

sound-β : ∀ {Δ Γ a b} {t : Tm (Γ , a) b} {ρ : Env Δ Γ} {u : Val Δ a} →
          C⟦ b ⟧ (eval t  (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)
sound-β (v , v⇓ , ⟦v⟧) = v , β-expand v⇓ , ⟦v⟧

⟦abs⟧ : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) →
  (∀{Δ'}(α : Δ' ≤ Δ)(u : Val Δ' a)(u⇓ : V⟦ a ⟧ u) → 
    C⟦ b ⟧ (eval t  (env≤ α ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))
⟦abs⟧ t ρ θ ih = (lam t ρ) , now⇓ , (λ α u p → 
  sound-β {t = t} {ρ = env≤ α ρ} {u = u} (ih α u p))

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

term : ∀ {Δ Γ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (eval t ρ)
term (var x)   ρ θ = ⟦var⟧ x ρ θ
term (abs t)   ρ θ = 
  ⟦abs⟧ t ρ θ (λ α u p → term t (env≤ α ρ , u) (⟪⟫≤ α ρ θ , p))
term (app t u) ρ θ = ⟦app⟧ (term t ρ θ) (term u ρ θ)


mutual
  rterm : ∀{Γ} a (v : Val Γ a) → V⟦ a ⟧ v → CanRead v
  rterm ★ (ne t) (n , p) = ne n , (λ η → later⇓ (map⇓ Nf.ne (p η)))
  rterm (a ⇒ b) f p =
    let v , q , r = p (weak id) 
                      (ne (var zero)) 
                      (rterm' a (var zero) (var zero , (λ η → now⇓))) 
        n , s = rterm b v r
    in lam n , λ η → {! !}
  rterm' : ∀{Γ} a (t : Ne Val Γ a) → NCanRead t → V⟦ a ⟧ ne t
  rterm' ★ t p = p
  rterm' (a ⇒ a₁) t p ρ u u⇓ = 
    ne (app (nev≤ ρ t) u) , 
    ({!!} , {!!})


{-
mutual
  rterm : ∀{Γ} a (v : Val Γ a) →   V⟦ a ⟧ v → CanRead a v
--  rterm ★        (ne t) (n , p) = 
--     ne n , later⇓ (map⇓ Nf.ne p) 
--  rterm ★ (ne t) p = let n , p' = p id in 
    ne n , 
    later⇓ (map⇓ ne (subst (λ X → nereadback X ⇓ fst (p id)) (nev≤-id t) p'))
  rterm (a ⇒ b)  f      p       =
    let v , q , r = p (weak id) 
                      (ne (var zero)) 
                      (rterm' a (var zero) ((var zero) , now⇓)) 
        n , s = rterm b v r
    in    
      lam n , later⇓ (later⇓ (>>=⇓ (λ x → now (lam x)) 
                                   (>>=⇓ (readback b) (unlater q) s) 
                                   now⇓))

  rterm' : ∀{Γ} a(t : Ne Val Γ a) → nereadback t ⇓ → V⟦ a ⟧ ne t
  rterm' ★ t p = {!!}
  rterm' (a ⇒ b) t (n , p) ρ u u⇓ = let n' , p' = rterm a u u⇓
                                        p'' = nereadback≤ ρ t p in
                              ne (app (nev≤ ρ t) u) , 
                              later⇓ now⇓ , 
                              rterm' b 
                                     (Ne.app (nev≤ ρ t) u) 
                                     (Ne.app (nen≤ ρ n) n' , 
         >>=⇓ (λ t₁ → later (∞readback a u ∞>>= (λ n₁ → now (Ne.app t₁ n₁)))) 
              p''
              (>>=⇓ (λ n₁ → now (Ne.app (nen≤ ρ n) n₁)) p' now⇓))
-}