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

lookup≤ : ∀ {Γ Δ Δ' a} (x : Var Γ a) (ρ : Env Δ Γ) (η : Δ' ≤ Δ) →
  val≤ η (lookup x ρ) ≡ lookup x (env≤ η ρ)
lookup≤ zero    (ρ , v) η = refl
lookup≤ (suc x) (ρ , v) η = lookup≤ x ρ η


weakVal : ∀ {Δ a c} → Val Δ c → Val (Δ , a) c
weakVal = val≤ (weak id)

ide : ∀ Γ → Env Γ Γ
ide ε = ε
ide (Γ , a) = env≤ (weak id) (ide Γ) , ne (var zero)

mutual
  eval : ∀{i Γ Δ a} → Tm Γ a → Env Δ Γ → Delay i (Val Δ a)
  eval (var x)   γ = now (lookup x γ)
  eval (abs t)   γ = now (lam t γ)
  eval (app t u) γ = apply* (eval t γ) (eval u γ)

  apply* : ∀{i Γ a b} → 
    Delay i (Val Γ (a ⇒ b)) → Delay i (Val Γ a) → Delay i (Val Γ b)
  apply* f v = apply =<<2 f , v

  apply : ∀{i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay i (Val Δ b)
  apply f v = later (∞apply f v)

  ∞apply : ∀{i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → ∞Delay i (Val Δ b)
  force (∞apply (ne x)    v) = now (ne (app x v))
  force (∞apply (lam t ρ) v) = eval t (ρ , v)


mutual
  eval≤~ : ∀ {i Γ Δ Δ' a} (t : Tm Γ a) (ρ : Env Δ Γ) (η : Δ' ≤ Δ) →
    _~_ {i} (val≤ η <$> (eval t ρ)) (eval t (env≤ η ρ))
  eval≤~ (var x)   ρ η rewrite lookup≤ x ρ η = ~now _
  eval≤~ (abs t)   ρ η = ~now _
  eval≤~ (app t u) ρ η = 
    proof
    ((eval t ρ >>=
      (λ a → eval u ρ >>= (λ v → later (∞apply a v))))
        >>= (λ x' → now (val≤ η x')))
    ~⟨ bind-assoc (eval t ρ) ⟩
    (eval t ρ >>=
      λ a → eval u ρ >>= (λ v → later (∞apply a v))
        >>= (λ x' → now (val≤ η x')))
    ~⟨ bind-cong-r (eval t ρ) (λ t₁ → bind-assoc (eval u ρ)) ⟩
    (eval t ρ >>=
      λ a → eval u ρ >>= λ v → later (∞apply a v)
        >>= (λ x' → now (val≤ η x')))
    ~⟨ bind-cong-r (eval t ρ) 
                   (λ t₁ → bind-cong-r (eval u ρ) 
                                       (λ u₁ → ~later (∞apply≤~ η t₁ u₁))) ⟩
    (eval t ρ >>=
     λ x' → eval u ρ >>= (λ x'' → later (∞apply (val≤ η x') (val≤ η x''))))
    ≡⟨⟩
    (eval t ρ >>= λ x' →
        (eval u ρ >>= λ x'' → now (val≤ η x'') >>= 
          λ v → later (∞apply (val≤ η x') v)))
    ~⟨ bind-cong-r (eval t ρ) (λ a → ~sym (bind-assoc (eval u ρ))) ⟩
    (eval t ρ >>= λ x' →
        (eval u ρ >>= λ x'' → now (val≤ η x'')) >>= 
          (λ v → later (∞apply (val≤ η x') v)))
    ~⟨ bind-cong-r (eval t ρ) (λ x' → bind-cong-l  (eval≤~ u ρ η) (λ _ → _)) ⟩
    (eval t ρ >>= λ x' →
        eval u (env≤ η ρ) >>= (λ v → later (∞apply (val≤ η x') v)))
    ≡⟨⟩
    (eval t ρ >>= λ x' → now (val≤ η x') >>=
      (λ a → eval u (env≤ η ρ) >>= (λ v → later (∞apply a v))))
    ~⟨ ~sym (bind-assoc (eval t ρ)) ⟩
    ((eval t ρ >>= (λ x' → now (val≤ η x'))) >>=
      (λ a → eval u (env≤ η ρ) >>= (λ v → later (∞apply a v))))
    ~⟨ bind-cong-l (eval≤~ t ρ η) (λ _ → _) ⟩
    (eval t (env≤ η ρ) >>=
      (λ a → eval u (env≤ η ρ) >>= (λ v → later (∞apply a v))))
    ∎ 
    where open ~-Reasoning

  ∞apply≤~ : ∀{i Γ Δ a b} (α : Δ ≤ Γ)(f : Val Γ (a ⇒ b))(v : Val Γ a) → 
             _∞~_ {i} (val≤ α ∞<$> ∞apply f v) (∞apply (val≤ α f) (val≤ α v))
  ~force (∞apply≤~ α (ne t)    v) = ~refl _
  ~force (∞apply≤~ α (lam t ρ) v) = eval≤~ t (ρ , v) α


mutual
  readback : ∀{i Γ} a → Val Γ a → Delay i (Nf Γ a)
  readback a v = later (∞readback a v)

  ∞readback : ∀{i Γ} a → Val Γ a → ∞Delay i (Nf Γ a)
  force (∞readback ★       (ne t)) = ne <$> nereadback t
  force (∞readback (a ⇒ b) v     ) = 
    lam <$> (readback b =<< apply (weakVal v) (ne (var zero)))

  nereadback : ∀{i Γ a} → Ne Val Γ a → Delay i (Ne Nf Γ a)
  nereadback (var x)   = now (var x)
  nereadback (app t v) = 
    nereadback t >>= (λ t → readback _ v >>= (λ n → now (app t n)))

mutual
  nereadback≤~ : ∀{i Γ Δ a}(α : Δ ≤ Γ)(t : Ne Val Γ a) → 
                 _~_ {i} (nen≤ α <$> nereadback t) (nereadback (nev≤ α t))
  nereadback≤~ α (var x) = ~now _
  nereadback≤~ α (app t u) = 
    proof
    ((nereadback t >>=
      (λ t₁ → readback _ u >>= (λ n → now (app t₁ n))))
                                   >>= (λ x' → now (nen≤ α x')))
    ~⟨ bind-assoc (nereadback t) ⟩
    (nereadback t >>= (λ x → 
      (readback _ u >>= (λ n → now (app x n)))
                                   >>= (λ x' → now (nen≤ α x'))))
    ~⟨ bind-cong-r (nereadback t) (λ x → bind-assoc (readback _ u)) ⟩
    (nereadback t >>= (λ x → 
       readback _ u >>= (λ y → now (app x y) >>= (λ x' → now (nen≤ α x')))))
    ≡⟨⟩
    (nereadback t >>=
      (λ x → (readback _ u >>= (λ y → now (app (nen≤ α x) (nf≤ α y))))))
    ≡⟨⟩
    (nereadback t >>=
           (λ x → (readback _ u >>= (λ x' → now (nf≤ α x') >>=
               (λ n → now (app (nen≤ α x) n))))))
    ~⟨ bind-cong-r (nereadback t) (λ x → ~sym (bind-assoc (readback _ u))) ⟩
    (nereadback t >>=
           (λ x → ((readback _ u >>= (λ x' → now (nf≤ α x'))) >>=
               (λ n → now (app (nen≤ α x) n)))))
    ≡⟨⟩
    (nereadback t >>= (λ x → now (nen≤ α x) >>=       
      (λ t₁ → ((readback _ u >>= (λ x' → now (nf≤ α x'))) >>=
          (λ n → now (app t₁ n))))))
    ~⟨ ~sym (bind-assoc (nereadback t)) ⟩
    ((nereadback t >>= (λ x' → now (nen≤ α x'))) >>=
      (λ t₁ → ((readback _ u >>= (λ x' → now (nf≤ α x'))) >>=
          (λ n → now (app t₁ n)))))
    ≡⟨⟩
    (nen≤ α <$> nereadback t >>=
       (λ t₁ → nf≤ α <$> readback _ u >>= (λ n → now (app t₁ n))))
    ~⟨ bind-cong-r (nen≤ α <$> nereadback t) 
                   (λ x → bind-cong-l (readback≤~ _ α u) 
                                      (λ x → _)) ⟩
    (nen≤ α <$> nereadback t >>=
       (λ t₁ → readback _ (val≤ α u) >>= (λ n → now (app t₁ n))))
    ~⟨  bind-cong-l (nereadback≤~ α t) (λ x → _) ⟩
    (nereadback (nev≤ α t) >>=
       (λ t₁ → readback _ (val≤ α u) >>= (λ n → now (app t₁ n))))
    ∎
    where open ~-Reasoning


  readback≤~ : ∀{i Γ Δ} a (α : Δ ≤ Γ)(v : Val Γ a) → 
                 _~_ {i} (nf≤ α <$> readback a v) (readback a (val≤ α v))
  readback≤~ a α v = ~later (∞readback≤~ a α v)

  ∞readback≤~ : ∀{i Γ Δ} a (α : Δ ≤ Γ)(v : Val Γ a) → 
                 _∞~_ {i} (nf≤ α ∞<$> ∞readback a v) (∞readback a (val≤ α v))
  ~force (∞readback≤~ ★       α (ne t)) = 
    proof
    ((nereadback t >>= (λ x' → now (ne x'))) >>= (λ a → now (nf≤ α a)))
    ~⟨ bind-assoc (nereadback t) ⟩ 
    (nereadback t >>= (λ x → now (ne x) >>= (λ a → now (nf≤ α a))))
    ≡⟨⟩
    (nereadback t >>= (λ x → now (ne (nen≤ α x))))
    ~⟨ ~sym (bind-assoc (nereadback t)) ⟩
    (nereadback t >>= (λ x' → now (nen≤ α x')) >>= (λ x' → now (ne x')))
    ~⟨ bind-cong-l (nereadback≤~ α t) (λ x → now (ne x)) ⟩
    (nereadback (nev≤ α t) >>= (λ x' → now (ne x')))
    ∎
    where open ~-Reasoning

  ~force (∞readback≤~ (a ⇒ b) α f     ) = ~later (
    proof
    ((∞apply (val≤ (weak id) f) (ne (var zero)) ∞>>=
      (λ v → later (∞readback b v)))
        ∞>>= (λ x' → now (lam x')))
          ∞>>= (λ a₁ → now (nf≤ α a₁))
    ∞~⟨ ∞bind-assoc (∞apply (val≤ (weak id) f) (ne (var zero)) ∞>>=
                               (λ v → later (∞readback b v))) ⟩
    (∞apply (val≤ (weak id) f) (ne (var zero)) ∞>>=
      (λ v → later (∞readback b v)))
        ∞>>= (λ x → now (lam x) >>= (λ a → now (nf≤ α a)))
    ≡⟨⟩
    (∞apply (val≤ (weak id) f) (ne (var zero)) ∞>>=
      (λ v → later (∞readback b v)))
        ∞>>= (λ x → now (lam (nf≤ (lift α) x)))
    ∞~⟨ ∞bind-assoc (∞apply (val≤ (weak id) f) (ne (var zero))) ⟩
    (∞apply (val≤ (weak id) f) (ne (var zero)) ∞>>= λ v →
      later (∞readback b v) >>= λ x → now (lam (nf≤ (lift α) x)))
    ∞~⟨ ∞bind-cong-r (∞apply (val≤ (weak id) f) (ne (var zero))) 
                     (λ v → ~later (∞~sym (∞bind-assoc (∞readback b v)))) ⟩
    (∞apply (val≤ (weak id) f) (ne (var zero)) ∞>>= λ a → 
      later (∞readback b a ∞>>= λ x → now (nf≤ (lift α) x)) >>= λ x' → now (lam x'))
    ∞~⟨ ∞bind-cong-r (∞apply (val≤ (weak id) f) (ne (var zero))) 
                     (λ a₁ → ~later (∞bind-cong-l (∞readback≤~ b (lift α) a₁)
                                                  (λ _ → _))) ⟩
    (∞apply (val≤ (weak id) f) (ne (var zero)) ∞>>= λ a → 
      later (∞readback b (val≤ (lift α) a)) >>= λ x' → now (lam x'))
    ∞~⟨ ∞~sym (∞bind-assoc (∞apply (val≤ (weak id) f) (ne (var zero)))) ⟩
    (∞apply (val≤ (weak id) f) (ne (var zero)) ∞>>=
      (λ a₁ → later (∞readback b (val≤ (lift α) a₁))))
        ∞>>= (λ x' → now (lam x'))
    ≡⟨⟩
    (∞apply (val≤ (weak id) f) (ne (var zero)) ∞>>= λ a →  
        now (val≤ (lift α) a) >>=
           (λ v → later (∞readback b v))) ∞>>= (λ x' → now (lam x'))
    ∞~⟨ ∞bind-cong-l (∞~sym (∞bind-assoc (∞apply (val≤ (weak id) f) 
                                                 (ne (var zero))))) 
                                         (λ _ → _) ⟩
    ((∞apply (val≤ (weak id) f) (ne (var zero)) ∞>>= 
        (λ a₁ → now (val≤ (lift α) a₁))) ∞>>=
           (λ v → later (∞readback b v))) ∞>>= (λ x' → now (lam x'))
    ∞~⟨ ∞bind-cong-l 
         (∞bind-cong-l 
           (∞apply≤~ (lift α) (val≤ (weak id) f) (ne (var zero))) 
           (λ _ → _)) 
         (λ _ → _) ⟩
    (∞apply (val≤ (lift α) (val≤ (weak id) f)) (ne (var zero)) ∞>>=
      (λ v → later (∞readback b v))) ∞>>= (λ x' → now (lam x'))
    ≡⟨ cong (λ f → (∞apply f (ne (var zero)) ∞>>= 
               (λ v → later (∞readback b v))) ∞>>= (λ x' → now (lam x')))
            (val≤-• (lift α) (weak id) f) ⟩
    (∞apply (val≤ (weak (α • id)) f) (ne (var zero)) ∞>>=
      (λ v → later (∞readback b v))) ∞>>= (λ x' → now (lam x'))
    ≡⟨ cong (λ α → (∞apply (val≤ (weak α) f) (ne (var zero)) ∞>>=
               (λ v → later (∞readback b v))) ∞>>= (λ x' → now (lam x')))
            (η•id α) ⟩
    (∞apply (val≤ (weak α) f) (ne (var zero)) ∞>>=
      (λ v → later (∞readback b v))) ∞>>= (λ x' → now (lam x'))
    ≡⟨ cong (λ f → (∞apply f (ne (var zero)) ∞>>= 
               (λ v → later (∞readback b v))) ∞>>= (λ x' → now (lam x')))
            (sym (val≤-• (weak id) α f)) ⟩
    (∞apply (val≤ (weak id) (val≤ α f)) (ne (var zero)) ∞>>=
      (λ v → later (∞readback b v))) ∞>>= (λ x' → now (lam x'))
    ∎)
    where open ∞~-Reasoning

nereadback≤ : ∀{Γ Δ a}(α : Δ ≤ Γ)(t : Ne Val Γ a){n : Ne Nf Γ a} → 
              nereadback t ⇓ n → nereadback (nev≤ α t) ⇓ nen≤ α n
nereadback≤ α t {n} p = subst~⇓ (map⇓ (nen≤ α) p) (nereadback≤~ α t)

mutual
  V⟦_⟧_ : ∀{Γ}(a : Ty) → Val Γ a → Set
  V⟦ ★ ⟧ ne t = nereadback t ⇓
  V⟦_⟧_ {Γ = Γ} (a ⇒ b) f = ∀{Δ}(ρ : Δ ≤ Γ)(u : Val Δ a) 
    (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (apply (val≤ ρ f) u)

  C⟦_⟧_ : ∀{Γ}(a : Ty) → Delay ∞ (Val Γ a) → Set
  C⟦ a ⟧ x = ∃ λ v → x ⇓ v × V⟦ a ⟧ v

V≤ : ∀{Δ Δ′} a (η : Δ′ ≤ Δ)(v : Val Δ a)(〖v〗 : V⟦ a ⟧ v) → V⟦ a ⟧ (val≤ η v)
V≤ ★       η (ne t) (n , p)        = nen≤ η n , nereadback≤ η t p
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
  {u* : Delay _ (Val Δ a)} {u : Val Δ a} (u⇓ : u* ⇓ u) →
  {v : Val Δ b} →  later (∞apply f u) ⇓ v → (u* >>= λ u → apply f u) ⇓ v
sound-app' f (later⇓ u⇓) h = later⇓ (sound-app' f u⇓ h)
sound-app' f  now⇓       h = h

sound-app : ∀ {Δ a b} →
  {f* : Delay _ (Val Δ (a ⇒ b))} {f : Val Δ (a ⇒ b)} (f⇓ : f* ⇓ f) →
  {u* : Delay _ (Val Δ a)      } {u : Val Δ a}       (u⇓ : u* ⇓ u) →
  {v : Val Δ b} →  later (∞apply f u) ⇓ v → apply* f* u* ⇓ v
sound-app  (later⇓ f⇓) u⇓ h = later⇓ (sound-app f⇓ u⇓ h)
sound-app {f = f} now⇓ u⇓ h = sound-app' f u⇓ h

⟦app⟧ : ∀ {Δ a b} {f : Delay _ (Val Δ (a ⇒ b))} {u : Delay _ (Val Δ a)} →
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
  rterm : ∀{Γ} a (v : Val Γ a) →   V⟦ a ⟧ v → readback a v ⇓
  rterm ★        (ne t) (n , p) = 
     ne n , later⇓ (map⇓ Nf.ne p) 
  rterm (a ⇒ b)  f      p       =
    let v , q , r = p (weak id) 
                      (ne (var zero)) 
                      (rterm' a (var zero) ((var zero) , now⇓)) 
        n , s = rterm b v r
    in    
      lam n , later⇓ (later⇓ (>>=⇓ (λ x → now (lam x)) 
                                   (>>=⇓ (readback b) (unlater q) s) 
                                   now⇓))

  rterm' : ∀{Γ} a (t : Ne Val Γ a) → nereadback t ⇓ → V⟦ a ⟧ ne t
  rterm' ★ t p = p
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

var⇓ : ∀{Γ a}(x : Var Γ a) → V⟦ a ⟧ ne (var x)
var⇓ x = rterm' _ (var x) (var x , now⇓)

ide⇓ : ∀ Γ → ⟪ Γ ⟫ ide Γ
ide⇓ ε       = _
ide⇓ (Γ , a) = ⟪⟫≤ (weak id) (ide Γ) (ide⇓ Γ) , var⇓ zero

nf : ∀{Γ a}(t : Tm Γ a) → Delay ∞ (Nf Γ a)
nf {Γ}{a} t = eval t (ide Γ) >>= readback a

nterm : ∀{Γ a}(t : Tm Γ a) → ∃ λ n → nf t ⇓ n
nterm {Γ}{a} t = let v , p , q = term t (ide Γ) (ide⇓ Γ) 
                     n , r = rterm a v q in 
                     n , >>=⇓ (readback a) p r