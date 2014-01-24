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

wk : ∀{Γ a} → (Γ , a) ≤ Γ
wk = weak id

weakVal : ∀ {Δ a c} → Val Δ c → Val (Δ , a) c
weakVal = val≤ wk

ide : ∀ Γ → Env Γ Γ
ide ε = ε
ide (Γ , a) = env≤ wk (ide Γ) , ne (var zero)

mutual
  eval : ∀{i Γ Δ a} → Tm Γ a → Env Δ Γ → Delay i (Val Δ a)
  eval (var x)   ρ = now (lookup x ρ)
  eval (abs t)   ρ = now (lam t ρ)
  eval (app t u) ρ = eval t ρ >>= λ f → eval u ρ >>= apply f

  apply : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay i (Val Δ b)
  apply (ne w)    v = now (ne (app w v))
  apply (lam t ρ) v = later (beta t ρ v)

  beta : ∀ {i Γ a b} (t : Tm (Γ , a) b)
    {Δ : Cxt} (ρ : Env Δ Γ) (v : Val Δ a) → ∞Delay i (Val Δ b)
  force (beta t ρ v) = eval t (ρ , v)

mutual 
  eval≤    : ∀ {i Γ Δ Δ′ a} (t : Tm Γ a) (ρ : Env Δ Γ) (η : Δ′ ≤ Δ) → 
             (val≤ η <$> (eval t ρ)) ~⟨ i ⟩~ (eval t (env≤ η ρ))           
  eval≤ (var x)   ρ η rewrite lookup≤ x ρ η = ~now _
  eval≤ (abs t)   ρ η = ~now _
  eval≤ (app t u) ρ η =
    proof
    ((eval t ρ >>=
      (λ f → eval u ρ >>= (λ v → apply f v)))
        >>= (λ x′ → now (val≤ η x′)))
    ~⟨ bind-assoc (eval t ρ) ⟩
    (eval t ρ >>=
      λ f → eval u ρ >>= (λ v → apply f v)
        >>= (λ x′ → now (val≤ η x′)))
    ~⟨ bind-cong-r (eval t ρ) (λ t₁ → bind-assoc (eval u ρ)) ⟩
    (eval t ρ >>=
      λ f → eval u ρ >>= λ v → apply f v
        >>= (λ x′ → now (val≤ η x′)))
    ~⟨ bind-cong-r (eval t ρ)
                   (λ t₁ → bind-cong-r (eval u ρ)
                                       (λ u₁ → apply≤ t₁ u₁ η )) ⟩
    (eval t ρ >>=
     λ x′ → eval u ρ >>= (λ x′′ → apply (val≤ η x′) (val≤ η x′′)))
    ≡⟨⟩
    (eval t ρ >>= λ x′ →
        (eval u ρ >>= λ x′′ → now (val≤ η x′′) >>=
          λ v → apply (val≤ η x′) v))
    ~⟨ bind-cong-r (eval t ρ) (λ a → ~sym (bind-assoc (eval u ρ))) ⟩
    (eval t ρ >>= λ x′ →
        (eval u ρ >>= λ x′′ → now (val≤ η x′′)) >>=
          (λ v → apply (val≤ η x′) v))
    ~⟨ bind-cong-r (eval t ρ) (λ x′ → bind-cong-l  (eval≤ u ρ η) (λ _ → _)) ⟩
    (eval t ρ >>= λ x′ →
        eval u (env≤ η ρ) >>= (λ v → apply (val≤ η x′) v))
    ≡⟨⟩
    (eval t ρ >>= λ x′ → now (val≤ η x′) >>=
      (λ f → eval u (env≤ η ρ) >>= (λ v → apply f v)))
    ~⟨ ~sym (bind-assoc (eval t ρ)) ⟩
    ((eval t ρ >>= (λ x′ → now (val≤ η x′))) >>=
      (λ f → eval u (env≤ η ρ) >>= (λ v → apply f v)))
    ~⟨ bind-cong-l (eval≤ t ρ η) (λ _ → _) ⟩
    (eval t (env≤ η ρ) >>=
      (λ f → eval u (env≤ η ρ) >>= (λ v → apply f v)))
    ∎
    where open ~-Reasoning

  apply≤  : ∀{i Γ Δ a b} (f : Val Γ (a ⇒ b))(v : Val Γ a)(η : Δ ≤ Γ) →       
            (val≤ η <$> apply f v) ~⟨ i ⟩~ (apply (val≤ η f) (val≤ η v))
  apply≤ (ne x)    v η = ~refl _
  apply≤ (lam t ρ) v η = ~later (beta≤ t ρ v η)

  beta≤ : ∀ {i Γ Δ E a b} (t : Tm (Γ , a) b)(ρ : Env Δ Γ) (v : Val Δ a) →
          (η : E ≤ Δ) →
          (val≤ η ∞<$> (beta t ρ v)) ∞~⟨ i ⟩~ beta t (env≤ η ρ) (val≤ η v)
  ~force (beta≤ t ρ v η) = eval≤ t (ρ , v) η


mutual
  readback : ∀{i Γ a} → Val Γ a → Delay i (Nf Γ a)
  readback {a = ★} (ne w) = ne  <$> nereadback w
  readback {a = _ ⇒ _} v = lam <$> later (eta v)

  eta : ∀{i Γ a b} → Val Γ (a ⇒ b) → ∞Delay i (Nf (Γ , a) b)
  force (eta v) = readback =<< apply (weakVal v) (ne (var zero))

  nereadback : ∀{i Γ a} → Ne Val Γ a → Delay i (Ne Nf Γ a)
  nereadback (var x)   = now (var x)
  nereadback (app w v) =
    nereadback w >>= λ m → app m <$> readback v

mutual
  nereadback≤ : ∀{i Γ Δ a}(η : Δ ≤ Γ)(t : Ne Val Γ a) →
                (nen≤ η <$> nereadback t) ~⟨ i ⟩~ (nereadback (nev≤ η t))
  nereadback≤ η (var x) = ~now _                                                  
  nereadback≤ η (app t u) =                                                       
    proof                                                                         
    ((nereadback t >>=                                                            
      (λ t₁ → readback u >>= (λ n → now (app t₁ n))))                             
                                   >>= (λ x′ → now (nen≤ η x′)))                  
    ~⟨ bind-assoc (nereadback t) ⟩                                                
    (nereadback t >>= (λ x →                                                      
      (readback u >>= (λ n → now (app x n)))                                      
                                   >>= (λ x′ → now (nen≤ η x′))))                 
    ~⟨ bind-cong-r (nereadback t) (λ x → bind-assoc (readback u)) ⟩               
    (nereadback t >>= (λ x →                                                      
       readback u >>= (λ y → now (app x y) >>= (λ x′ → now (nen≤ η x′)))))        
    ≡⟨⟩                                                                           
    (nereadback t >>=                                                             
      (λ x → (readback u >>= (λ y → now (app (nen≤ η x) (nf≤ η y))))))            
    ≡⟨⟩                                                                           
    (nereadback t >>=                                                             
           (λ x → (readback u >>= (λ x′ → now (nf≤ η x′) >>=                      
               (λ n → now (app (nen≤ η x) n))))))                                 
    ~⟨ bind-cong-r (nereadback t) (λ x → ~sym (bind-assoc (readback u))) ⟩        
    (nereadback t >>=                                                             
           (λ x → ((readback u >>= (λ x′ → now (nf≤ η x′))) >>=                   
               (λ n → now (app (nen≤ η x) n)))))                                  
    ≡⟨⟩                                                                           
    (nereadback t >>= (λ x → now (nen≤ η x) >>=
      (λ t₁ → ((readback u >>= (λ x′ → now (nf≤ η x′))) >>=
          (λ n → now (app t₁ n))))))
    ~⟨ ~sym (bind-assoc (nereadback t)) ⟩
    ((nereadback t >>= (λ x′ → now (nen≤ η x′))) >>=
      (λ t₁ → ((readback u >>= (λ x′ → now (nf≤ η x′))) >>=
          (λ n → now (app t₁ n)))))
    ≡⟨⟩
    (nen≤ η <$> nereadback t >>=
       (λ t₁ → nf≤ η <$> readback u >>= (λ n → now (app t₁ n))))
    ~⟨ bind-cong-r (nen≤ η <$> nereadback t)
                   (λ x → bind-cong-l (readback≤ _ η u)
                                      (λ x → _)) ⟩
    (nen≤ η <$> nereadback t >>=
       (λ t₁ → readback (val≤ η u) >>= (λ n → now (app t₁ n))))
    ~⟨  bind-cong-l (nereadback≤ η t) (λ x → _) ⟩
    (nereadback (nev≤ η t) >>=
       (λ t₁ → readback (val≤ η u) >>= (λ n → now (app t₁ n))))
    ∎
    where open ~-Reasoning
    
  readback≤   : ∀{i Γ Δ} a (η : Δ ≤ Γ)(v : Val Γ a) →
                (nf≤ η <$> readback v) ~⟨ i ⟩~ (readback (val≤ η v))
  readback≤ ★ η (ne w) =
    proof
      nf≤ η  <$>  (ne  <$> nereadback w)   ~⟨ map-compose (nereadback w) ⟩
      (nf≤ η ∘ ne)     <$> nereadback w     ≡⟨⟩
      (Nf.ne ∘ nen≤ η) <$> nereadback w     ~⟨ ~sym (map-compose (nereadback w)) ⟩
      ne <$>  (nen≤ η  <$> nereadback w)    ~⟨ map-cong ne (nereadback≤ η w) ⟩
      ne <$>   nereadback (nev≤ η w)
    ∎
    where open ~-Reasoning
  readback≤ (a ⇒ b) η f      = ~later (
    proof
    (eta f ∞>>= (λ a₁ → now (lam a₁))) ∞>>= (λ x' → now (nf≤ η x'))
    ∞~⟨ ∞bind-assoc (eta f) ⟩
    (eta f ∞>>= λ a₁ → now (lam a₁) >>= λ x' → now (nf≤ η x'))
    ≡⟨⟩
    (eta f ∞>>= (λ a₁ → now (lam (nf≤ (lift η) a₁))))
    ≡⟨⟩
    (eta f ∞>>= λ a₁ → now (nf≤ (lift η) a₁) >>= λ a₁ → now (lam a₁))
    ∞~⟨ ∞~sym (∞bind-assoc (eta f)) ⟩
    (eta f ∞>>= (λ a₁ → now (nf≤ (lift η) a₁))) ∞>>= (λ a₁ → now (lam a₁))
    ∞~⟨ ∞bind-cong-l (eta≤ η f) (λ a → now (lam a)) ⟩
    eta (val≤ η f) ∞>>= (λ a₁ → now (lam a₁))
    ∎)
    where open ∞~-Reasoning
  
  eta≤  : ∀{i Γ Δ a b} (η : Δ ≤ Γ)(v : Val Γ (a ⇒ b)) →
          (nf≤ (lift η) ∞<$> eta v) ∞~⟨ i ⟩~ (eta (val≤ η v))
  ~force (eta≤ η f) =
    proof
    ((apply (weakVal f) (ne (var zero)) >>= readback)
      >>= (λ a → now (nf≤ (lift η) a)))
    ~⟨ bind-assoc (apply (weakVal f) (ne (var zero))) ⟩
    (apply (weakVal f) (ne (var zero)) >>=
         (λ z → readback z >>= (λ x' → now (nf≤ (lift η) x'))))
    ~⟨ bind-cong-r (apply (weakVal f) (ne (var zero)))
                   (λ x → readback≤ _ (lift η) x) ⟩
    (apply (weakVal f) (ne (var zero)) >>=
      (λ x' → readback (val≤ (lift η) x')))
    ≡⟨⟩
    (apply (weakVal f) (ne (var zero)) >>=
          (λ x' → now (val≤ (lift η) x') >>= readback))
    ~⟨ ~sym (bind-assoc (apply (weakVal f) (ne (var zero))))  ⟩
    ((apply (weakVal f) (ne (var zero)) >>=
          (λ x' → now (val≤ (lift η) x')))
         >>= readback)
    ~⟨ bind-cong-l (apply≤ (weakVal f) (ne (var zero)) (lift η)) readback ⟩
    (apply (val≤ (lift η) (val≤ wk f)) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ f₁ → apply f₁ (ne (var zero)) >>= readback)
             (val≤-• (lift η) wk f) ⟩
    (apply (val≤ (weak (η • id)) f) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ η₁ → apply (val≤ (weak η₁) f) (ne (var zero)) >>= readback)
            (η•id η) ⟩
    (apply (val≤ (weak η) f) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ f₁ → apply f₁ (ne (var zero)) >>= readback)
            (sym (val≤-• wk η f)) ⟩
    (apply (weakVal (val≤ η f)) (ne (var zero)) >>= readback)
    ∎
    where open ~-Reasoning

mutual
  V⟦_⟧_ : ∀{Γ}(a : Ty) → Val Γ a → Set
  V⟦ ★ ⟧ ne t = nereadback t ⇓
  V⟦_⟧_ {Γ = Γ} (a ⇒ b) f = ∀{Δ}(ρ : Δ ≤ Γ)(u : Val Δ a) 
    (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (apply (val≤ ρ f) u)

  C⟦_⟧_ : ∀{Γ}(a : Ty) → Delay ∞ (Val Γ a) → Set
  C⟦ a ⟧ x = ∃ λ v → x ⇓ v × V⟦ a ⟧ v

E⟦_⟧_ : ∀{Δ}(Γ : Cxt) → Env Δ Γ → Set
E⟦ ε ⟧     ε       = ⊤
E⟦ Γ , a ⟧ (ρ , v) = E⟦ Γ ⟧ ρ × V⟦ a ⟧ v

nereadback≤⇓ : ∀{Γ Δ a}(η : Δ ≤ Γ)(t : Ne Val Γ a){n : Ne Nf Γ a} →
              nereadback t ⇓ n → nereadback (nev≤ η t) ⇓ nen≤ η n
nereadback≤⇓ η t {n} p = subst~⇓ (map⇓ (nen≤ η) p) (nereadback≤ η t)

V⟦⟧≤ : ∀{Δ Δ′} a (η : Δ′ ≤ Δ)(v : Val Δ a)(⟦v⟧ : V⟦ a ⟧ v) → V⟦ a ⟧ (val≤ η v)
V⟦⟧≤ ★       η (ne t) (n , p)        = nen≤ η n , nereadback≤⇓ η t p
V⟦⟧≤ (a ⇒ b) η v      p       ρ u u⇓ =
  let v′ , p′ , p′′ = p (ρ • η) u u⇓ in
      v′ , subst (λ X → apply X u ⇓ fst (p (ρ • η) u u⇓))
                 ((sym (val≤-• ρ η v)))
                 p′
         , p′′

E⟦⟧≤ : ∀{Γ Δ Δ′} (η : Δ′ ≤ Δ) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) → E⟦ Γ ⟧ (env≤ η ρ)
E⟦⟧≤ η ε       θ        = _
E⟦⟧≤ η (ρ , v) (θ , ⟦v⟧) = E⟦⟧≤ η ρ θ , V⟦⟧≤ _ η v ⟦v⟧

⟦var⟧ : ∀{Δ Γ a} (x : Var Γ a) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
            C⟦ a ⟧ (now (lookup x ρ))
⟦var⟧ zero   (_ , v) (_ , v⇓) = v , now⇓ , v⇓
⟦var⟧(suc x) (ρ , _) (θ , _ ) = ⟦var⟧ x ρ θ

sound-β : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (u : Val Δ a) →
          C⟦ b ⟧ (eval t  (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)
sound-β t ρ u (v , v⇓ , ⟦v⟧) = v , later⇓ v⇓ , ⟦v⟧

⟦abs⟧ : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
  (∀{Δ′}(η : Δ′ ≤ Δ)(u : Val Δ′ a)(u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (eval t (env≤ η ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))
⟦abs⟧ t ρ θ ih = lam t ρ , now⇓ , (λ η u p → sound-β t (env≤ η ρ) u (ih η u p))

⟦app⟧ : ∀ {Δ a b} {f? : Delay _ (Val Δ (a ⇒ b))} {u? : Delay _ (Val Δ a)} →
          C⟦ a ⇒ b ⟧ f? → C⟦ a ⟧ u? → C⟦ b ⟧ (f? >>= λ f → u? >>= apply f)
⟦app⟧ {u? = u?} (f , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) =
  let v , v⇓ , ⟦v⟧ = ⟦f⟧ id u ⟦u⟧
      v⇓′          = bind⇓ (λ f′ → u? >>= apply f′)
                    f⇓
                    (bind⇓ (apply f)
                          u⇓
                          (subst (λ X → apply X u ⇓ v)
                                 (val≤-id f)
                                 v⇓))
  in  v , v⇓′ , ⟦v⟧

term : ∀ {Δ Γ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) → C⟦ a ⟧ (eval t ρ)
term (var x)   ρ θ = ⟦var⟧ x ρ θ
term (abs t)   ρ θ = ⟦abs⟧ t ρ θ (λ η u p →
  term t (env≤ η ρ , u) (E⟦⟧≤ η ρ θ , p))
term (app t u) ρ θ = ⟦app⟧ (term t ρ θ) (term u ρ θ)


mutual
  reify : ∀{Γ} a (v : Val Γ a) → V⟦ a ⟧ v → readback v ⇓
  reify ★        (ne _) (m , ⇓m) = ne m , map⇓ ne ⇓m
  reify (a ⇒ b)  f      ⟦f⟧      =
    let u           = ne (var zero)
        ⟦u⟧          = reflect a (var zero) (var zero , now⇓)
        v , v⇓ , ⟦v⟧ = ⟦f⟧ wk u ⟦u⟧
        n , ⇓n = reify b v ⟦v⟧
        ⇓λn    = later⇓ (bind⇓ (λ x → now (lam x))
                               (bind⇓ readback v⇓ ⇓n)
                               now⇓)
    in  lam n , ⇓λn

  reflect : ∀{Γ} a (w : Ne Val Γ a) → nereadback w ⇓ → V⟦ a ⟧ (ne w)
  reflect ★ w w⇓ = w⇓
  reflect (a ⇒ b) w (m , w⇓m) η u ⟦u⟧ =
    let n , ⇓n = reify a u ⟦u⟧
        m′      = nen≤ η m
        ⇓m     = nereadback≤⇓ η w w⇓m
        wu     = app (nev≤ η w) u
        ⟦wu⟧   = reflect b wu (app m′ n ,
                   bind⇓ (λ m → app m <$> readback u)
                        ⇓m
                        (bind⇓ (λ n → now (app m′ n)) ⇓n now⇓))
    in  ne wu , now⇓ , ⟦wu⟧

var↑ : ∀{Γ a}(x : Var Γ a) → V⟦ a ⟧ ne (var x)
var↑ x = reflect _ (var x) (var x , now⇓)

⟦ide⟧ : ∀ Γ → E⟦ Γ ⟧ (ide Γ)
⟦ide⟧ ε       = _
⟦ide⟧ (Γ , a) = E⟦⟧≤ wk (ide Γ) (⟦ide⟧ Γ) , var↑ zero

nf : ∀{Γ a}(t : Tm Γ a) → Delay ∞ (Nf Γ a)
nf t = eval t (ide _) >>= readback

normalize : ∀ Γ a (t : Tm Γ a) → ∃ λ n → nf t ⇓ n
normalize Γ a t = let v , v⇓ , ⟦v⟧ = term t (ide Γ) (⟦ide⟧ Γ)
                      n , ⇓n      = reify a v ⟦v⟧
                  in  n , bind⇓ readback v⇓ ⇓n