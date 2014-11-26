{-# OPTIONS --copatterns --sized-types #-}

module SpinelessValues where

open import Library
open import Term hiding (Nf; module Nf) -- ; nf≤; NfFun; nf≤-id; nf≤-•)
open import Spine
open import Delay
open import RenamingAndSubstitution


data Ne (T : Cxt → Ty → Set)(Γ : Cxt) : Ty → Set where
  var : ∀{a} → Var Γ a → Ne T Γ a
  app : ∀{a b} → Ne T Γ (a ⇒ b) → T Γ a → Ne T Γ b

data Nf (Γ : Cxt) : Ty → Set where
  lam : ∀{a b}(n : Nf (Γ , a) b) → Nf Γ (a ⇒ b)
  ne  : Ne Nf Γ ★ → Nf Γ ★

{-
mutual
  nf≤ : ∀{Γ Δ} → Γ ≤ Δ → ∀{a} → Nf Δ a → Nf Γ a
  nf≤ α (ne t)   = ne (nen≤ α t)
  nf≤ α (lam t)  = lam (nf≤ (lift α) t)

  nen≤ : ∀{Γ Δ} → Γ ≤ Δ → ∀{a} → Ne Nf Δ a → Ne Nf Γ a
  nen≤ α (var x)   = var (var≤ α x)
  nen≤ α (app t u) = app (nen≤ α t) (nf≤ α u)

-}


mutual
  rennf : ∀{Γ Δ} → Ren Δ Γ → ∀{a} → Nf Δ a → Nf Γ a
  rennf α (ne t)   = ne (rennen α t)
  rennf α (lam t)  = lam (rennf (wk α) t)

  rennen : ∀{Γ Δ} → Ren Δ Γ → ∀{a} → Ne Nf Δ a → Ne Nf Γ a
  rennen α (var x) = var (α x)
  rennen α (app n x) = app (rennen α n) (rennf α x)

{-
-- first functor law
mutual
  nf≤-id : ∀ {Δ a} (n : Nf Δ a) → nf≤ id n ≡ n
  nf≤-id (lam n) = cong lam {!!} -- need lift' trick/unique OPEs
  nf≤-id (ne n)  = cong ne (nen≤-id n)

  nen≤-id : ∀ {Δ a} (n : Ne Nf Δ a) → nen≤ id n ≡ n
  nen≤-id (var x)    = refl
  nen≤-id (app n n') = cong₂ app (nen≤-id n) (nf≤-id n')
-}

{-
-- second functor law
mutual
  nf≤-• : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (n : Nf Δ₃ a) →
          nf≤ η (nf≤ η' n) ≡ nf≤ (η • η') n
  nf≤-• η η' (lam n) = proof
    lam (nf≤ (lift η) (nf≤ (lift η') n)) 
    ≡⟨ cong lam (nf≤-•  (lift η) (lift η') n ) ⟩
    lam (nf≤ (lift η • lift η') n)
    ≡⟨⟩
    lam (nf≤ (lift (η • η')) n) 
    ∎
    where open ≡-Reasoning renaming (begin_ to proof_)
  nf≤-• η η' (ne n)  = cong ne (nen≤-• η η' n)

  nen≤-• : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (n : Ne Nf Δ₃ a) →
          nen≤ η (nen≤ η' n) ≡ nen≤ (η • η') n
  nen≤-• η η' (var x)   = cong var (var≤-• η η' x)
  nen≤-• η η' (app n n') = cong₂ app (nen≤-• η η' n) (nf≤-• η η' n')
-}
-- nf≤ forms a functor from the category of OPEs
{-
NfFun : Fun OPECat (Fam Ty Nf)
NfFun = record 
  { OMap  = idf
  ; HMap  = nf≤ 
  ; fid   = iext λ a → ext λ n → ≡-to-≅ (nf≤-id n)
  ; fcomp = λ {_ _ _ f g} → iext λ a → ext λ n → ≡-to-≅ (sym (nf≤-• g f n))
  }

NeNFun : Fun OPECat (Fam Ty (Ne Nf))
NeNFun = record 
  { OMap  = idf
  ; HMap  = nen≤ 
  ; fid   = iext λ a → ext λ n → ≡-to-≅ (nen≤-id n)
  ; fcomp = λ {_ _ _ f g} → iext λ a → ext λ n → ≡-to-≅ (sym (nen≤-• g f n))
  }
-}

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

{-
-- val≤ forms a functor from the category of OPEs
ValFun : Fun OPECat (Fam Ty Val)
ValFun = record 
  { OMap  = idf
  ; HMap  = val≤ 
  ; fid   = iext λ a → ext λ n → ≡-to-≅ (val≤-id n)
  ; fcomp = λ {_ _ _ f g} → iext λ a → ext λ n → ≡-to-≅ (sym (val≤-• g f n))
  }
-}

{-
NeVFun : Fun OPECat (Fam Ty (Ne Val))
NeVFun = record 
  { OMap  = idf
  ; HMap  = nev≤ 
  ; fid   = iext λ a → ext λ n → ≡-to-≅ (nev≤-id n)
  ; fcomp = λ {_ _ _ f g} → iext λ a → ext λ n → ≡-to-≅ (sym (nev≤-• g f n))
  }
-}

{-
EnvFun : Fun OPECat (Fam Cxt Env)
EnvFun = record 
  { OMap  = idf
  ; HMap  = env≤ 
  ; fid   = iext λ a → ext λ n → ≡-to-≅ (env≤-id n)
  ; fcomp = λ {_ _ _ f g} → iext λ a → ext λ n → ≡-to-≅ (sym (env≤-• g f n))
  }
-}

{-
wk : ∀{Γ a} → (Γ , a) ≤ Γ
wk = weak id
-}


mutual
  renval : ∀{Γ Δ} → Ren Γ Δ → ∀ {σ} → Val Γ σ → Val Δ σ
  renval f (ne x)    = ne (rennev f x)
  renval f (lam t ρ) = lam t (renenv f ρ)

  renenv : ∀{Γ Δ} → Ren Γ Δ → ∀ {B} → Env Γ B → Env Δ B
  renenv f ε       = ε
  renenv f (e , v) = renenv f e , renval f v

  rennev : ∀{Γ Δ} → Ren Γ Δ → ∀ {σ} → Ne Val Γ σ → Ne Val Δ σ
  rennev f (var x)   = var (f x)
  rennev f (app t u) = app (rennev f t) (renval f u)

lookup≤ : ∀ {Γ Δ Δ' a} (x : Var Γ a) (ρ : Env Δ Γ) (η : Ren Δ Δ') →
  renval η (lookup x ρ) ≡ lookup x (renenv η ρ)
lookup≤ zero    (ρ , v) η = refl
lookup≤ (suc x) (ρ , v) η = lookup≤ x ρ η



mutual
  renvalid : {Γ : Cxt} {σ : Ty} (v : Val Γ σ) → renval renId v ≡ idf v
  renvalid (ne x)    = cong ne (rennevid x)
  renvalid (lam t ρ) = cong (lam t) (renenvid ρ)

  renenvid : {Γ Δ : Cxt}(e : Env Γ Δ) → renenv renId e ≡ idf e
  renenvid ε       = refl
  renenvid (e , v) = cong₂ _,_ (renenvid e) (renvalid v)

  rennevid : {Γ : Cxt} {σ : Ty} (n : Ne Val Γ σ) → rennev renId n ≡ idf n
  rennevid (var x)   = refl
  rennevid (app n v) = cong₂ app (rennevid n) (renvalid v)


mutual
  renenvcomp : ∀ {Γ Δ₁ Δ₂ Δ₃} (η : Ren Δ₂ Δ₁) (η' : Ren Δ₃ Δ₂) (ρ : Env Δ₃ Γ) →
           renenv η (renenv η' ρ) ≡ renenv (η ∘ η') ρ
  renenvcomp η η' ε       = refl
  renenvcomp η η' (ρ , v) = cong₂ _,_ (renenvcomp η η' ρ) (renvalcomp η η' v)

  renvalcomp : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Ren Δ₂ Δ₁) (η' : Ren Δ₃ Δ₂) (v : Val Δ₃ a) →
           renval η (renval η' v) ≡ renval (η ∘ η') v
  renvalcomp η η' (ne t) = cong ne (rennevcomp η η' t)
  renvalcomp η η' (lam t ρ) = cong (lam t) (renenvcomp η η' ρ)

  rennevcomp : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Ren Δ₂ Δ₁) (η' : Ren Δ₃ Δ₂) (t : Ne Val Δ₃ a) →
           rennev η (rennev η' t) ≡ rennev (η ∘ η') t
  rennevcomp η η' (var x)   = refl
  rennevcomp η η' (app t u) = cong₂ app (rennevcomp η η' t) (renvalcomp η η' u)

weakVal : ∀ {Δ a c} → Val Δ c → Val (Δ , a) c
weakVal = renval suc


ide : ∀ Γ → Env Γ Γ
ide ε = ε
ide (Γ , a) = renenv suc (ide Γ) , ne (var zero)

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
  reneval    : ∀ {i Γ Δ Δ′ a} (t : Tm Γ a) (ρ : Env Δ Γ) (η : Ren Δ Δ′) →
             (renval η <$> (eval t ρ)) ~⟨ i ⟩~ (eval t (renenv η ρ))
  reneval (var x)   ρ η rewrite lookup≤ x ρ η = ~now _
  reneval (abs t)   ρ η = ~now _
  reneval (app t u) ρ η =
    proof
    ((eval t ρ >>=
      (λ f → eval u ρ >>= (λ v → apply f v)))
        >>= (λ x′ → now (renval η x′)))
    ~⟨ bind-assoc (eval t ρ) ⟩
    (eval t ρ >>=
      λ f → eval u ρ >>= (λ v → apply f v)
        >>= (λ x′ → now (renval η x′)))
    ~⟨ bind-cong-r (eval t ρ) (λ t₁ → bind-assoc (eval u ρ)) ⟩
    (eval t ρ >>=
      λ f → eval u ρ >>= λ v → apply f v
        >>= (λ x′ → now (renval η x′)))
    ~⟨ bind-cong-r (eval t ρ)
                   (λ t₁ → bind-cong-r (eval u ρ)
                                       (λ u₁ → renapply t₁ u₁ η )) ⟩
    (eval t ρ >>=
     λ x′ → eval u ρ >>= (λ x′′ → apply (renval η x′) (renval η x′′)))
    ≡⟨⟩
    (eval t ρ >>= λ x′ →
        (eval u ρ >>= λ x′′ → now (renval η x′′) >>=
          λ v → apply (renval η x′) v))
    ~⟨ bind-cong-r (eval t ρ) (λ a → ~sym (bind-assoc (eval u ρ))) ⟩
    (eval t ρ >>= λ x′ →
        (eval u ρ >>= λ x′′ → now (renval η x′′)) >>=
          (λ v → apply (renval η x′) v))
    ~⟨ bind-cong-r (eval t ρ) (λ x′ → bind-cong-l  (reneval u ρ η) (λ _ → _)) ⟩
    (eval t ρ >>= λ x′ →
        eval u (renenv η ρ) >>= (λ v → apply (renval η x′) v))
    ≡⟨⟩
    (eval t ρ >>= λ x′ → now (renval η x′) >>=
      (λ f → eval u (renenv η ρ) >>= (λ v → apply f v)))
    ~⟨ ~sym (bind-assoc (eval t ρ)) ⟩
    ((eval t ρ >>= (λ x′ → now (renval η x′))) >>=
      (λ f → eval u (renenv η ρ) >>= (λ v → apply f v)))
    ~⟨ bind-cong-l (reneval t ρ η) (λ _ → _) ⟩
    (eval t (renenv η ρ) >>=
      (λ f → eval u (renenv η ρ) >>= (λ v → apply f v)))
    ∎
    where open ~-Reasoning

  renapply  : ∀{i Γ Δ a b} (f : Val Γ (a ⇒ b))(v : Val Γ a)(η : Ren Γ Δ) →
            (renval η <$> apply f v) ~⟨ i ⟩~ (apply (renval η f) (renval η v))
  renapply (ne x)    v η = ~refl _
  renapply (lam t ρ) v η = ~later (renbeta t ρ v η)

  renbeta : ∀ {i Γ Δ E a b} (t : Tm (Γ , a) b)(ρ : Env Δ Γ) (v : Val Δ a) →
          (η : Ren Δ E) →
          (renval η ∞<$> (beta t ρ v)) ∞~⟨ i ⟩~ beta t (renenv η ρ) (renval η v)
  ~force (renbeta t ρ v η) = reneval t (ρ , v) η

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
  rennereadback : ∀{i Γ Δ a}(η : Ren Γ Δ)(t : Ne Val Γ a) →
                (rennen η <$> nereadback t) ~⟨ i ⟩~ (nereadback (rennev η t))
  rennereadback η (var x) = ~now _
  rennereadback η (app t u) =
    proof
    ((nereadback t >>=
      (λ t₁ → readback u >>= (λ n → now (app t₁ n))))
                                   >>= (λ x′ → now (rennen η x′)))
    ~⟨ bind-assoc (nereadback t) ⟩
    (nereadback t >>= (λ x →
      (readback u >>= (λ n → now (app x n)))
                                   >>= (λ x′ → now (rennen η x′))))
    ~⟨ bind-cong-r (nereadback t) (λ x → bind-assoc (readback u)) ⟩
    (nereadback t >>= (λ x →
       readback u >>= (λ y → now (app x y) >>= (λ x′ → now (rennen η x′)))))
    ≡⟨⟩
    (nereadback t >>=
      (λ x → (readback u >>= (λ y → now (app (rennen η x) (rennf η y))))))
    ≡⟨⟩
    (nereadback t >>=
           (λ x → (readback u >>= (λ x′ → now (rennf η x′) >>=
               (λ n → now (app (rennen η x) n))))))
    ~⟨ bind-cong-r (nereadback t) (λ x → ~sym (bind-assoc (readback u))) ⟩
    (nereadback t >>=
           (λ x → ((readback u >>= (λ x′ → now (rennf η x′))) >>=
               (λ n → now (app (rennen η x) n)))))
    ≡⟨⟩
    (nereadback t >>= (λ x → now (rennen η x) >>=
      (λ t₁ → ((readback u >>= (λ x′ → now (rennf η x′))) >>=
          (λ n → now (app t₁ n))))))
    ~⟨ ~sym (bind-assoc (nereadback t)) ⟩
    ((nereadback t >>= (λ x′ → now (rennen η x′))) >>=
      (λ t₁ → ((readback u >>= (λ x′ → now (rennf η x′))) >>=
          (λ n → now (app t₁ n)))))
    ≡⟨⟩
    (rennen η <$> nereadback t >>=
       (λ t₁ → rennf η <$> readback u >>= (λ n → now (app t₁ n))))
    ~⟨ bind-cong-r (rennen η <$> nereadback t)
                   (λ x → bind-cong-l (renreadback _ η u)
                                      (λ x → _)) ⟩
    (rennen η <$> nereadback t >>=
       (λ t₁ → readback (renval η u) >>= (λ n → now (app t₁ n))))
    ~⟨  bind-cong-l (rennereadback η t) (λ x → _) ⟩
    (nereadback (rennev η t) >>=
       (λ t₁ → readback (renval η u) >>= (λ n → now (app t₁ n))))
    ∎
    where open ~-Reasoning

  renreadback   : ∀{i Γ Δ} a (η : Ren Γ Δ)(v : Val Γ a) →
                (rennf η <$> readback v) ~⟨ i ⟩~ (readback (renval η v))
  renreadback ★ η (ne w) =
    proof
      rennf η  <$>  (ne  <$> nereadback w)   ~⟨ map-compose (nereadback w) ⟩
      (rennf η ∘ ne)     <$> nereadback w     ≡⟨⟩
      (Nf.ne ∘ rennen η) <$> nereadback w     ~⟨ ~sym (map-compose (nereadback w)) ⟩
      ne <$>  (rennen η  <$> nereadback w)    ~⟨ map-cong ne (rennereadback η w) ⟩
      ne <$>   nereadback (rennev η w)
    ∎
    where open ~-Reasoning
  renreadback (a ⇒ b) η f      = ~later (
    proof
    (eta f ∞>>= (λ a₁ → now (lam a₁))) ∞>>= (λ x' → now (rennf η x'))
    ∞~⟨ ∞bind-assoc (eta f) ⟩
    (eta f ∞>>= λ a₁ → now (lam a₁) >>= λ x' → now (rennf η x'))
    ≡⟨⟩
    (eta f ∞>>= (λ a₁ → now (lam (rennf (wk η) a₁))))
    ≡⟨⟩
    (eta f ∞>>= λ a₁ → now (rennf (wk η) a₁) >>= λ a₁ → now (lam a₁))
    ∞~⟨ ∞~sym (∞bind-assoc (eta f)) ⟩
    (eta f ∞>>= (λ a₁ → now (rennf (wk η) a₁))) ∞>>= (λ a₁ → now (lam a₁))
    ∞~⟨ ∞bind-cong-l (reneta η f) (λ a → now (lam a)) ⟩
    eta (renval η f) ∞>>= (λ a₁ → now (lam a₁))
    ∎)
    where open ∞~-Reasoning

  reneta  : ∀{i Γ Δ a b} (η : Ren Γ Δ)(v : Val Γ (a ⇒ b)) →
          (rennf (wk η) ∞<$> eta v) ∞~⟨ i ⟩~ (eta (renval η v))
  ~force (reneta η f) =
    proof
    ((apply (weakVal f) (ne (var zero)) >>= readback)
      >>= (λ a → now (rennf (wk η) a)))
    ~⟨ bind-assoc (apply (weakVal f) (ne (var zero))) ⟩
    (apply (weakVal f) (ne (var zero)) >>=
         (λ z → readback z >>= (λ x' → now (rennf (wk η) x'))))
    ~⟨ bind-cong-r (apply (weakVal f) (ne (var zero)))
                   (λ x → renreadback _ (wk η) x) ⟩
    (apply (weakVal f) (ne (var zero)) >>=
      (λ x' → readback (renval (wk η) x')))
    ≡⟨⟩
    (apply (weakVal f) (ne (var zero)) >>=
          (λ x' → now (renval (wk η) x') >>= readback))
    ~⟨ ~sym (bind-assoc (apply (weakVal f) (ne (var zero))))  ⟩
    ((apply (weakVal f) (ne (var zero)) >>=
          (λ x' → now (renval (wk η) x')))
         >>= readback)
    ~⟨ bind-cong-l (renapply (weakVal f) (ne (var zero)) (wk η)) readback ⟩
    (apply (renval (wk η) (renval suc f)) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ f₁ → apply f₁ (ne (var zero)) >>= readback)
             (renvalcomp (wk η) suc f) ⟩
    (apply (renval (suc ∘ η) f) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ (η₁ : Ren _ _) → apply (renval (suc ∘ η₁) f) (ne (var zero)) >>= readback)
            refl  ⟩ -- is this step needed?
    (apply (renval (suc ∘ η) f) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ f₁ → apply f₁ (ne (var zero)) >>= readback)
            (sym (renvalcomp suc η f)) ⟩
    (apply (weakVal (renval η f)) (ne (var zero)) >>= readback)
    ∎
    where open ~-Reasoning

mutual
  V⟦_⟧_ : ∀{Γ}(a : Ty) → Val Γ a → Set
  V⟦ ★ ⟧ ne t = nereadback t ⇓
  V⟦_⟧_ {Γ = Γ} (a ⇒ b) f = ∀{Δ}(ρ : Ren Γ Δ)(u : Val Δ a)
    (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (apply (renval ρ f) u)

  C⟦_⟧_ : ∀{Γ}(a : Ty) → Delay ∞ (Val Γ a) → Set
  C⟦ a ⟧ x = ∃ λ v → x ⇓ v × V⟦ a ⟧ v

E⟦_⟧_ : ∀{Δ}(Γ : Cxt) → Env Δ Γ → Set
E⟦ ε ⟧     ε       = ⊤
E⟦ Γ , a ⟧ (ρ , v) = E⟦ Γ ⟧ ρ × V⟦ a ⟧ v


rennereadback⇓ : ∀{Γ Δ a}(η : Ren Γ Δ)(t : Ne Val Γ a){n : Ne Nf Γ a} →
              nereadback t ⇓ n → nereadback (rennev η t) ⇓ rennen η n
rennereadback⇓ η t {n} p = subst~⇓ (map⇓ (rennen η) p) (rennereadback η t)

renV⟦⟧ : ∀{Δ Δ′} a (η : Ren Δ Δ′)(v : Val Δ a)(⟦v⟧ : V⟦ a ⟧ v) → V⟦ a ⟧ (renval η v)
renV⟦⟧ ★       η (ne t) (n , p)        = rennen η n , rennereadback⇓ η t p
renV⟦⟧ (a ⇒ b) η v      p       ρ u u⇓ =
  let v′ , (p′ , p′′) = p (ρ ∘ η) u u⇓ in
      v′ , (subst (λ X → apply X u ⇓ fst (p (ρ ∘ η) u u⇓))
                 ((sym (renvalcomp ρ η v)))
                 p′
         , p′′)


renE⟦⟧ : ∀{Γ Δ Δ′} (η : Ren Δ Δ′) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) → E⟦ Γ ⟧ (renenv η ρ)
renE⟦⟧ η ε       θ        = _
renE⟦⟧ η (ρ , v) (θ , ⟦v⟧) = renE⟦⟧ η ρ θ , renV⟦⟧ _ η v ⟦v⟧


⟦var⟧ : ∀{Δ Γ a} (x : Var Γ a) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
            C⟦ a ⟧ (now (lookup x ρ))
⟦var⟧ zero   (_ , v) (_ , v⇓) = v , (now⇓ , v⇓)
⟦var⟧(suc x) (ρ , _) (θ , _ ) = ⟦var⟧ x ρ θ


sound-β : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (u : Val Δ a) →
          C⟦ b ⟧ (eval t  (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)
sound-β t ρ u (v , (v⇓ , ⟦v⟧)) = v , (later⇓ v⇓ , ⟦v⟧)


⟦abs⟧ : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
  (∀{Δ′}(η : Ren Δ Δ′)(u : Val Δ′ a)(u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (eval t (renenv η ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))
⟦abs⟧ t ρ θ ih = lam t ρ , (now⇓ , (λ η u p → sound-β t (renenv η ρ) u (ih η u p)))


⟦app⟧ : ∀ {Δ a b} {f? : Delay _ (Val Δ (a ⇒ b))} {u? : Delay _ (Val Δ a)} →
          C⟦ a ⇒ b ⟧ f? → C⟦ a ⟧ u? → C⟦ b ⟧ (f? >>= λ f → u? >>= apply f)
⟦app⟧ {u? = u?} (f , (f⇓ , ⟦f⟧)) (u , (u⇓ , ⟦u⟧)) =
  let v , (v⇓ , ⟦v⟧) = ⟦f⟧ renId u ⟦u⟧
      v⇓′          = bind⇓ (λ f′ → u? >>= apply f′)
                    f⇓
                    (bind⇓ (apply f)
                          u⇓
                          (subst (λ X → apply X u ⇓ v)
                                 (renvalid f)
                                 v⇓))
  in  v , (v⇓′ , ⟦v⟧)


term : ∀ {Δ Γ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) → C⟦ a ⟧ (eval t ρ)
term (var x)   ρ θ = ⟦var⟧ x ρ θ
term (abs t)   ρ θ = ⟦abs⟧ t ρ θ (λ η u p →
  term t (renenv η ρ , u) (renE⟦⟧ η ρ θ , p))
term (app t u) ρ θ = ⟦app⟧ (term t ρ θ) (term u ρ θ)


mutual
  reify : ∀{Γ} a (v : Val Γ a) → V⟦ a ⟧ v → readback v ⇓
  reify ★        (ne _) (m , ⇓m) = ne m , map⇓ ne ⇓m
  reify (a ⇒ b)  f      ⟦f⟧      =
    let u           = ne (var zero)
        ⟦u⟧          = reflect a (var zero) (var zero , now⇓)
        v , (v⇓ , ⟦v⟧) = ⟦f⟧ suc u ⟦u⟧
        n , ⇓n = reify b v ⟦v⟧
        ⇓λn    = later⇓ (bind⇓ (λ x → now (lam x))
                               (bind⇓ readback v⇓ ⇓n)
                               now⇓)
    in  lam n , ⇓λn

  reflect : ∀{Γ} a (w : Ne Val Γ a) → nereadback w ⇓ → V⟦ a ⟧ (ne w)
  reflect ★ w w⇓ = w⇓
  reflect (a ⇒ b) w (m , w⇓m) η u ⟦u⟧ =
    let n , ⇓n = reify a u ⟦u⟧
        m′      = rennen η m
        ⇓m     = rennereadback⇓ η w w⇓m
        wu     = app (rennev η w) u
        ⟦wu⟧   = reflect b wu (app m′ n ,
                   bind⇓ (λ m → app m <$> readback u)
                        ⇓m
                        (bind⇓ (λ n → now (app m′ n)) ⇓n now⇓))
    in  ne wu , (now⇓ , ⟦wu⟧)


var↑ : ∀{Γ a}(x : Var Γ a) → V⟦ a ⟧ ne (var x)
var↑ x = reflect _ (var x) (var x , now⇓)


⟦ide⟧ : ∀ Γ → E⟦ Γ ⟧ (ide Γ)
⟦ide⟧ ε       = _
⟦ide⟧ (Γ , a) = renE⟦⟧ suc (ide Γ) (⟦ide⟧ Γ) , var↑ zero

nf : ∀{Γ a}(t : Tm Γ a) → Delay ∞ (Nf Γ a)
nf t = eval t (ide _) >>= readback

normalize : ∀ Γ a (t : Tm Γ a) → ∃ λ n → nf t ⇓ n
normalize Γ a t = let v , (v⇓ , ⟦v⟧) = term t (ide Γ) (⟦ide⟧ Γ)
                      n , ⇓n      = reify a v ⟦v⟧
                  in  n , bind⇓ readback v⇓ ⇓n

