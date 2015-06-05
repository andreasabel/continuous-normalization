{-# OPTIONS --copatterns --sized-types #-}

module Evaluation where

open import Library
open import Delay
open import Syntax
open import RenamingAndSubstitution

-- Identity environment.

-- ide : ∀ Γ → Env Γ Γ
-- ide ε = ε
-- ide (Γ , a) = renenv (wkr renId) (ide Γ) , ne (var zero)

-- Looking up in an environment.

lookup : ∀ {i Γ Δ a} → Var Γ a → Env i Δ Γ → Val i Δ a
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

lookup≤ : ∀ {Γ Δ Δ' a} (x : Var Γ a) (ρ : Env ∞ Δ Γ) (η : Ren Δ' Δ) →
  Val∋ renval η (lookup x ρ) ≈ lookup x (renenv η ρ)
lookup≤ zero    (ρ , v) η = ≈reflVal (renval η v)
lookup≤ (suc x) (ρ , v) η = lookup≤ x ρ η

-- Weakening a value to an extended context.

weakVal : ∀ {i Δ a c} → Val i Δ c → Val i (Δ , a) c
weakVal = renval (wkr renId)

mutual
  eval : ∀{i Γ Δ a} → Tm Γ a → Env i Δ Γ → Val i Δ a
  eval (var x)   ρ = lookup x ρ
  eval (abs t)   ρ = lam t ρ
  eval (app t u) ρ = apply (eval t ρ) (eval u ρ)

  apply : ∀ {i Δ a b} → Val i Δ (a ⇒ b) → Val i Δ a → Val i Δ b
  apply (ne w)    v = ne (app w v)
  apply (lam t ρ) v = later (beta t ρ v)
  apply (later w) v = later (∞apply w v)

  ∞apply : ∀ {i Δ a b} → ∞Val i Δ (a ⇒ b) → Val i Δ a → ∞Val i Δ b
  ∞Val.force (∞apply w v) = apply (∞Val.force w) v

  beta : ∀ {i Γ a b} (t : Tm (Γ , a) b)
    {Δ : Cxt} (ρ : Env i Δ Γ) (v : Val i Δ a) → ∞Val i Δ b
  ∞Val.force (beta t ρ v) = eval t (ρ , v)

-- apply-cong
mutual 
  eval-cong : ∀{i Γ Δ a}(t : Tm Γ a){ρ ρ' : Env ∞ Δ Γ} → Env∋ ρ ≈⟨ i ⟩≈ ρ' → 
         Val∋ eval t ρ ≈⟨ i ⟩≈ eval t ρ'
  eval-cong (var zero)    (p ≈, q) = q
  eval-cong (var (suc x)) (p ≈, q) = eval-cong (var x) p
  eval-cong (abs t)   p = ≈lam p
  eval-cong (app t u) p = apply-cong (eval-cong t p) (eval-cong u p)

  apply-cong : ∀ {i Δ a b}{f f' : Val ∞ Δ (a ⇒ b)}{v v' : Val ∞ Δ a} →
               Val∋ f ≈⟨ i ⟩≈ f' → Val∋ v ≈⟨ i ⟩≈ v' → 
               Val∋ apply f v ≈⟨ i ⟩≈ apply f' v'
  apply-cong (≈lam p)    q = ≈later (beta-cong _ p q)
  apply-cong (≈ne p)     q = ≈ne (≈app p q)
  apply-cong (≈later p) q = ≈later (∞apply-cong p q)             

  ∞apply-cong : ∀ {i Δ a b}{f f' : ∞Val ∞ Δ (a ⇒ b)}{v v' : Val ∞ Δ a} →
               ∞Val∋ f ≈⟨ i ⟩≈ f' → Val∋ v ≈⟨ i ⟩≈ v' → 
               ∞Val∋ ∞apply f v ≈⟨ i ⟩≈ ∞apply f' v'
  ∞Val∋_≈⟨_⟩≈_.≈force (∞apply-cong p q) =
    apply-cong (∞Val∋_≈⟨_⟩≈_.≈force p) q

  beta-cong : ∀ {i Γ a b} (t : Tm (Γ , a) b)
    {Δ : Cxt}{ρ ρ' : Env ∞ Δ Γ}{v v' : Val ∞ Δ a} → 
    Env∋ ρ ≈⟨ i ⟩≈ ρ' → Val∋ v ≈⟨ i ⟩≈ v' →
    ∞Val∋ beta t ρ v ≈⟨ i ⟩≈ beta t ρ' v'
  ∞Val∋_≈⟨_⟩≈_.≈force (beta-cong t p q) = eval-cong t (p ≈, q)
  
mutual
  reneval : ∀ {i Γ Δ Δ′ a} (t : Tm Γ a) (ρ : Env ∞ Δ Γ) (η : Ren Δ′ Δ) →
    Val∋ (renval η $ eval t ρ) ≈⟨ i ⟩≈ (eval t $ renenv η ρ)
  reneval (var x)   ρ η = lookup≤ x ρ η
  reneval (abs t)   ρ η = ≈lam (≈reflEnv (renenv η ρ))
  reneval (app t u) ρ η = proof
    renval η (apply (eval t ρ) (eval u ρ))
    ≈⟨ renapply (eval t ρ) (eval u ρ) η ⟩
    apply (renval η (eval t ρ)) (renval η (eval u ρ))
    ≈⟨ apply-cong (reneval t ρ η) (reneval u ρ η) ⟩
    apply (eval t (renenv η ρ)) (eval u (renenv η ρ))
    ∎ where open ≈Val-Reasoning

  renapply  : ∀{i Γ Δ a b} (f : Val ∞ Γ (a ⇒ b))(v : Val ∞ Γ a)(η : Ren Δ Γ) →
    Val∋ (renval η $ apply f v) ≈⟨ i ⟩≈ (apply (renval η f) (renval η v))
  renapply (ne x)    v η = ≈reflVal _
  renapply (lam t ρ) v η = ≈later (renbeta t ρ v η)
  renapply (later p) v η = ≈later (∞renapply p v η)

  ∞renapply  : ∀{i Γ Δ a b} (f : ∞Val ∞ Γ (a ⇒ b))(v : Val ∞ Γ a)(η : Ren Δ Γ) →
     ∞Val∋ (∞renval η $ ∞apply f v) ≈⟨ i ⟩≈ (∞apply (∞renval η f) (renval η v))
  ∞Val∋_≈⟨_⟩≈_.≈force (∞renapply f v η) = renapply (∞Val.force f) v η

  renbeta : ∀ {i Γ Δ E a b} (t : Tm (Γ , a) b)(ρ : Env ∞ Δ Γ) (v : Val ∞ Δ a) →
    (η : Ren E Δ) →
     ∞Val∋ ∞renval η $ (beta t ρ v) ≈⟨ i ⟩≈ (beta t (renenv η ρ) (renval η v))
  ∞Val∋_≈⟨_⟩≈_.≈force (renbeta t ρ v η) = reneval t (ρ , v) η

mutual
  readback : ∀{i Γ a} → Val i Γ a → Delay i (Nf Γ a)
  readback {a = ★} (ne w) = ne  <$> nereadback w
  readback {a = ★} (later w) = later (∞readback w)
  readback {a = _ ⇒ _} v = abs <$> later (eta v)

  ∞readback : ∀{i Γ a} → ∞Val i Γ a → ∞Delay i (Nf Γ a)
  ∞Delay.force (∞readback w) = readback (∞Val.force w)

  eta : ∀{i Γ a b} → Val i Γ (a ⇒ b) → ∞Delay i (Nf (Γ , a) b)
  force (eta v) = readback (apply (weakVal v) (ne (var zero)))

  nereadback : ∀{i Γ a} → NeVal i Γ a → Delay i (Ne Γ a)
  nereadback (var x)   = now (var x)
  nereadback (app w v) =
    nereadback w >>= λ m → app m <$> readback v

{-
mutual
  rennereadback : ∀{i Γ Δ a}(η : Ren Δ Γ)(t : NeVal Γ a) →
                (rennen η <$> nereadback t) ≈⟨ i ⟩≈ (nereadback (rennev η t))
  rennereadback η (var x) = ≈now _ _ refl
  rennereadback η (app t u) =
    proof
    ((nereadback t >>=
      (λ t₁ → readback u >>= (λ n → now (app t₁ n))))
                                   >>= (λ x′ → now (rennen η x′)))
    ≈⟨ bind-assoc (nereadback t) ⟩
    (nereadback t >>= (λ x →
      (readback u >>= (λ n → now (app x n)))
                                   >>= (λ x′ → now (rennen η x′))))
    ≈⟨ bind-cong-r (nereadback t) (λ x → bind-assoc (readback u)) ⟩
    (nereadback t >>= (λ x →
       readback u >>= (λ y → now (app x y) >>= (λ x′ → now (rennen η x′)))))
    ≡⟨⟩
    (nereadback t >>=
      (λ x → (readback u >>= (λ y → now (app (rennen η x) (rennf η y))))))
    ≡⟨⟩
    (nereadback t >>=
           (λ x → (readback u >>= (λ x′ → now (rennf η x′) >>=
               (λ n → now (app (rennen η x) n))))))
    ≈⟨ bind-cong-r (nereadback t) (λ x → ≈sym (bind-assoc (readback u))) ⟩
    (nereadback t >>=
           (λ x → ((readback u >>= (λ x′ → now (rennf η x′))) >>=
               (λ n → now (app (rennen η x) n)))))
    ≡⟨⟩
    (nereadback t >>= (λ x → now (rennen η x) >>=
      (λ t₁ → ((readback u >>= (λ x′ → now (rennf η x′))) >>=
          (λ n → now (app t₁ n))))))
    ≈⟨ ≈sym (bind-assoc (nereadback t)) ⟩
    ((nereadback t >>= (λ x′ → now (rennen η x′))) >>=
      (λ t₁ → ((readback u >>= (λ x′ → now (rennf η x′))) >>=
          (λ n → now (app t₁ n)))))
    ≡⟨⟩
    (rennen η <$> nereadback t >>=
       (λ t₁ → rennf η <$> readback u >>= (λ n → now (app t₁ n))))
    ≈⟨ bind-cong-r (rennen η <$> nereadback t)
                   (λ x → bind-cong-l (renreadback _ η u)
                                      (λ x → _)) ⟩
    (rennen η <$> nereadback t >>=
       (λ t₁ → readback (renval η u) >>= (λ n → now (app t₁ n))))
    ≈⟨  bind-cong-l (rennereadback η t) (λ x → _) ⟩
    (nereadback (rennev η t) >>=
       (λ t₁ → readback (renval η u) >>= (λ n → now (app t₁ n))))
    ∎
    where open ≈-Reasoning

  renreadback   : ∀{i Γ Δ} a (η : Ren Δ Γ)(v : Val Γ a) →
                (rennf η <$> readback v) ≈⟨ i ⟩≈ (readback (renval η v))
  renreadback ★ η (ne w) =
    proof
      rennf η  <$>  (ne  <$> nereadback w)   ≈⟨ map-compose (nereadback w) ⟩
      (rennf η ∘ ne)     <$> nereadback w     ≡⟨⟩
      (Nf.ne ∘ rennen η) <$> nereadback w     ≈⟨ ≈sym (map-compose (nereadback w)) ⟩
      ne <$>  (rennen η  <$> nereadback w)    ≈⟨ map-cong ne (rennereadback η w) ⟩
      ne <$>   nereadback (rennev η w)
    ∎
    where open ≈-Reasoning
  renreadback (a ⇒ b) η f      = ≈later (
    proof
    (eta f ∞>>= (λ a₁ → now (abs a₁))) ∞>>= (λ x' → now (rennf η x'))
    ∞≈⟨ ∞bind-assoc (eta f) ⟩
    (eta f ∞>>= λ a₁ → now (abs a₁) >>= λ x' → now (rennf η x'))
    ≡⟨⟩
    (eta f ∞>>= (λ a₁ → now (abs (rennf (liftr η) a₁))))
    ≡⟨⟩
    (eta f ∞>>= λ a₁ → now (rennf (liftr η) a₁) >>= λ a₁ → now (abs a₁))
    ∞≈⟨ ∞≈sym (∞bind-assoc (eta f)) ⟩
    (eta f ∞>>= (λ a₁ → now (rennf (liftr η) a₁))) ∞>>= (λ a₁ → now (abs a₁))
    ∞≈⟨ ∞bind-cong-l (reneta η f) (λ a → now (abs a)) ⟩
    eta (renval η f) ∞>>= (λ a₁ → now (abs a₁))
    ∎)
    where open ∞≈-Reasoning


  reneta  : ∀{i Γ Δ a b} (η : Ren Δ Γ)(v : Val Γ (a ⇒ b)) →
          (rennf (liftr η) ∞<$> eta v) ∞≈⟨ i ⟩≈ (eta (renval η v))
  ≈force (reneta η f) =
    proof
    ((apply (weakVal f) (ne (var zero)) >>= readback)
      >>= (λ a → now (rennf (liftr η) a)))
    ≈⟨ bind-assoc (apply (weakVal f) (ne (var zero))) ⟩
    (apply (weakVal f) (ne (var zero)) >>=
         (λ z → readback z >>= (λ x' → now (rennf (liftr η) x'))))
    ≈⟨ bind-cong-r (apply (weakVal f) (ne (var zero)))
                   (λ x → renreadback _ (liftr η) x) ⟩
    (apply (weakVal f) (ne (var zero)) >>=
      (λ x' → readback (renval (liftr η) x')))
    ≡⟨⟩
    (apply (weakVal f) (ne (var zero)) >>=
          (λ x' → now (renval (liftr η) x') >>= readback))
    ≈⟨ ≈sym (bind-assoc (apply (weakVal f) (ne (var zero))))  ⟩
    ((apply (weakVal f) (ne (var zero)) >>=
          (λ x' → now (renval (liftr η) x')))
         >>= readback)
    ≈⟨ bind-cong-l (renapply (weakVal f) (ne (var zero)) (liftr η)) readback ⟩
    (apply (renval (liftr η) (renval (wkr renId) f)) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ f₁ → apply f₁ (ne (var zero)) >>= readback)
             (renvalcomp (liftr η) (wkr renId) f) ⟩
    (apply (renval (renComp (liftr η) (wkr renId)) f) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ xs → apply (renval xs f) (ne (var zero)) >>= readback)
            (lemrr (wkr η) zero renId) ⟩
    (apply (renval (renComp (wkr η) renId) f) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ xs → apply (renval xs f) (ne (var zero)) >>= readback)
            (ridr (wkr η)) ⟩
    (apply (renval (wkr η) f) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ xs → apply (renval xs f) (ne (var zero)) >>= readback)
            (sym $ cong wkr (lidr η)) ⟩
    (apply (renval (wkr (renComp renId η)) f) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ xs → apply (renval xs f) (ne (var zero)) >>= readback)
            (sym $ wkrcomp renId η) ⟩
    (apply (renval (renComp (wkr renId) η) f) (ne (var zero)) >>= readback)
    ≡⟨ cong (λ f₁ → apply f₁ (ne (var zero)) >>= readback)
            (sym (renvalcomp (wkr renId) η f)) ⟩
    (readback =<< apply (weakVal (renval η f)) (ne (var zero))) ∎
          where open ≈-Reasoning

nf : ∀{Γ a}(t : Tm Γ a) → Delay ∞ (Nf Γ a)
nf t = eval t (ide _) >>= readback

-- -}
