module Evaluation where

open import Library
open import Delay
open import Syntax
open import RenamingAndSubstitution

-- Identity environment.

ide : ∀ Γ → Env ∞ Γ Γ
ide ε       = ε
ide (Γ , a) = renenv (wkr renId) (ide Γ) , ne (var zero)

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
  force (∞apply w v) = apply (force w) v

  beta : ∀ {i Γ a b} (t : Tm (Γ , a) b)
    {Δ : Cxt} (ρ : Env i Δ Γ) (v : Val i Δ a) → ∞Val i Δ b
  force (beta t ρ v) = eval t (ρ , v)

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
  ≈force (∞apply-cong p q) = apply-cong (≈force p) q

  beta-cong : ∀ {i Γ a b} (t : Tm (Γ , a) b)
    {Δ : Cxt}{ρ ρ' : Env ∞ Δ Γ}{v v' : Val ∞ Δ a} →
    Env∋ ρ ≈⟨ i ⟩≈ ρ' → Val∋ v ≈⟨ i ⟩≈ v' →
    ∞Val∋ beta t ρ v ≈⟨ i ⟩≈ beta t ρ' v'
  ≈force (beta-cong t p q) = eval-cong t (p ≈, q)

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

  ∞renapply  : ∀{i Γ Δ a b}(f : ∞Val ∞ Γ (a ⇒ b))(v : Val ∞ Γ a)(η : Ren Δ Γ) →
     ∞Val∋ (∞renval η $ ∞apply f v) ≈⟨ i ⟩≈ (∞apply (∞renval η f) (renval η v))
  ≈force (∞renapply f v η) = renapply (force f) v η

  renbeta : ∀ {i Γ Δ E a b} (t : Tm (Γ , a) b)(ρ : Env ∞ Δ Γ) (v : Val ∞ Δ a) →
    (η : Ren E Δ) →
     ∞Val∋ ∞renval η $ (beta t ρ v) ≈⟨ i ⟩≈ (beta t (renenv η ρ) (renval η v))
  ≈force (renbeta t ρ v η) = reneval t (ρ , v) η

mutual
  readback : ∀{i Γ a} → Val i Γ a → Delay i (Nf Γ a)
  readback {a = ★} (ne w) = ne  <$> nereadback w
  readback {a = ★} (later w) = later (∞readback w)
  readback {a = _ ⇒ _} v = later (abs ∞<$> eta v)

  ∞readback : ∀{i Γ a} → ∞Val i Γ a → ∞Delay i (Nf Γ a)
  force (∞readback w) = readback (force w)

  eta : ∀{i Γ a b} → Val i Γ (a ⇒ b) → ∞Delay i (Nf (Γ , a) b)
  force (eta v) = readback (apply (weakVal v) (ne (var zero)))

  nereadback : ∀{i Γ a} → NeVal i Γ a → Delay i (Ne Γ a)
  nereadback (var x)   = now (var x)
  nereadback (app w v) =
--    nereadback w >>= λ m → app m <$> readback v
      app <$> nereadback w <*> readback v


mutual
  readback-cong : ∀{i Γ} a {v v' : Val ∞ Γ a} → Val∋ v ≈⟨ i ⟩≈ v' →
                  readback v ≈⟨ i ⟩≈ readback v'
  readback-cong ★       (≈ne p)    = map-cong ne (nereadback-cong ★ p)
  readback-cong ★       (≈later p) = ≈later (∞readback-cong _ p)
  readback-cong (a ⇒ b) p          =
    ≈later (∞map-cong abs (eta-cong p))

  ∞readback-cong : ∀{i Γ} a {v v' : ∞Val ∞ Γ a} → ∞Val∋ v ≈⟨ i ⟩≈ v' →
                  ∞readback v ∞≈⟨ i ⟩≈ ∞readback v'
  ≈force (∞readback-cong a p) = readback-cong a (≈force p)

  nereadback-cong : ∀{i Γ} a {n n' : NeVal ∞ Γ a} → NeVal∋ n ≈⟨ i ⟩≈ n' →
                  nereadback n ≈⟨ i ⟩≈ nereadback n'
  nereadback-cong a ≈var       = ≈now _ _ refl
  nereadback-cong a (≈app p q) =
    *-cong (map-cong app (nereadback-cong _ p)) (readback-cong _ q)

  eta-cong : ∀{i Γ a b}{v v' : Val ∞ Γ (a ⇒ b)} →
             Val∋ v ≈⟨ i ⟩≈ v' → eta v ∞≈⟨ i ⟩≈ eta v'
  ≈force (eta-cong p) =
    readback-cong _ (apply-cong (renval-cong (wkr renId) p) (≈ne ≈var))

-- these proofs could surely be shortened, readback-cong would help

mutual
  rennereadback : ∀{i Γ Δ a}(η : Ren Δ Γ)(t : NeVal ∞ Γ a) →
                (rennen η <$> nereadback t) ≈⟨ i ⟩≈ (nereadback (rennev η t))
  rennereadback η (var x) = ≈now _ _ refl
  rennereadback η (app t u) = proof
    rennen η <$> (app <$> nereadback t <*> readback u)
    ≈⟨ lifta2lem1 app (rennen η) (nereadback t) (readback u)  ⟩
    (λ m n → rennen η (app m n)) <$> nereadback t <*> readback u
    ≡⟨⟩
    (λ m n → app (rennen η m) (rennf η n)) <$> nereadback t <*> readback u
    ≈⟨ lifta2lem2 app (rennen η) (rennf η) (nereadback t) (readback u) ⟩
    app <$> (rennen η <$> nereadback t) <*> (rennf η <$> readback u)
    ≈⟨ *-cong (map-cong app (rennereadback η t)) (renreadback _ η u) ⟩
    (app <$> nereadback (rennev η t) <*> readback (renval η u))
    ∎
    where open ≈-Reasoning

  renreadback   : ∀{i Γ Δ} a (η : Ren Δ Γ)(v : Val ∞ Γ a) →
                (rennf η <$> readback v) ≈⟨ i ⟩≈ (readback (renval η v))
  renreadback ★ η (ne w) =
    proof
      rennf η  <$>  (ne  <$> nereadback w)
      ≈⟨ map-compose (nereadback w) ⟩
      (rennf η ∘ ne)     <$> nereadback w
      ≡⟨⟩
      (Nf.ne ∘ rennen η) <$> nereadback w
      ≈⟨ ≈sym (map-compose (nereadback w)) ⟩
      ne <$>  (rennen η  <$> nereadback w)
      ≈⟨ map-cong ne (rennereadback η w) ⟩
      ne <$>   nereadback (rennev η w)
    ∎
    where open ≈-Reasoning
  renreadback ★ η (later p) = ≈later (∞renreadback ★ η p)
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

  ∞renreadback   : ∀{i Γ Δ} a (η : Ren Δ Γ)(v : ∞Val ∞ Γ a) →
                (rennf η ∞<$> ∞readback v) ∞≈⟨ i ⟩≈ (∞readback (∞renval η v))
  ≈force (∞renreadback a η v) = renreadback a η (force v)

  reneta  : ∀{i Γ Δ a b} (η : Ren Δ Γ)(v : Val ∞ Γ (a ⇒ b)) →
          (rennf (liftr η) ∞<$> eta v) ∞≈⟨ i ⟩≈ (eta (renval η v))
  ≈force (reneta η f) = proof
    readback (apply (renval (wkr renId) f) (ne (var zero))) Bind.>>=
      (λ a → now (rennf (wkr η , zero) a))
    ≈⟨ renreadback _ (liftr η) (apply (renval (wkr renId) f) (ne (var zero))) ⟩
    readback (renval (wkr η , zero)
                     (apply (renval (wkr renId) f) (ne (var zero))))
    ≈⟨ readback-cong _ (renapply (renval (wkr renId) f) (ne (var zero))
                      (liftr η) ) ⟩
    readback (apply (renval (liftr η) (renval (wkr renId) f)) (ne (var zero)))
    ≈⟨  readback-cong _ (apply-cong (renvalcomp (liftr η) (wkr renId) f)
                                    (≈reflVal _))  ⟩
    readback (apply (renval (renComp (liftr η) (wkr renId)) f) (ne (var zero)))
    ≡⟨ cong (λ η → readback (apply (renval η f) (ne (var zero))))
            (lemrr (wkr η) zero renId)  ⟩
    readback (apply (renval (renComp (wkr η) renId) f) (ne (var zero)))
    ≡⟨ cong (λ η → readback (apply (renval η f) (ne (var zero))))
            (wkrcomp η renId) ⟩
    readback (apply (renval (wkr (renComp η renId)) f) (ne (var zero)))
    ≡⟨ cong (λ η → readback (apply (renval (wkr η) f) (ne (var zero))))
            (trans (ridr η) (sym $ lidr η) ) ⟩
    readback (apply (renval (wkr (renComp renId η)) f) (ne (var zero)))
    ≡⟨ cong (λ η → readback (apply (renval η f) (ne (var zero))))
            (sym (wkrcomp renId η)) ⟩
    readback (apply (renval (renComp (wkr renId) η) f) (ne (var zero)))
    ≈⟨ readback-cong _ (apply-cong (≈symVal (renvalcomp (wkr renId) η f))
                                 (≈reflVal _)) ⟩
    readback (apply (renval (wkr renId) (renval η f)) (ne (var zero)))
    ∎ where open ≈-Reasoning

nf : ∀{Γ a}(t : Tm Γ a) → Delay ∞ (Nf Γ a)
nf t = readback (eval t (ide _))

-- this stuff is for the substitution lemma primarily
evalS : ∀{Γ Δ Δ′} → Sub Δ Γ → Env ∞ Δ′ Δ → Env ∞ Δ′ Γ
evalS ε       ρ = ε
evalS (σ , v) ρ = evalS σ ρ , eval v ρ

renevalS : ∀ {i Γ Γ' Δ Δ′} (σ : Sub Γ Γ') (ρ : Env ∞ Δ Γ) (η : Ren Δ′ Δ) →
    Env∋ (renenv η $ evalS σ ρ) ≈⟨ i ⟩≈ (evalS σ $ renenv η ρ)
renevalS ε       ρ η = ≈ε
renevalS (σ , t) ρ η = renevalS σ ρ η ≈, reneval t ρ η

lookupR : ∀{Γ Γ' Δ}(σ : Ren Γ' Γ)(ρ : Env ∞ Δ Γ') → Env ∞ Δ Γ
lookupR ε       ρ = ε
lookupR (σ , x) ρ = lookupR σ ρ , lookup x ρ

renlookupR : ∀{Γ Γ' Δ Δ'}(η : Ren Δ' Δ)(σ : Ren Γ' Γ)(ρ : Env ∞ Δ Γ') →
             Env∋ renenv η (lookupR σ ρ) ≈⟨ ∞ ⟩≈ lookupR σ (renenv η ρ)
renlookupR η ε       ρ = ≈ε
renlookupR η (σ , x) ρ = renlookupR η σ ρ ≈, lookup≤ x ρ η

lookupRwkr : ∀{Γ Γ' Δ a}(u : Val ∞ Δ a)(σ : Ren Γ' Γ)(ρ : Env ∞ Δ Γ') →
      Env∋  lookupR σ ρ ≈⟨ ∞ ⟩≈ lookupR (wkr σ) (ρ , u)
lookupRwkr u ε       ρ = ≈ε
lookupRwkr u (σ , x) ρ = (lookupRwkr u σ ρ) ≈, ≈reflVal (lookup x ρ)

lookupRrenId : ∀{Γ Δ}(ρ : Env ∞ Δ Γ) →
      Env∋  lookupR renId ρ ≈⟨ ∞ ⟩≈ ρ
lookupRrenId ε       = ≈ε
lookupRrenId (ρ , v) =
  ≈transEnv (≈symEnv (lookupRwkr v renId ρ)) (lookupRrenId ρ) ≈, ≈reflVal v

lookuplookr : ∀{Γ Γ' Δ a}(ρ : Env ∞ Δ Γ')(σ : Ren Γ' Γ)(x : Var Γ a) →
              Val∋ lookup (lookr σ x) ρ ≈⟨ ∞ ⟩≈ lookup x (lookupR σ ρ)
lookuplookr ρ (σ , y) zero    = ≈reflVal (lookup y ρ)
lookuplookr ρ (σ , y) (suc x) = lookuplookr ρ σ x
