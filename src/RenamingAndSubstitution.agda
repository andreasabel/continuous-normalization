module RenamingAndSubstitution where

open import Library -- hiding (_≡_)
open import Syntax

-- Renamings.
-- If  ρ : Ren Δ Γ  and  t : Tm Γ a  then  ren ρ t : Tm Δ a.

Ren : Cxt → Cxt → Set
Ren Δ Γ = ∀ {a} → Var Γ a → Var Δ a

-- The category of renamings.

renId : ∀{Γ} → Ren Γ Γ
renId = idf

renComp : ∀{B Γ Δ} → Ren Δ Γ → Ren Γ B → Ren Δ B
renComp f g = f ∘ g

ConCat : Cat
ConCat = record{
  Obj  = Cxt;
  Hom  = Ren;
  iden = renId;
  comp = flip renComp;
  idl  = iext λ _ → refl;
  idr  = iext λ _ → refl;
  ass  = iext λ _ → refl}

-- Lifting of a renaming.

wk : ∀{Γ Δ σ} → Ren Γ Δ → Ren (Γ , σ) (Δ , σ)
wk f zero     = zero
wk f (suc i) = suc (f i)

wkcong : ∀{Γ Δ σ τ}{f f' : Ren Δ Γ} →
         (∀{σ}(x : Var Γ σ) → f x ≅ f' x) → (x : Var (Γ , τ) σ) →
         wk f x ≅ wk f' x
wkcong p zero    = refl
wkcong p (suc x) = hcong suc (p x)

-- Functoriality of renamings.

wkid : ∀{Γ σ τ}(x : Var (Γ , τ) σ) → wk renId x ≅ renId x
wkid zero    = refl
wkid (suc x) = refl

wkcomp : ∀ {B Γ Δ}(f : Ren Δ Γ)(g : Ren Γ B){σ τ}(x : Var (B , σ) τ) →
            wk (renComp f g) x ≅ renComp (wk f) (wk g) x
wkcomp f g zero     = refl
wkcomp f g (suc i) = refl

-- The renaming action on terms.

ren : ∀{Γ Δ} → Ren Δ Γ → ∀ {σ} → Tm Γ σ → Tm Δ σ
ren f (var x)   = var (f x)
ren f (app t u) = app (ren f t) (ren f u)
ren f (abs t)   = abs (ren (wk f) t)

rencong : ∀{Γ Δ σ}{f f' : Ren Δ Γ} →
          (∀{σ}(x : Var Γ σ) → f x ≅ f' x) → (t : Tm Γ σ) →
          ren f t ≅ ren f' t
rencong p (var x)   = hcong var (p x)
rencong p (abs t)   = hcong abs (rencong (wkcong p) t)
rencong p (app t u) = hcong₂ app (rencong p t) (rencong p u)

open ≅-Reasoning renaming (begin_ to proof_)

-- Functoriality of the renaming action on terms.

renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≅ t
renid (var x)   = refl
renid (app t u) =
  proof
  app (ren renId t) (ren renId u)
  ≅⟨ hcong₂ app (renid t) (renid u) ⟩
  app t u
  ∎
renid (abs t)   =
  proof abs (ren (wk renId) t)
  ≅⟨ hcong abs (rencong wkid t) ⟩
  abs (ren renId t)
  ≅⟨ hcong abs (renid t) ⟩
  abs t
  ∎

rencomp : ∀ {B Γ Δ}(f : Ren Δ Γ)(g : Ren Γ B){σ}(t : Tm B σ) →
            ren (renComp f g) t ≅ (ren f ∘ ren g) t
rencomp f g (var x)   = refl
rencomp f g (app t u) =
  proof
  app (ren (renComp f g) t) (ren (renComp f g) u)
  ≅⟨ hcong₂ app (rencomp f g t) (rencomp f g u) ⟩
  app (ren f (ren g t)) (ren f (ren g u))
  ∎
rencomp f g (abs t)   =
  proof
  abs (ren (wk (renComp f g)) t)
  ≅⟨ hcong abs (rencong (wkcomp f g) t) ⟩
  abs (ren (renComp (wk f) (wk g)) t)
  ≅⟨ hcong abs (rencomp (wk f) (wk g) t) ⟩
  abs (ren (wk f) (ren (wk g) t))
  ∎

-- Renaming of normal forms.

mutual
  rennf : ∀{Γ Δ} → Ren Γ Δ → ∀{a} → Nf Δ a → Nf Γ a
  rennf α (ne t)   = ne (rennen α t)
  rennf α (lam t)  = lam (rennf (wk α) t)

  rennen : ∀{Γ Δ} → Ren Γ Δ → ∀{a} → Ne Δ a → Ne Γ a
  rennen α (var x) = var (α x)
  rennen α (app n x) = app (rennen α n) (rennf α x)

-- Renaming of values.

mutual
  renval : ∀{Γ Δ} → Ren Δ Γ → ∀ {σ} → Val Γ σ → Val Δ σ
  renval f (ne x)    = ne (rennev f x)
  renval f (lam t ρ) = lam t (renenv f ρ)

  renenv : ∀{Γ Δ} → Ren Δ Γ → ∀ {B} → Env Γ B → Env Δ B
  renenv f ε       = ε
  renenv f (e , v) = renenv f e , renval f v

  rennev : ∀{Γ Δ} → Ren Δ Γ → ∀ {σ} → NeVal Γ σ → NeVal Δ σ
  rennev f (var x)   = var (f x)
  rennev f (app t u) = app (rennev f t) (renval f u)

-- Functoriality of the renaming action on values.

mutual
  renvalid : {Γ : Cxt} {σ : Ty} (v : Val Γ σ) → renval renId v ≡ idf v
  renvalid (ne x)    = cong ne (rennevid x)
  renvalid (lam t ρ) = cong (lam t) (renenvid ρ)

  renenvid : {Γ Δ : Cxt}(e : Env Γ Δ) → renenv renId e ≡ idf e
  renenvid ε       = refl
  renenvid (e , v) = cong₂ _,_ (renenvid e) (renvalid v)

  rennevid : {Γ : Cxt} {σ : Ty} (n : NeVal Γ σ) → rennev renId n ≡ idf n
  rennevid (var x)   = refl
  rennevid (app n v) = cong₂ app (rennevid n) (renvalid v)


mutual
  renenvcomp : ∀ {Γ Δ₁ Δ₂ Δ₃} (η : Ren Δ₁ Δ₂) (η' : Ren Δ₂ Δ₃) (ρ : Env Δ₃ Γ) →
           renenv η (renenv η' ρ) ≡ renenv (η ∘ η') ρ
  renenvcomp η η' ε       = refl
  renenvcomp η η' (ρ , v) = cong₂ _,_ (renenvcomp η η' ρ) (renvalcomp η η' v)

  renvalcomp : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Ren Δ₁ Δ₂) (η' : Ren Δ₂ Δ₃) (v : Val Δ₃ a) →
           renval η (renval η' v) ≡ renval (η ∘ η') v
  renvalcomp η η' (ne t) = cong ne (rennevcomp η η' t)
  renvalcomp η η' (lam t ρ) = cong (lam t) (renenvcomp η η' ρ)

  rennevcomp : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Ren Δ₁ Δ₂) (η' : Ren Δ₂ Δ₃) (t : NeVal Δ₃ a) →
           rennev η (rennev η' t) ≡ rennev (η ∘ η') t
  rennevcomp η η' (var x)   = refl
  rennevcomp η η' (app t u) = cong₂ app (rennevcomp η η' t) (renvalcomp η η' u)

-- Substitutions.

Sub : Cxt → Cxt → Set
Sub Δ Γ = ∀{σ} → Var Γ σ → Tm Δ σ

-- Lifting a substitution under a binder.

lift'' : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ , σ) (Δ , σ)
lift'' f zero     = var zero
lift'' f (suc x) = ren suc (f x)

liftcong : ∀{Γ Δ σ τ}{f f' : Sub Δ Γ} →
         (∀{σ}(x : Var Γ σ) → f x ≅ f' x) → (x : Var (Γ , τ) σ) →
         lift'' f x ≅ lift'' f' x
liftcong p zero    = refl
liftcong p (suc x) = hcong (ren suc) (p x) -- doesn't rely on rencong

-- Substitution action on terms.

sub : ∀{Γ Δ} → Sub Δ Γ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x)   = f x
sub f (app t u) = app (sub f t) (sub f u)
sub f (abs t)   = abs (sub (lift'' f) t)

subcong : ∀{Γ Δ σ}{f f' : Sub Δ Γ} →
          (∀{σ}(x : Var Γ σ) → f x ≅ f' x) → (t : Tm Γ σ) →
          sub f t ≅ sub f' t
subcong p (var x)    = p x
subcong p (abs t)   = hcong abs (subcong (liftcong p) t)
subcong p (app t u) = hcong₂ app (subcong p t) (subcong p u)

-- Category of substitutions.

subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Δ Γ → Sub Γ B → Sub Δ B
subComp f g = sub f ∘ g

-- Functoriality of substitution.

-- First functor law (identity substitution).

liftid : ∀{Γ σ τ}(x : Var (Γ , σ) τ) → lift'' subId x ≅ subId x
liftid zero    = refl
liftid (suc x) = refl

subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≅ t
subid (var x)   = refl
subid (app t u) =
  proof
  app (sub subId t) (sub subId u)
  ≅⟨ hcong₂ app (subid t) (subid u) ⟩
  app t u
  ∎
subid (abs t)   =
  proof
  abs (sub (lift'' subId) t)
  ≅⟨ hcong  abs (subcong liftid t) ⟩
  abs (sub subId t)
  ≅⟨ hcong abs (subid t) ⟩
  abs t
  ∎

-- Second functor law (substitution composition).

liftwk : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Ren Γ B){σ τ}(x : Var (B , σ) τ) →
            (lift'' f ∘ wk g) x ≅ lift'' (f ∘ g) x
liftwk f g zero     = refl
liftwk f g (suc x) = refl

subren : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Ren Γ B){σ}(t : Tm B σ) →
         (sub f ∘ ren g) t ≅ sub (f ∘ g) t
subren f g (var x)   = refl
subren f g (app t u) =
  proof
  app (sub f (ren g t)) (sub f (ren g u))
  ≅⟨ hcong₂ app (subren f g t) (subren f g u) ⟩
  app (sub (f ∘ g) t) (sub (f ∘ g) u)
  ∎
subren f g (abs t)   =
  proof
  abs (sub (lift'' f) (ren (wk g) t))
  ≅⟨ hcong abs (subren (lift'' f) (wk g) t) ⟩
  abs (sub (lift'' f ∘ wk g) t)
  ≅⟨ hcong abs (subcong (liftwk f g) t) ⟩
  abs (sub (lift'' (f ∘ g)) t) ∎

renwklift : ∀{B Γ Δ}(f : Ren Δ Γ)(g : Sub Γ B){σ τ}(x : Var (B , σ) τ) →
               (ren (wk f) ∘ lift'' g) x ≅ lift'' (ren f ∘ g) x
renwklift f g zero     = refl
renwklift f g (suc x) =
  proof
  ren (wk f) (ren suc (g x))
  ≅⟨ hsym (rencomp (wk f) suc (g x)) ⟩
  ren (wk f ∘ suc) (g x)
  ≅⟨ rencomp suc f (g x) ⟩
  ren suc (ren f (g x))
  ∎

rensub : ∀{B Γ Δ}(f : Ren Δ Γ)(g : Sub Γ B){σ}(t : Tm B σ) →
         (ren f ∘ sub g) t ≅ sub (ren f ∘ g) t
rensub f g (var x)   = refl
rensub f g (app t u) =
  proof
  app (ren f (sub g t)) (ren f (sub g u))
  ≅⟨ hcong₂ app (rensub f g t) (rensub f g u) ⟩
  app (sub (ren f ∘ g) t) (sub (ren f ∘ g) u)
  ∎
rensub f g (abs t)   =
  proof
  abs (ren (wk f) (sub (lift'' g) t))
  ≅⟨ hcong abs (rensub (wk f) (lift'' g) t) ⟩
  abs (sub (ren (wk f) ∘ lift'' g) t)
  ≅⟨ hcong abs (subcong (renwklift f g) t) ⟩
  abs (sub (lift'' (ren f ∘ g)) t)
  ∎

liftcomp : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Sub Γ B){σ τ}(x : Var (B , σ) τ) →
           lift'' (subComp f g) x ≅ subComp (lift'' f) (lift'' g) x
liftcomp f g zero     = refl
liftcomp f g (suc x) =
  proof
  ren suc (sub f (g x))
  ≅⟨ rensub suc f (g x) ⟩
  sub (ren suc ∘ f) (g x)
  ≅⟨ hsym (subren (lift'' f) suc (g x)) ⟩
  sub (lift'' f) (ren suc (g x))
  ∎

subcomp : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Sub Γ B){σ}(t : Tm B σ) →
          sub (subComp f g) t ≅ (sub f ∘ sub g) t
subcomp f g (var x)   = refl
subcomp f g (app t u) =
  proof
  app (sub (subComp f g) t) (sub (subComp f g) u)
  ≅⟨ hcong₂ app (subcomp f g t) (subcomp f g u) ⟩
  app (sub f (sub g t)) (sub f (sub g u))
  ∎
subcomp f g (abs t)   =
  proof
  abs (sub (lift'' (subComp f g)) t)
  ≅⟨ hcong abs (subcong (liftcomp f g) t) ⟩
  abs (sub (subComp (lift'' f) (lift'' g)) t)
  ≅⟨ hcong abs (subcomp (lift'' f) (lift'' g) t) ⟩
  abs (sub (lift'' f) (sub (lift'' g) t)) ∎

