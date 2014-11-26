module RenamingAndSubstitution where

open import Library hiding (_≡_)
open import Term
open import Spine

-- renaming and substitution from relative monads

Ren : Cxt → Cxt → Set
Ren Γ Δ = ∀ {σ} → Var Γ σ → Var Δ σ 

renId : ∀{Γ} → Ren Γ Γ
renId = idf

renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = f ∘ g

ConCat : Cat 
ConCat = record{
  Obj  = Cxt; 
  Hom  = Ren;
  iden = renId;
  comp = renComp;
  idl  = iext λ _ → refl;
  idr  = iext λ _ → refl;
  ass  = iext λ _ → refl}

wk : ∀{Γ Δ σ} → Ren Γ Δ → Ren (Γ , σ) (Δ , σ)
wk f zero     = zero
wk f (suc i) = suc (f i)

wkcong : ∀{Γ Δ σ τ}{f f' : Ren Γ Δ} →
         (∀{σ}(x : Var Γ σ) → f x ≅ f' x) → (x : Var (Γ , τ) σ) →
         wk f x ≅ wk f' x
wkcong p zero    = refl
wkcong p (suc x) = hcong suc (p x)

ren : ∀{Γ Δ} → Ren Γ Δ → ∀ {σ} → Tm Γ σ → Tm Δ σ
ren f (var x)   = var (f x)
ren f (app t u) = app (ren f t) (ren f u)
ren f (abs t)   = abs (ren (wk f) t)

rencong : ∀{Γ Δ σ}{f f' : Ren Γ Δ} →
          (∀{σ}(x : Var Γ σ) → f x ≅ f' x) → (t : Tm Γ σ) →
          ren f t ≅ ren f' t
rencong p (var x)   = hcong var (p x)
rencong p (abs t)   = hcong abs (rencong (wkcong p) t)
rencong p (app t u) = hcong₂ app (rencong p t) (rencong p u)

wkid : ∀{Γ σ τ}(x : Var (Γ , τ) σ) → wk renId x ≅ renId x
wkid zero    = refl
wkid (suc x) = refl

open ≅-Reasoning renaming (begin_ to proof_)

renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≅ idf t
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

wkcomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B , σ) τ) → 
            wk (renComp f g) x ≅ renComp (wk f) (wk g) x  
wkcomp f g zero     = refl
wkcomp f g (suc i) = refl

rencomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
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

Sub : Cxt → Cxt → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift'' : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ , σ) (Δ , σ)
lift'' f zero     = var zero
lift'' f (suc x) = ren suc (f x)

liftcong : ∀{Γ Δ σ τ}{f f' : Sub Γ Δ} →
         (∀{σ}(x : Var Γ σ) → f x ≅ f' x) → (x : Var (Γ , τ) σ) →
         lift'' f x ≅ lift'' f' x
liftcong p zero    = refl
liftcong p (suc x) = hcong (ren suc) (p x) -- doesn't rely on rencong

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x)   = f x
sub f (app t u) = app (sub f t) (sub f u)
sub f (abs t)   = abs (sub (lift'' f) t)

subcong : ∀{Γ Δ σ}{f f' : Sub Γ Δ} →
          (∀{σ}(x : Var Γ σ) → f x ≅ f' x) → (t : Tm Γ σ) →
          sub f t ≅ sub f' t
subcong p (var x)    = p x
subcong p (abs t)   = hcong abs (subcong (liftcong p) t)
subcong p (app t u) = hcong₂ app (subcong p t) (subcong p u)

subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g

liftid : ∀{Γ σ τ}(x : Var (Γ , σ) τ) → lift'' subId x ≅ subId x
liftid zero    = refl
liftid (suc x) = refl

subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≅ idf t
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

liftwk : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B , σ) τ) →
            (lift'' f ∘ wk g) x ≅ lift'' (f ∘ g) x
liftwk f g zero     = refl
liftwk f g (suc x) = refl

subren : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
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

renwklift : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B , σ) τ) →
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

rensub : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) →
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

liftcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B , σ) τ) →
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

subcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) → 
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

