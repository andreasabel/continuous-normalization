module RenamingAndSubstitution where

open import Library
open import Syntax

-- ren

data Ren (Δ : Cxt) : (Γ : Cxt) → Set where
  ε   : Ren Δ ε
  _,_ : ∀ {Γ a} (ρ : Ren Δ Γ) (v : Var Δ a) → Ren Δ (Γ , a)

lookr : ∀{Γ Δ} → Ren Δ Γ → ∀ {σ} → Var Γ σ → Var Δ σ
lookr (xs , x) zero    = x
lookr (xs , x) (suc i) = lookr xs i

wkr : ∀{Γ Δ σ} → Ren Γ Δ → Ren (Γ , σ) Δ
wkr ε        = ε
wkr (xs , x) = wkr xs , suc x

liftr : ∀{Γ Δ σ} → Ren Γ Δ → Ren (Γ , σ) (Δ , σ)
liftr xs = wkr xs , zero

ren : ∀{Γ Δ} → Ren Δ Γ → ∀ {σ} → Tm Γ σ → Tm Δ σ
ren xs (var x)   = var (lookr xs x)
ren xs (abs t)   = abs (ren (liftr xs) t)
ren xs (app t u) = app (ren xs t) (ren xs u)

renId : ∀{Γ} → Ren Γ Γ
renId {ε}     = ε
renId {Γ , _} = liftr (renId {Γ}) 

renComp : ∀{B Γ Δ} → Ren Δ Γ → Ren Γ B → Ren Δ B
renComp xs ε        = ε
renComp xs (ys , y) = renComp xs ys , lookr xs y

lookrcomp : ∀{B Γ Δ}(f : Ren Δ Γ)(g : Ren Γ B){σ}(i : Var B σ) →
            lookr (renComp f g) i ≡ (lookr f ∘ lookr g) i
lookrcomp f (g , v) zero = refl
lookrcomp f (g , v) (suc i) = lookrcomp f g i

lookrwkr : ∀{Γ Δ σ τ}(xs : Ren Δ Γ)(i : Var Γ σ) →
           lookr (wkr {σ = τ} xs) i ≡ Var.suc {b = τ} (lookr xs i)
lookrwkr (xs , _) zero    = refl
lookrwkr (xs , _) (suc i) = lookrwkr xs i

lemrr : ∀{B Γ Δ σ}(xs : Ren B Γ)(x : Var B σ)(ys : Ren Γ Δ) →
       renComp (xs , x) (wkr ys) ≡ renComp xs ys
lemrr xs x ε        = refl
lemrr xs x (ys , y) = cong (λ zs → zs , lookr xs y) (lemrr xs x ys)


wkrcomp : ∀{B Γ Δ σ}(xs : Ren B Γ)(ys : Ren Γ Δ) →
       renComp (wkr {σ = σ} xs) ys ≡ wkr {σ = σ} (renComp xs ys)
wkrcomp xs ε        = refl
wkrcomp xs (ys , y) = cong₂ Ren._,_ (wkrcomp xs ys) (lookrwkr xs y)

lookrid : ∀{Γ σ}(x : Var Γ σ) → lookr renId x ≡ x
lookrid zero    = refl
lookrid (suc x) = trans (lookrwkr renId x) (cong suc (lookrid x))

renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≡ t
renid (var x)   = cong var (lookrid x)
renid (abs t)   = cong abs (renid t)
renid (app t u) = cong₂ app (renid t) (renid u)

lidr : ∀{B Γ}(xs : Ren B Γ) → renComp renId xs ≡ xs
lidr ε        = refl
lidr (xs , x) = cong₂ Ren._,_ (lidr xs) (lookrid x)

ridr : ∀{B Γ}(xs : Ren B Γ) → renComp xs renId ≡ xs
ridr {Γ = ε}     ε  = refl
ridr {Γ = Γ , σ} (xs , x) =
  cong (λ zs → zs Ren., x)
        (trans (lemrr xs x renId)
                (ridr {Γ = Γ} xs))

rencomp : ∀ {B Γ Δ}(f : Ren Δ Γ)(g : Ren Γ B){σ}(t : Tm B σ) →
            ren (renComp f g) t ≡ (ren f ∘ ren g) t
rencomp f g (var x)   = cong Tm.var (lookrcomp f g x)
rencomp f g (abs t)   = cong abs $
  trans (cong (λ xs → ren xs t)
         (cong (λ zs → zs Ren., zero)
                (trans (sym (wkrcomp f g)) (sym (lemrr (wkr f) zero g)))))
         (rencomp (liftr f) (liftr g) t)
rencomp f g (app t u) = cong₂ app (rencomp f g t) (rencomp f g u)

-- Renaming of normal forms.

mutual
  rennf : ∀{Γ Δ} → Ren Γ Δ → ∀{a} → Nf Δ a → Nf Γ a
  rennf α (ne t)   = ne (rennen α t)
  rennf α (abs t)  = abs (rennf (liftr α) t)

  rennen : ∀{Γ Δ} → Ren Γ Δ → ∀{a} → Ne Δ a → Ne Γ a
  rennen α (var x) = var (lookr α x)
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
  rennev f (var x)   = var (lookr f x)
  rennev f (app t u) = app (rennev f t) (renval f u)


-- Functoriality of the renaming action on values.

mutual
  renvalid : {Γ : Cxt} {σ : Ty} (v : Val Γ σ) → renval renId v ≡ v
  renvalid (ne x)    = cong ne (rennevid x)
  renvalid (lam t ρ) = cong (lam t) (renenvid ρ)

  renenvid : {Γ Δ : Cxt}(e : Env Γ Δ) → renenv renId e ≡ e
  renenvid ε       = refl
  renenvid (e , v) = cong₂ _,_ (renenvid e) (renvalid v)

  rennevid : {Γ : Cxt} {σ : Ty} (n : NeVal Γ σ) → rennev renId n ≡ n
  rennevid (var x)   = cong var (lookrid x)
  rennevid (app n v) = cong₂ app (rennevid n) (renvalid v)

mutual
  renenvcomp : ∀ {Γ Δ₁ Δ₂ Δ₃} (η : Ren Δ₁ Δ₂) (η' : Ren Δ₂ Δ₃) (ρ : Env Δ₃ Γ) →
           renenv η (renenv η' ρ) ≡ renenv (renComp η η') ρ
  renenvcomp η η' ε       = refl
  renenvcomp η η' (ρ , v) = cong₂ _,_ (renenvcomp η η' ρ) (renvalcomp η η' v)

  renvalcomp : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Ren Δ₁ Δ₂) (η' : Ren Δ₂ Δ₃) (v : Val Δ₃ a) →
           renval η (renval η' v) ≡ renval (renComp η η') v
  renvalcomp η η' (ne t) = cong ne (rennevcomp η η' t)
  renvalcomp η η' (lam t ρ) = cong (lam t) (renenvcomp η η' ρ)

  rennevcomp : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Ren Δ₁ Δ₂) (η' : Ren Δ₂ Δ₃) (t : NeVal Δ₃ a) →
           rennev η (rennev η' t) ≡ rennev (renComp η η') t
  rennevcomp η η' (var x)   = cong var (sym $ lookrcomp η η' x)
  rennevcomp η η' (app t u) = cong₂ app (rennevcomp η η' t) (renvalcomp η η' u)

-- sub

data Sub (Δ : Cxt) : (Γ : Cxt) → Set where
  ε   : Sub Δ ε
  _,_ : ∀ {Γ a} (ρ : Sub Δ Γ) (v : Tm Δ a) → Sub Δ (Γ , a)

ren2sub : ∀{Γ Δ} → Ren Γ Δ → Sub Γ Δ
ren2sub ε        = ε
ren2sub (xs , x) = ren2sub xs , var x

looks : ∀{Γ Δ} → Sub Δ Γ → ∀ {σ} → Var Γ σ → Tm Δ σ
looks (xs , x) zero    = x
looks (xs , x) (suc i) = looks xs i

wks : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ , σ) Δ
wks ε        = ε
wks (xs , x) = wks xs , ren (wkr renId) x

lifts : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ , σ) (Δ , σ)
lifts xs = wks xs , var zero

sub : ∀{Γ Δ} → Sub Δ Γ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub xs (var x)   = looks xs x
sub xs (abs t)   = abs (sub (lifts xs) t)
sub xs (app t u) = app (sub xs t) (sub xs u)

subId : ∀{Γ} → Sub Γ Γ
subId {ε}     = ε
subId {Γ , _} = lifts (subId {Γ})

subComp : ∀{B Γ Δ} → Sub Δ Γ → Sub Γ B → Sub Δ B
subComp xs ε        = ε
subComp xs (ys , y) = subComp xs ys , sub xs y

lookswks : ∀{Γ Δ σ τ}(i : Var Γ σ)(xs : Sub Δ Γ) →
           looks (wks {σ = τ} xs) i ≡ ren (wkr {σ = τ} renId) (looks xs i)
lookswks zero    (xs , _) = refl
lookswks (suc i) (xs , _) = lookswks i xs

lemsr : ∀{B Γ Δ σ}(xs : Sub B Γ)(x : Tm B σ)(ys : Ren Γ Δ) →
        subComp (xs , x) (ren2sub (wkr ys)) ≡ subComp xs (ren2sub ys)
lemsr xs x ε        = refl
lemsr xs x (ys , y) = cong (λ zs → zs , looks xs y) (lemsr xs x ys)

lookslookr : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Ren Γ B){σ}(x : Var B σ) →
            looks (subComp f (ren2sub g)) x ≡ looks f (lookr g x)
lookslookr f (g , _) zero    = refl
lookslookr f (g , _) (suc x) = lookslookr f g x            

wksrcomp : ∀{B Γ Δ σ}(xs : Sub B Γ)(ys : Ren Γ Δ) →
  subComp (wks {σ = σ} xs) (ren2sub ys) ≡ wks {σ = σ} (subComp xs (ren2sub ys))
wksrcomp xs ε        = refl
wksrcomp xs (ys , y) = cong₂ Sub._,_ (wksrcomp xs ys) (lookswks y xs)

subren : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Ren Γ B){σ}(t : Tm B σ) →
         (sub f ∘ ren g) t ≡ sub (subComp f (ren2sub g)) t
subren f g (var x)   = sym $ lookslookr f g x
subren f g (abs t)   = cong Tm.abs $
  trans (subren (lifts f) (liftr g) t)
         (cong (λ xs → sub xs t)
                (cong (λ zs → zs Sub., var zero)
                       (trans (lemsr (wks f) (var zero) g)
                               (wksrcomp f g))))
subren f g (app t u) = cong₂ app (subren f g t) (subren f g u)


looksid : ∀{Γ σ}(x : Var Γ σ) → looks subId x ≡ var x
looksid zero    = refl
looksid (suc x) = trans (lookswks x subId) (trans (cong (ren (wkr renId)) (looksid x)) (cong var (trans (lookrwkr renId x) (cong suc (lookrid x)))))

subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≡ t
subid (var x)   = looksid x
subid (abs t)   = cong abs (subid t)
subid (app t u) = cong₂ app (subid t) (subid u)

sidl : ∀{B Γ}(xs : Sub B Γ) → subComp subId xs ≡ xs
sidl ε        = refl
sidl (xs , t) = cong₂ _,_ (sidl xs) (subid t)

sidr2 : ∀{B Γ}(xs : Sub B Γ) → subComp xs (ren2sub renId) ≡ xs
sidr2 {Γ = ε} ε            = refl
sidr2 {Γ = Γ , a} (xs , x) = cong
  (λ zs → zs , x)
  (trans (lemsr xs x renId) ( sidr2 {Γ = Γ} xs ))

lemss : ∀{B Γ Δ σ}(xs : Sub B Γ)(x : Tm B σ)(ys : Sub Γ Δ) →
        subComp (xs , x) (wks ys) ≡ subComp xs ys
lemss xs x ε        = refl
lemss xs x (ys , y) = cong₂
  Sub._,_
  (lemss xs x ys)
  (trans (subren (xs , x) (wkr renId) y)
          (cong (λ xs → sub xs y)
                 (trans (lemsr xs x renId)
                        (sidr2 xs))))
                        
ren2sublook : ∀{Γ Δ σ}(f : Ren Δ Γ)(i : Var Γ σ) →
              Tm.var (lookr f i) ≡ looks (ren2sub f) i
ren2sublook (f , _) zero    = refl
ren2sublook (f , _) (suc i) = ren2sublook f i

ren2subwk : ∀{Γ Δ σ}(g : Ren Δ Γ) →
            ren2sub (wkr {σ = σ} g) ≡ wks {σ = σ} (ren2sub g)
ren2subwk ε       = refl
ren2subwk (g , x) = cong₂
  Sub._,_
  (ren2subwk g)
  (cong var
         (trans (cong Var.suc (sym $ lookrid x))
                 (sym $ lookrwkr renId x)))

ren2subren : ∀{Γ Δ σ}(f : Ren Δ Γ)(t : Tm Γ σ) → ren f t ≡ sub (ren2sub f) t
ren2subren f (var x)   = ren2sublook f x
ren2subren f (abs t)   = cong Tm.abs $
  trans (ren2subren (liftr f) t)
  (cong (λ xs → sub xs t) (cong (λ zs → zs , var zero) (ren2subwk f)))
ren2subren f (app t u) = cong₂ app (ren2subren f t) (ren2subren f u)


wkrscomp : ∀{B Γ Δ σ}(xs : Ren B Γ)(ys : Sub Γ Δ) →
  subComp (ren2sub (wkr {σ = σ} xs)) ys ≡ wks {σ = σ} (subComp (ren2sub xs) ys)
wkrscomp xs ε        = refl
wkrscomp xs (ys , y) = cong₂
  Sub._,_
  (wkrscomp xs ys)
  (trans (sym $ ren2subren (wkr xs) y)
          (trans (trans (cong (λ zs → ren zs y)
                                 (trans (cong wkr (sym $ lidr xs))
                                         (sym $ wkrcomp renId xs) ))
                          (rencomp (wkr renId) xs y) )
                  (cong (ren (wkr renId)) (ren2subren xs y))))

renlooks : ∀{B Γ Δ}(f : Ren Δ Γ)(g : Sub Γ B){σ}(x : Var B σ) →
         (ren f ∘ looks g) x ≡ looks (subComp (ren2sub f) g) x
renlooks f (_ , v) zero    = ren2subren f v
renlooks f (g , _) (suc x) = renlooks f g x         

rensub : ∀{B Γ Δ}(f : Ren Δ Γ)(g : Sub Γ B){σ}(t : Tm B σ) →
         (ren f ∘ sub g) t ≡ sub (subComp (ren2sub f) g) t
rensub f g (var x) = renlooks f g x
rensub f g (abs t) = cong Tm.abs $
  trans (rensub (liftr f) (lifts g) t)
         (cong (λ zs → sub zs t)
                (cong (λ zs → zs Sub., var zero)
                       (trans (lemss (ren2sub (wkr f)) (var zero) g)
                               (wkrscomp f g))))
rensub f g (app t u) = cong₂ app (rensub f g t) (rensub f g u)

lookscomp : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Sub Γ B){σ}(x : Var B σ) →
            looks (subComp f g) x ≡ sub f (looks g x)
lookscomp f (g , _) zero    = refl
lookscomp f (g , _) (suc x) = lookscomp f g x

ren2subid : ∀{Γ} → subId {Γ} ≡ ren2sub renId
ren2subid {ε}     = refl
ren2subid {Γ , a} = cong (λ xs → xs , var zero)
                         (trans (cong wks (ren2subid {Γ}))
                                (sym $ ren2subwk renId))

wksscomp : ∀{B Γ Δ σ}(xs : Sub B Γ)(ys : Sub Γ Δ) →
  subComp (wks {σ = σ} xs) ys ≡ wks {σ = σ} (subComp xs ys)
wksscomp xs ε        = refl
wksscomp xs (ys , y) = cong₂
  Sub._,_
  (wksscomp xs ys)
  (trans (cong (λ xs → sub xs y)
                 (trans (cong wks (sym $ sidl xs))
                        (trans (cong (λ ys → wks (subComp ys xs)) ren2subid)
                               (sym $ wkrscomp renId xs) )))
          (sym $ rensub (wkr renId) xs y))

sidr : ∀{B Γ}(xs : Sub B Γ) → subComp xs subId ≡ xs
sidr xs = trans (cong (subComp xs) ren2subid) (sidr2 xs)

subcomp : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Sub Γ B){σ}(t : Tm B σ) →
          sub (subComp f g) t ≡ (sub f ∘ sub g) t
subcomp f g (var x)   = lookscomp f g x
subcomp f g (abs t)   = cong abs $
  trans (cong (λ xs → sub xs t)
                (cong (λ zs → zs Sub., var zero)
                       (trans (sym $ wksscomp f g)
                               (sym $ lemss (wks f) (var zero) g))))
         (subcomp (lifts f) (lifts g) t)
subcomp f g (app t u) = cong₂ app (subcomp f g t) (subcomp f g u)

--


mutual
  renembNe : ∀{Γ Δ a}(u : Ne Γ a)(σ : Ren Δ Γ) →
             ren σ (embNe u) ≡ embNe (rennen σ u)
  renembNe (var x)   σ = refl
  renembNe (app u n) σ = cong₂ app (renembNe u σ) (renembNf n σ)    

  renembNf : ∀{Γ Δ a}(n : Nf Γ a)(σ : Ren Δ Γ) →
             ren σ (embNf n) ≡ embNf (rennf σ n)
  renembNf (abs n) σ = cong abs (renembNf n (liftr σ))
  renembNf (ne n)  σ = renembNe n σ
