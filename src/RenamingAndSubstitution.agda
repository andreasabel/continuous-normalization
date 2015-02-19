module RenAndSub where

open import Library
open import Syntax
open import Function

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
            lookr (renComp f g) i ≅ (lookr f ∘ lookr g) i
lookrcomp f (g , v) zero = refl
lookrcomp f (g , v) (suc i) = lookrcomp f g i

lookrwkr : ∀{Γ Δ σ τ}(xs : Ren Δ Γ)(i : Var Γ σ) →
           lookr (wkr {σ = τ} xs) i ≅ Var.suc {b = τ} (lookr xs i)
lookrwkr (xs , _) zero    = refl
lookrwkr (xs , _) (suc i) = lookrwkr xs i

lemrr : ∀{B Γ Δ σ}(xs : Ren B Γ)(x : Var B σ)(ys : Ren Γ Δ) →
       renComp (xs , x) (wkr ys) ≅ renComp xs ys
lemrr xs x ε        = refl
lemrr xs x (ys , y) = hcong (λ zs → zs , lookr xs y) (lemrr xs x ys)


wkrcomp : ∀{B Γ Δ σ}(xs : Ren B Γ)(ys : Ren Γ Δ) →
       renComp (wkr {σ = σ} xs) ys ≅ wkr {σ = σ} (renComp xs ys)
wkrcomp xs ε        = refl
wkrcomp xs (ys , y) = hcong₂ Ren._,_ (wkrcomp xs ys) (lookrwkr xs y)

lookrid : ∀{Γ σ}(x : Var Γ σ) → lookr renId x ≅ x
lookrid zero    = refl
lookrid (suc x) = htrans (lookrwkr renId x) (hcong suc (lookrid x))

renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≅ t
renid (var x)   = hcong var (lookrid x)
renid (abs t)   = hcong abs (renid t)
renid (app t u) = hcong₂ app (renid t) (renid u)

lidr : ∀{B Γ}(xs : Ren B Γ) → renComp renId xs ≅ xs
lidr ε        = refl
lidr (xs , x) = hcong₂ Ren._,_ (lidr xs) (lookrid x)

ridr : ∀{B Γ}(xs : Ren B Γ) → renComp xs renId ≅ xs
ridr {Γ = ε}     ε  = refl
ridr {Γ = Γ , σ} (xs , x) =
  hcong (λ zs → zs Ren., x)
        (htrans (lemrr xs x renId)
                (ridr {Γ = Γ} xs))

rencomp : ∀ {B Γ Δ}(f : Ren Δ Γ)(g : Ren Γ B){σ}(t : Tm B σ) →
            ren (renComp f g) t ≅ (ren f ∘ ren g) t
rencomp f g (var x)   = hcong Tm.var (lookrcomp f g x)
rencomp f g (abs t)   = hcong abs $
  htrans (hcong (λ xs → ren xs t)
         (hcong (λ zs → zs Ren., zero)
                (htrans (hsym (wkrcomp f g)) (hsym (lemrr (wkr f) zero g)))))
         (rencomp (liftr f) (liftr g) t)
rencomp f g (app t u) = hcong₂ app (rencomp f g t) (rencomp f g u)

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
           looks (wks {σ = τ} xs) i ≅ ren (wkr {σ = τ} renId) (looks xs i)
lookswks zero    (xs , _) = refl
lookswks (suc i) (xs , _) = lookswks i xs

lemsr : ∀{B Γ Δ σ}(xs : Sub B Γ)(x : Tm B σ)(ys : Ren Γ Δ) →
        subComp (xs , x) (ren2sub (wkr ys)) ≅ subComp xs (ren2sub ys)
lemsr xs x ε        = refl
lemsr xs x (ys , y) = hcong (λ zs → zs , looks xs y) (lemsr xs x ys)

lookslookr : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Ren Γ B){σ}(x : Var B σ) →
            looks (subComp f (ren2sub g)) x ≅ looks f (lookr g x)
lookslookr f (g , _) zero    = refl
lookslookr f (g , _) (suc x) = lookslookr f g x            

wksrcomp : ∀{B Γ Δ σ}(xs : Sub B Γ)(ys : Ren Γ Δ) →
  subComp (wks {σ = σ} xs) (ren2sub ys) ≅ wks {σ = σ} (subComp xs (ren2sub ys))
wksrcomp xs ε        = refl
wksrcomp xs (ys , y) = hcong₂ Sub._,_ (wksrcomp xs ys) (lookswks y xs)

subren : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Ren Γ B){σ}(t : Tm B σ) →
         (sub f ∘ ren g) t ≅ sub (subComp f (ren2sub g)) t
subren f g (var x)   = hsym $ lookslookr f g x
subren f g (abs t)   = hcong Tm.abs $
  htrans (subren (lifts f) (liftr g) t)
         (hcong (λ xs → sub xs t)
                (hcong (λ zs → zs Sub., var zero)
                       (htrans (lemsr (wks f) (var zero) g)
                               (wksrcomp f g))))
subren f g (app t u) = hcong₂ app (subren f g t) (subren f g u)


sidr : ∀{B Γ}(xs : Sub B Γ) → subComp xs (ren2sub renId) ≅ xs
sidr {Γ = ε} ε            = refl
sidr {Γ = Γ , a} (xs , x) =
  hcong (λ zs → zs Sub., x)
        (htrans (lemsr xs x renId) (sidr {Γ = Γ} xs))

lemss : ∀{B Γ Δ σ}(xs : Sub B Γ)(x : Tm B σ)(ys : Sub Γ Δ) →
        subComp (xs , x) (wks ys) ≅ subComp xs ys
lemss xs x ε        = refl
lemss xs x (ys , y) = hcong₂
  Sub._,_
  (lemss xs x ys)
  (htrans (subren (xs , x) (wkr renId) y)
          (hcong (λ xs → sub xs y)
                 (htrans (lemsr xs x renId)
                         (sidr xs)))) 

ren2sublook : ∀{Γ Δ σ}(f : Ren Δ Γ)(i : Var Γ σ) →
              Tm.var (lookr f i) ≅ looks (ren2sub f) i
ren2sublook (f , _) zero    = refl
ren2sublook (f , _) (suc i) = ren2sublook f i

ren2subwk : ∀{Γ Δ σ}(g : Ren Δ Γ) →
            ren2sub (wkr {σ = σ} g) ≅ wks {σ = σ} (ren2sub g)
ren2subwk ε       = refl
ren2subwk (g , x) = hcong₂
  Sub._,_
  (ren2subwk g)
  (hcong var
         (htrans (hcong Var.suc (hsym $ lookrid x))
                 (hsym $ lookrwkr renId x)))

ren2subren : ∀{Γ Δ σ}(f : Ren Δ Γ)(t : Tm Γ σ) → ren f t ≅ sub (ren2sub f) t
ren2subren f (var x)   = ren2sublook f x
ren2subren f (abs t)   = hcong Tm.abs $
  htrans (ren2subren (liftr f) t)
  (hcong (λ xs → sub xs t) (hcong (λ zs → zs , var zero) (ren2subwk f)))
ren2subren f (app t u) = hcong₂ app (ren2subren f t) (ren2subren f u)

sidl : ∀{B Γ}(xs : Sub B Γ) → subComp (ren2sub renId) xs ≅ xs
sidl ε        = refl
sidl (xs , x) = hcong₂
  Sub._,_
  (sidl xs)
  (htrans (hsym $ ren2subren renId x )
          (renid x))

wkrscomp : ∀{B Γ Δ σ}(xs : Ren B Γ)(ys : Sub Γ Δ) →
  subComp (ren2sub (wkr {σ = σ} xs)) ys ≅ wks {σ = σ} (subComp (ren2sub xs) ys)
wkrscomp xs ε        = refl
wkrscomp xs (ys , y) = hcong₂
  Sub._,_
  (wkrscomp xs ys)
  (htrans (hsym $ ren2subren (wkr xs) y)
          (htrans (htrans (hcong (λ zs → ren zs y)
                                 (htrans (hcong wkr (hsym $ lidr xs))
                                         (hsym $ wkrcomp renId xs) ))
                          (rencomp (wkr renId) xs y) )
                  (hcong (ren (wkr renId)) (ren2subren xs y))))

renlooks : ∀{B Γ Δ}(f : Ren Δ Γ)(g : Sub Γ B){σ}(x : Var B σ) →
         (ren f ∘ looks g) x ≅ looks (subComp (ren2sub f) g) x
renlooks f (_ , v) zero    = ren2subren f v
renlooks f (g , _) (suc x) = renlooks f g x         

rensub : ∀{B Γ Δ}(f : Ren Δ Γ)(g : Sub Γ B){σ}(t : Tm B σ) →
         (ren f ∘ sub g) t ≅ sub (subComp (ren2sub f) g) t
rensub f g (var x) = renlooks f g x
rensub f g (abs t) = hcong Tm.abs $
  htrans (rensub (liftr f) (lifts g) t)
         (hcong (λ zs → sub zs t)
                (hcong (λ zs → zs Sub., var zero)
                       (htrans (lemss (ren2sub (wkr f)) (var zero) g)
                               (wkrscomp f g))))
rensub f g (app t u) = hcong₂ app (rensub f g t) (rensub f g u)

lookscomp : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Sub Γ B){σ}(x : Var B σ) →
            looks (subComp f g) x ≅ sub f (looks g x)
lookscomp f (g , _) zero    = refl
lookscomp f (g , _) (suc x) = lookscomp f g x

wksscomp : ∀{B Γ Δ σ}(xs : Sub B Γ)(ys : Sub Γ Δ) →
  subComp (wks {σ = σ} xs) ys ≅ wks {σ = σ} (subComp xs ys)
wksscomp xs ε        = refl
wksscomp xs (ys , y) = hcong₂
  Sub._,_
  (wksscomp xs ys)
  (htrans (hcong (λ xs → sub xs y)
                 (htrans (hcong wks (hsym $ sidl xs))
                         (hsym $ wkrscomp renId xs) ))
          (hsym $ rensub (wkr renId) xs y))

subcomp : ∀{B Γ Δ}(f : Sub Δ Γ)(g : Sub Γ B){σ}(t : Tm B σ) →
          sub (subComp f g) t ≅ (sub f ∘ sub g) t
subcomp f g (var x)   = lookscomp f g x
subcomp f g (abs t)   = hcong abs $
  htrans (hcong (λ xs → sub xs t)
                (hcong (λ zs → zs Sub., var zero)
                       (htrans (hsym $ wksscomp f g)
                               (hsym $ lemss (wks f) (var zero) g))))
         (subcomp (lifts f) (lifts g) t)
subcomp f g (app t u) = hcong₂ app (subcomp f g t) (subcomp f g u)
