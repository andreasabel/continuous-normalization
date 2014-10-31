{-# OPTIONS --sized-types --copatterns #-}

-- Syntax: Types, terms and contexts.

module Term where

open import Library
open import Spine

-- Variables and terms.

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀ {Γ a}                 → Var (Γ , a) a
  suc  : ∀ {Γ a b} (x : Var Γ a) → Var (Γ , b) a

data Tm (Γ : Cxt) : (a : Ty) → Set where
  var : ∀ {a}   (x : Var Γ a)                   → Tm Γ a
  abs : ∀ {a b} (t : Tm (Γ , a) b)              → Tm Γ (a ⇒ b)
  app : ∀ {a b} (t : Tm Γ (a ⇒ b)) (u : Tm Γ a) → Tm Γ b

-- β-normal forms.

data βNf {i : Size} (Γ : Cxt) : Ty → Set where
  lam : ∀{j : Size< i}{a b}(n : βNf {j} (Γ , a) b) → βNf Γ (a ⇒ b)
  ne  : ∀{j : Size< i}{a b}(x : Var Γ a)(ns : RSpine (βNf {j} Γ) a b) → βNf Γ b

-- η-long β-normal forms.

mutual
  data Nf {i : Size} (Γ : Cxt) : Ty → Set where
    lam : ∀{j : Size< i}{a b}(n : Nf {j} (Γ , a) b) → Nf Γ (a ⇒ b)
    ne  : ∀{j : Size< i}{a}(x : Var Γ a)(ns : NfSpine {j} Γ a ★) → Nf Γ ★

  NfSpine : {i : Size} (Γ : Cxt) (a c : Ty) → Set
  NfSpine {i} Γ a c = RSpine (Nf {i} Γ) a c

-- Additional stuff for contexts.
-- order preserving embeddings

data _≤_ : (Γ Δ : Cxt) → Set where
  id   : ∀ {Γ} → Γ ≤ Γ
  weak : ∀ {Γ Δ a} → Γ ≤ Δ → (Γ , a) ≤ Δ
  lift : ∀ {Γ Δ a} → Γ ≤ Δ → (Γ , a) ≤ (Δ , a)

-- Composition

_•_ : ∀ {Γ Δ Δ'} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') → Γ ≤ Δ'
id     • η'      = η'
weak η • η'      = weak (η • η')
lift η • id      = lift η
lift η • weak η' = weak (η • η')
lift η • lift η' = lift (η • η')

η•id :  ∀ {Γ Δ} (η : Γ ≤ Δ) → η • id ≡ η
η•id id       = refl
η•id (weak η) = cong weak (η•id η)
η•id (lift η) = refl

•ass : ∀ {Γ Δ Δ' Δ''} (η : Γ ≤ Δ) (η' : Δ ≤ Δ')(η'' : Δ' ≤ Δ'') → 
       η • (η' • η'') ≡ (η • η') • η''
•ass id       η'        η''        = refl
•ass (weak η) η'        η''        = cong weak (•ass η η' η'')
•ass (lift η) id        η''        = refl
•ass (lift η) (weak η') η''        = cong weak (•ass η η' η'')
•ass (lift η) (lift η') id         = refl
•ass (lift η) (lift η') (weak η'') = cong weak (•ass η η' η'')
•ass (lift η) (lift η') (lift η'') = cong lift (•ass η η' η'')

--OPEs form a category
OPECat : Cat 
Obj  OPECat = Cxt
Hom  OPECat = _≤_
iden OPECat = id
comp OPECat = λ f g → g • f
idl  OPECat = ≡-to-≅ (η•id _)
idr  OPECat = refl
ass  OPECat = λ {_ _ _ _ f g h} → ≡-to-≅ (•ass h g f)

-- Smart lift, preserves id (first functor law)

-- lift preserves id too our representation of OPEs is not unique, 
-- hence this trick

lift' : ∀ {Γ Δ a} → Γ ≤ Δ → (Γ , a) ≤ (Δ , a)
lift' id = id
lift' η  = lift η

-- smart lift, preserves composition (second functor law)
lift'-• : ∀ {Γ Δ Δ' a} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') →
  lift' {a = a} η • lift' η' ≡ lift' (η • η')
lift'-• id       η'        = refl
lift'-• (weak η) id        = cong (lift ∘ weak) (sym (η•id η))
lift'-• (weak η) (weak η') = refl
lift'-• (weak η) (lift η') = refl
lift'-• (lift η) id        = refl
lift'-• (lift η) (weak η') = refl
lift'-• (lift η) (lift η') = refl

-- lift' forms an endofunctor on OPECat
liftFun :  Ty → Fun OPECat OPECat
OMap  (liftFun a) = λ Γ → Γ , a
HMap  (liftFun a) = lift'
fid   (liftFun a) = refl
fcomp (liftFun a) = λ {_ _ _ η η'} →  ≡-to-≅ (sym (lift'-• η' η))

-- Monotonicity / map for variables
var≤ : ∀ {Γ Δ}(η : Γ ≤ Δ){a} (x : Var Δ a) → Var Γ a
var≤ id        x      = x
var≤ (weak η)  x      = suc (var≤ η x)
var≤ (lift η)  zero   = zero
var≤ (lift η) (suc x) = suc (var≤ η x)

-- Second functor law.
var≤-• : ∀ {Γ₁ Γ₂ Γ₃ a} (η : Γ₁ ≤ Γ₂) (η' : Γ₂ ≤ Γ₃) (x : Var Γ₃ a) →
  var≤ η (var≤ η' x) ≡ var≤ (η • η') x
var≤-• id       η'        x       = refl
var≤-• (weak η) η'        x       = cong suc (var≤-• η η' x)
var≤-• (lift η) id        x       = refl
var≤-• (lift η) (weak η') x       = cong suc (var≤-• η η' x)
var≤-• (lift η) (lift η') zero    = refl
var≤-• (lift η) (lift η') (suc x) = cong suc (var≤-• η η' x)

--category of polymorphic functions from ∀ {a} → T Γ a → T Δ a
Fam : (I : Set)(T : Cxt → I → Set) → Cat
Fam I T = record
  { Obj = Cxt
  ; Hom = λ Γ Δ → ∀ {a} → T Δ a → T Γ a
  ; iden = idf
  ; comp = λ f g → g ∘ f
  ; idl = refl
  ; idr = refl
  ; ass = refl
  }

-- var≤ forms a functor from the category of OPEs
VarFun : Fun OPECat (Fam Ty Var)
VarFun = record 
  { OMap  = idf
  ; HMap  = var≤ 
  ; fid   = refl 
  ; fcomp = λ{ _ _ _ f g} → iext λ a → ext λ x → ≡-to-≅ (sym (var≤-• g f x)) }

-- Length.
len : Cxt → ℕ
len ε       = 0
len (Γ , _) = 1 + len Γ

-- Monotonicity / map for long normal forms
mutual
  nf≤ : ∀ {i Γ Δ} (η : Γ ≤ Δ){a} (t : Nf {i} Δ a) → Nf {i} Γ a
  nf≤ η (lam t)   = lam (nf≤ (lift' η) t)
  nf≤ η (ne x ts) = ne (var≤ η x) (nfSpine≤ η ts)

  nfSpine≤ : ∀ {i Γ Δ a c} (η : Γ ≤ Δ) (ts : NfSpine {i} Δ a c) → 
             NfSpine {i} Γ a c
  nfSpine≤ η ts = mapRSp (nf≤ η) ts

-- functor law 1
mutual
  nf≤-id : ∀ {i Γ a} (n : Nf {i} Γ a) → nf≤ id n ≡ n
  nf≤-id (lam n)   = cong lam (nf≤-id n)
  nf≤-id (ne x ns) = cong (ne x) (nfSpine≤-id ns)

  nfSpine≤-id : ∀ {i Γ a c} (ns : NfSpine {i} Γ a c) → nfSpine≤ id ns ≡ ns
  nfSpine≤-id ε        = refl
  nfSpine≤-id (ns , n) = cong₂ _,_ (nfSpine≤-id ns) (nf≤-id n)

-- functor law 2

open ≡-Reasoning renaming (begin_ to proof_)

mutual
  nf≤-• : ∀ {i Γ₁ Γ₂ Γ₃ a} (η : Γ₁ ≤ Γ₂) (η' : Γ₂ ≤ Γ₃) (n : Nf {i} Γ₃ a) →
          nf≤ η (nf≤ η' n) ≡ nf≤ (η • η') n
  nf≤-• η η' (lam n)   = proof
    lam (nf≤ (lift' η) (nf≤ (lift' η') n)) 
    ≡⟨ cong lam (nf≤-•  (lift' η) (lift' η') n ) ⟩
    lam (nf≤ (lift' η • lift' η') n)
    ≡⟨ cong (λ f → lam (nf≤ f n)) (lift'-• η η') ⟩
    lam (nf≤ (lift' (η • η')) n) 
    ∎
  nf≤-• η η' (ne x ns) = cong₂ ne (var≤-• η η' x) (nfSpine≤-• η η' ns)

  nfSpine≤-• : ∀{i Γ₁ Γ₂ Γ₃ a c}(η : Γ₁ ≤ Γ₂)(η' : Γ₂ ≤ Γ₃)
               (ns : NfSpine {i} Γ₃ a c) →
               nfSpine≤ η (nfSpine≤ η' ns) ≡ nfSpine≤ (η • η') ns
  nfSpine≤-• η η' ε        = refl
  nfSpine≤-• η η' (ns , n) = cong₂ _,_ (nfSpine≤-• η η' ns) (nf≤-• η η' n)

-- nf≤ forms a functor from the category of OPEs
NfFun : Fun OPECat (Fam Ty Nf)
NfFun = record 
  { OMap  = idf
  ; HMap  = nf≤ 
  ; fid   = iext λ a → ext λ n → ≡-to-≅ (nf≤-id n)
  ; fcomp = λ {_ _ _ f g} → iext λ a → ext λ n → ≡-to-≅ (sym (nf≤-• g f n))}
