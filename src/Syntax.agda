-- Syntax: Types, terms and contexts.
module Syntax where

open import Library

infixr 6 _⇒_
infixr 4 _,_

-- Types and contexts.

data Ty : Set where
  ★   : Ty
  _⇒_ : (a b : Ty) → Ty

data Cxt : Set where
  ε   : Cxt
  _,_ : (Γ : Cxt) (a : Ty) → Cxt

-- Variables and terms.

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀ {Γ a}                 → Var (Γ , a) a
  suc  : ∀ {Γ a b} (x : Var Γ a) → Var (Γ , b) a

data Tm (Γ : Cxt) : (a : Ty) → Set where
  var : ∀ {a}   (x : Var Γ a)                   → Tm Γ a
  abs : ∀ {a b} (t : Tm (Γ , a) b)              → Tm Γ (a ⇒ b)
  app : ∀ {a b} (t : Tm Γ (a ⇒ b)) (u : Tm Γ a) → Tm Γ b

-- Generalized neutral terms.

data GNe (Arg : Cxt → Ty → Set) (Γ : Cxt) : Ty → Set where
  var : ∀{a}    (x : Var Γ a)                         → GNe Arg Γ a
  app : ∀{a b}  (n : GNe Arg Γ (a ⇒ b)) (o : Arg Γ a) → GNe Arg Γ b

-- β-normal forms.

mutual

  Ne = GNe Nf

  data Nf (Γ : Cxt) : Ty → Set where
    abs : ∀{a b}  (o : Nf (Γ , a) b)  → Nf Γ (a ⇒ b)
    ne  :         (n : Ne Γ ★)        → Nf Γ ★

mutual

  embNe : ∀{Γ a} → Ne Γ a → Tm Γ a
  embNe (var x) = var x
  embNe (app t u) = app (embNe t) (embNf u)

  embNf : ∀{Γ a} → Nf Γ a → Tm Γ a
  embNf (ne t) = embNe t
  embNf (abs t) = abs (embNf t)

-- Values and environments.

mutual

  data Env (i : Size) (Δ : Cxt) : (Γ : Cxt) → Set where
    ε   : Env i Δ ε
    _,_ : ∀ {Γ a} (ρ : Env i Δ Γ) (v : Val i Δ a) → Env i Δ (Γ , a)

  NeVal = λ i → GNe (Val i)

  data Val (i : Size) (Δ : Cxt) : (a : Ty) → Set where
    ne    : ∀{a}      (n : NeVal i Δ a)                   → Val i Δ a
    lam   : ∀{Γ a b}  (t : Tm (Γ , a) b) (ρ : Env i Δ Γ)  → Val i Δ (a ⇒ b)
    later : ∀{a}      (v∞ : ∞Val i Δ a)                   → Val i Δ a

  record ∞Val (i : Size) (Δ : Cxt) (a : Ty) : Set where
    coinductive
    constructor ∞val
    field
      force : {j : Size< i} → Val j Δ a


  -- Note: this is not the same thing as Delay i (Val i Δ a)
  -- because now the sizes are not uniform, but the size is
  -- the sum on the longest path

  -- ALT:
  -- data Delay (i : Size) (A : Size → Set) : Set where
  --   now : A i → Delay i A
  --   ...
  -- but we would need to tell Agda that A is antitone
  -- otherwise Delay i A is not antitone in i

mutual
  Val∋_≈⟨_⟩≈_ = λ {Δ}{a} a? i b? → Val∋_≈_ {i}{Δ}{a} a? b?
  NeVal∋_≈⟨_⟩≈_ = λ {Δ}{a} a? i b? → NeVal∋_≈_ {i}{Δ}{a} a? b?
  Env∋_≈⟨_⟩≈_ = λ {Δ}{Γ} a? i b? → Env∋_≈_ {i}{Δ}{Γ} a? b?

  data NeVal∋_≈_ {i}{Δ} : {a : Ty}(a? b? : NeVal ∞ Δ a) → Set where
    ≈var : ∀{a}{x : Var Δ a} → NeVal∋ var x ≈ var x
    ≈app : ∀{a b}{n n' : NeVal ∞ Δ (a ⇒ b)} → NeVal∋ n ≈⟨ i ⟩≈ n' →
           {v v' : Val ∞ Δ a} → Val∋ v ≈⟨ i ⟩≈ v' → NeVal∋ app n v ≈ app n' v'
 
  data Env∋_≈_ {i}{Δ} : ∀{Γ} → Env ∞ Δ Γ → Env ∞ Δ Γ → Set where
    ≈ε : Env∋ ε ≈ ε
    _≈,_ : ∀{Γ a}{ρ ρ' : Env ∞ Δ Γ} → Env∋ ρ ≈⟨ i ⟩≈ ρ' →
           {v v' : Val ∞ Δ a} → Val∋ v ≈⟨ i ⟩≈ v' → Env∋ (ρ , v) ≈ (ρ' , v')
    
  data Val∋_≈_ {i}{Δ} : {a : Ty}(a? b? : Val ∞ Δ a) → Set where
    ≈lam : ∀{Γ a b}{t : Tm (Γ , a) b}{ρ ρ' : Env ∞ Δ Γ} → Env∋ ρ ≈⟨ i ⟩≈ ρ' →
           Val∋ lam t ρ ≈ lam t ρ'
    ≈ne  : ∀{a}{n n' : NeVal ∞ Δ a} → NeVal∋ n ≈⟨ i ⟩≈ n' → Val∋ ne n ≈ ne n'
    ≈later : ∀ {a}{a∞ b∞ : ∞Val ∞ Δ a}(eq : ∞Val∋ a∞ ≈⟨ i ⟩≈ b∞) →
             Val∋ later a∞ ≈ later b∞

  record ∞Val∋_≈⟨_⟩≈_ {Δ a} (a∞ : ∞Val ∞ Δ a) i (b∞ : ∞Val ∞ Δ a) : Set where
    coinductive
    field
      ≈force : {j : Size< i} → Val∋ ∞Val.force a∞ ≈⟨ j ⟩≈ ∞Val.force b∞

  ∞Val∋_≈_ = λ {i}{Δ}{a} a? b? → ∞Val∋_≈⟨_⟩≈_ {Δ}{a} a? i b?

mutual
  ≈reflVal : ∀{i}{Δ}{a}(v : Val ∞ Δ a) → Val∋ v ≈⟨ i ⟩≈ v
  ≈reflVal {i} (ne n) = ≈ne (≈reflNeVal {i = i} n)
  ≈reflVal (lam t ρ)  = ≈lam (≈reflEnv ρ)
  ≈reflVal (later v∞) = ≈later (∞≈reflVal v∞)

  ∞≈reflVal : ∀{i}{Δ}{a}(v : ∞Val ∞ Δ a) → ∞Val∋ v ≈⟨ i ⟩≈ v
  ∞Val∋_≈⟨_⟩≈_.≈force (∞≈reflVal v) = ≈reflVal (∞Val.force v) 

  ≈reflNeVal : ∀{i}{Δ}{a}(v : NeVal ∞ Δ a) → NeVal∋ v ≈⟨ i ⟩≈ v
  ≈reflNeVal (var x) = ≈var
  ≈reflNeVal (app v o) = ≈app (≈reflNeVal v) (≈reflVal o)

  ≈reflEnv : ∀{i}{Δ}{Γ}(e : Env ∞ Δ Γ) → Env∋ e ≈⟨ i ⟩≈ e
  ≈reflEnv ε = ≈ε
  ≈reflEnv (e , v) = ≈reflEnv e ≈, ≈reflVal v

mutual
  ≈symVal : ∀{i}{Δ}{a}{v v' : Val ∞ Δ a} → Val∋ v ≈⟨ i ⟩≈ v' → 
            Val∋ v' ≈⟨ i ⟩≈ v
  ≈symVal (≈lam p) = ≈lam (≈symEnv p )
  ≈symVal (≈ne p)  = ≈ne (≈symNeVal p)
  ≈symVal (≈later p) = ≈later (∞≈symVal p)

  ∞≈symVal : ∀{i}{Δ}{a}{v v' : ∞Val ∞ Δ a} → ∞Val∋ v ≈⟨ i ⟩≈ v' → 
             ∞Val∋ v' ≈⟨ i ⟩≈ v
  ∞Val∋_≈⟨_⟩≈_.≈force (∞≈symVal p) = ≈symVal (∞Val∋_≈⟨_⟩≈_.≈force p)

  ≈symNeVal : ∀{i}{Δ}{a}{v v' : NeVal ∞ Δ a} →
              NeVal∋ v ≈⟨ i ⟩≈ v' → NeVal∋ v' ≈⟨ i ⟩≈ v
  ≈symNeVal ≈var       = ≈var
  ≈symNeVal (≈app p q) = ≈app (≈symNeVal p) (≈symVal q)
  
  ≈symEnv : ∀{i}{Δ}{Γ}{e e' : Env ∞ Δ Γ} →
             Env∋ e ≈⟨ i ⟩≈ e' → Env∋ e' ≈⟨ i ⟩≈ e
  ≈symEnv ≈ε       = ≈ε
  ≈symEnv (p ≈, q) = ≈symEnv p ≈, ≈symVal q

mutual
  ≈transVal : ∀{i}{Δ}{a}{v v' v'' : Val ∞ Δ a} → Val∋ v ≈⟨ i ⟩≈ v' → 
            Val∋ v' ≈⟨ i ⟩≈ v'' → Val∋ v ≈⟨ i ⟩≈ v''
  ≈transVal (≈lam p)   (≈lam p')   = ≈lam (≈transEnv p p')
  ≈transVal (≈ne p)    (≈ne p')    = ≈ne (≈transNeVal p p')
  ≈transVal (≈later p) (≈later p') = ≈later (∞≈transVal p p')            

  ∞≈transVal : ∀{i}{Δ}{a}{v v' v'' : ∞Val ∞ Δ a} → ∞Val∋ v ≈⟨ i ⟩≈ v' → 
    ∞Val∋ v' ≈⟨ i ⟩≈ v'' → ∞Val∋ v ≈⟨ i ⟩≈ v''
  ∞Val∋_≈⟨_⟩≈_.≈force (∞≈transVal p q) =
    ≈transVal (∞Val∋_≈⟨_⟩≈_.≈force p) (∞Val∋_≈⟨_⟩≈_.≈force q)

  ≈transNeVal : ∀{i}{Δ}{a}{v v' v'' : NeVal ∞ Δ a} →
              NeVal∋ v ≈⟨ i ⟩≈ v' → NeVal∋ v' ≈⟨ i ⟩≈ v'' → 
              NeVal∋ v ≈⟨ i ⟩≈ v''
  ≈transNeVal ≈var       ≈var        = ≈var
  ≈transNeVal (≈app p q) (≈app p' q') =
    ≈app (≈transNeVal p p' ) (≈transVal q q')
  
  ≈transEnv : ∀{i}{Δ}{a}{v v' v'' : Env ∞ Δ a} → Env∋ v ≈⟨ i ⟩≈ v' → 
    Env∋ v' ≈⟨ i ⟩≈ v'' → Env∋ v ≈⟨ i ⟩≈ v''
  ≈transEnv ≈ε       ≈ε         = ≈ε
  ≈transEnv (p ≈, q) (p' ≈, q') = (≈transEnv p p') ≈, ≈transVal q q'

{-
  ≈congVal : ∀{i Δ Γ a b}(f : Val ∞ Δ a → Val ∞ Γ b){v v' : Val ∞ Δ a} →
             Val∋ v ≈⟨ i ⟩≈ v' → Val∋ f v ≈⟨ i ⟩≈ f v'
  ≈congVal f (≈lam x) = {!!}
  ≈congVal f (≈ne x) = {!!}
  ≈congVal f (≈later eq) = {!!}
-}
≈Valsetoid : (i : Size)(Δ : Cxt)(a : Ty) → Setoid lzero lzero
≈Valsetoid i Δ a = record
  { Carrier       = Val ∞ Δ a
  ; _≈_           = Val∋_≈_ {i}
  ; isEquivalence = record
    { refl  = ≈reflVal _
    ; sym   = ≈symVal
    ; trans = ≈transVal
    }
  }

module ≈Val-Reasoning {i : Size}{Δ : Cxt}{a : Ty} where
  open Pre (Setoid.preorder (≈Valsetoid i Δ a)) public
--    using (begin_; _∎) (_≈⟨⟩_ to _≈⟨⟩_; _≈⟨_⟩_ to _≈⟨_⟩_)
    renaming (_≈⟨⟩_ to _≡⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _≈⟨_⟩_; begin_ to proof_)


