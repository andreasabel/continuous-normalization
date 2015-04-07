{-# OPTIONS --copatterns --sized-types #-}

module Completeness where

open import Library
open import Delay
open import WeakBisim
open import Syntax
open import RenamingAndSubstitution
open import Evaluation
open import EquationalTheory
open import Termination using (rennereadback⇓)

-- infixr 4 _,_

record Delay_∋_≃_ {A} (R : A → A → Set) (a? b? : Delay ∞ A) : Set where
  constructor delay≃
  field
    a   : A
    a⇓  : a? ⇓ a
    b   : A
    b⇓  : b? ⇓ b
    rab : R a b

-- Symmetry

D≃sym : ∀ {A R} {a? b? : Delay ∞ A}
     → (sym : ∀ {a b} → R a b → R b a)
     → (r : Delay R ∋ a? ≃ b?) → Delay R ∋ b? ≃ a?
D≃sym sym (delay≃ a a⇓ b b⇓ rab) = delay≃ b b⇓ a a⇓ (sym rab)

D≃trans : ∀ {A R} {a? b? c? : Delay ∞ A}
     → (trans : ∀ {a b c} → R a b → R b c → R a c)
     → (r : Delay R ∋ a? ≃ b?) (s : Delay R ∋ b? ≃ c?) → Delay R ∋ a? ≃ c?
D≃trans trans (delay≃ a a⇓ b b⇓ rab) (delay≃ b′ b⇓′ c c⇓ rbc) with uniq⇓ b⇓ b⇓′
D≃trans trans (delay≃ a a⇓ b b⇓ rab) (delay≃ .b b⇓′ c c⇓ rbc) | refl = delay≃ a a⇓ c c⇓ (trans rab rbc)


-- _≃_ : ∀{Γ} (v v' : Val Γ ★) → Set
-- ne v ≃ ne v' = ∃ λ n → nereadback v ⇓ n × nereadback v' ⇓ n

record _≃_ {Γ a} (n n' : NeVal Γ a) : Set where
  constructor ne≃
  field
    read : Ne Γ a
    fst⇓ : nereadback n  ⇓ read
    snd⇓ : nereadback n' ⇓ read

≃sym : ∀ {Γ a} {n n' : NeVal Γ a} (r : n ≃ n') → n' ≃ n
≃sym (ne≃ n fst⇓ snd⇓) = ne≃ n snd⇓ fst⇓

≃trans : ∀ {Γ a} {n m l : NeVal Γ a} (r : n ≃ m) (s : m ≃ l) → n ≃ l
≃trans (ne≃ z n⇓ m⇓) (ne≃ z′ m⇓′ l⇓) with uniq⇓ m⇓ m⇓′
≃trans (ne≃ z n⇓ m⇓) (ne≃ .z m⇓′ l⇓) | refl = ne≃ z n⇓ l⇓

ren≃ : ∀ {Γ Δ a} (η : Ren Δ Γ) {v v' : NeVal Γ a} (r : v ≃ v') → rennev η v ≃ rennev η v'
ren≃ η {v} {v'} (ne≃ n v⇓n v'⇓n) =
  ne≃ (rennen η n) (rennereadback⇓ η v v⇓n) (rennereadback⇓ η v' v'⇓n)

mutual

  -- Values v and v' are related at type a.

  _V∋_≃_ : ∀{Γ}(a : Ty) (v v' : Val Γ a) → Set
  _V∋_≃_         ★       (ne n) (ne n') = n ≃ n'
  _V∋_≃_ {Γ = Γ} (a ⇒ b) f     f'       = ∀{Δ}(ρ : Ren Δ Γ)(u u' : Val Δ a)
    (u≃u' : a V∋ u ≃ u') → b C∋ (apply (renval ρ f) u) ≃ (apply (renval ρ f') u')

  VLR : ∀{Γ}(a : Ty) (v v' : Val Γ a) → Set
  VLR a v v' = _V∋_≃_ a v v'

  -- Value computations v? and w? are related at type a.

  _C∋_≃_ : ∀{Γ}(a : Ty) (v? w? : Delay ∞ (Val Γ a)) → Set
  a C∋ v? ≃ w? = Delay (VLR a) ∋ v? ≃ w?



V∋≃sym : ∀{Γ}(a : Ty){v v' : Val Γ a} →
           a V∋ v ≃ v' → a V∋ v' ≃ v
V∋≃sym ★       {ne _}{ne _} p          = ≃sym p
V∋≃sym (a ⇒ b)              p ρ u u' q =
  D≃sym (V∋≃sym b) (p ρ u' u (V∋≃sym a q))


V∋≃trans : ∀{Γ}(a : Ty){v v' v'' : Val Γ a} →
           a V∋ v ≃ v' → a V∋ v' ≃ v'' → a V∋ v ≃ v''
V∋≃trans ★ {ne n}{ne n'}{ne n''} p q = ≃trans p q
V∋≃trans (a ⇒ b) p q ρ u u' r =
  D≃trans {R = VLR b} (V∋≃trans b)
                     (p ρ u u (V∋≃trans a r (V∋≃sym a r)))
                     (q ρ u u' r)

{-
V∋≃refl : ∀{Γ}(a : Ty){v v' : Val Γ a} →
           a V∋ v ≃ v' → a V∋ v ≃ v
V∋≃refl a p = V∋≃trans a p (V∋≃sym a p)

C∋≃refl : ∀{Γ}(a : Ty){v v' : Delay ∞ (Val Γ a)} →
           a C∋ v ≃ v' → a C∋ v ≃ v
C∋≃refl a p = ≃trans (V∋≃trans a) p (≃sym (V∋≃sym a) p)
-}

-- Environments ρ and ρ' are related.

_≃E_ : ∀{Γ Δ} (ρ ρ' : Env Δ Γ) → Set
ε       ≃E ε         = ⊤
(ρ , v) ≃E (ρ' , v') = (ρ ≃E ρ') × (VLR _ v v')

≃Esym : ∀{Γ Δ}{ρ ρ' : Env Δ Γ} → ρ ≃E ρ' → ρ' ≃E ρ
≃Esym {ρ = ε}    {ε}       _        = _
≃Esym {ρ = ρ , v}{ρ' , v'} (p , p') = ≃Esym p  , V∋≃sym _ p'

≃Etrans : ∀{Γ Δ}{ρ ρ' ρ'' : Env Δ Γ} → ρ ≃E ρ' → ρ' ≃E ρ'' → ρ ≃E ρ''
≃Etrans {ρ = ε}    {ε}       {ε}         _         _        = _
≃Etrans {ρ = ρ , v}{ρ' , v'} {ρ'' , v''} (p , q)  (p' , q') = ≃Etrans p p' , V∋≃trans _ q q'

≃Erefl : ∀{Γ Δ}{ρ ρ' : Env Δ Γ} → ρ ≃E ρ' → ρ ≃E ρ
≃Erefl p = ≃Etrans p (≃Esym p)



-- Closure under renaming

renV≃ : ∀{Δ Δ′} a (η : Ren Δ′ Δ) {v v' : Val Δ a} (v≃v' : VLR a v v') →
        VLR a (renval η v) (renval η v')
renV≃ ★       η {ne n}{ne n'} p    = ren≃ η p
renV≃ (a ⇒ b) η {f}{f'} p ρ u u' q =
  subst (λ X → b C∋ apply (renval ρ (renval η f)) u ≃ apply X u')
        (sym $ renvalcomp ρ η f')
        (subst (λ X → b C∋ apply X u ≃ apply (renval (renComp ρ η) f') u')
               (sym $ renvalcomp ρ η f)
               (p (renComp ρ η) u u' q))

renE≃ : ∀{Γ Δ Δ′} (η : Ren Δ′ Δ) {ρ ρ' : Env Δ Γ} (ρ≃ρ' : ρ ≃E ρ') → (renenv η ρ) ≃E (renenv η ρ')
renE≃ η {ε} {ε} ρ≃ρ' = _
renE≃ η {ρ , v} {ρ' , v'} (ρ≃ρ' , v≃v') = (renE≃ η ρ≃ρ') , (renV≃ _ η v≃v')

{-

-- Substitution lemma.

data DEnv (Δ : Cxt) : (Γ : Cxt) → Set where
  ε   : DEnv Δ ε
  _,_ : ∀ {Γ a} (ρ : DEnv Δ Γ) (v : Delay ∞ (Val Δ a)) → DEnv Δ (Γ , a)

sequence : ∀{Γ Δ} → DEnv Γ Δ → Delay ∞ (Env Γ Δ)
sequence ε = now ε
sequence (ρ , v?) = _,_ <$> sequence ρ <*> v?

evalS₀ : ∀{Γ Δ Δ′} (σ : Sub Δ Δ′) (ρ : Env Γ Δ) → DEnv Γ Δ′
evalS₀ ε       ρ = ε
evalS₀ (σ , t) ρ = evalS₀ σ ρ , eval t ρ


evalS : ∀{Γ Δ Δ′} (σ : Sub Δ Δ′) (ρ : Env Γ Δ) → Delay ∞ (Env Γ Δ′)
evalS σ ρ = sequence (evalS₀ σ ρ)

{-
evalS-ε : ∀{Γ Δ} (σ : Sub Δ ε) (ρ : Env Γ Δ) → evalS σ ρ ≡ now ε
evalS-ε σ ρ = refl
-}

substitution-var : ∀{Γ Δ Δ′ a} (x : Var Γ a) (σ : Sub Δ Γ) (ρ : Env Δ′ Δ) →
  a C∋ (lookup x <$> evalS σ ρ) ≃ eval (looks σ x) ρ
substitution-var zero    (σ , v) ρ = ≃trans (V∋≃trans _) {!!} {!bind-now!}
substitution-var (suc x) (σ , v) ρ = ≃trans (V∋≃trans _) {!!} (substitution-var x σ ρ)

{-
-- substitution-var {Δ′ = ε} x σ ρ = {!!}
-- substitution-var {Δ′ = Δ′ , a} x σ ρ = {!!}
substitution-var {ε} () σ ρ
substitution-var {Γ , a} zero σ ρ = {!!}
  --  a C∋ lookup zero <$> evalS σ ρ ≃ eval (σ zero) ρ
substitution-var {Γ , a} (suc x) σ ρ = {!!}
-}

substitution : ∀{Γ Δ Δ′ a} (t : Tm Γ a) (σ : Sub Δ Γ) (ρ : Env Δ′ Δ) →
  a C∋ (eval t =<< evalS σ ρ) ≃ eval (sub σ t) ρ
substitution (var x) σ ρ = {!eval t!}
substitution (abs t) σ ρ = {!!}
substitution (app t t₁) σ ρ = {!substitution t σ ρ !}
-}

-- Extensional equality of typed terms (evaluate to bisimilar values).

_≃T_ : ∀{Γ a} (t t' : Tm Γ a) → Set
_≃T_ {Γ} {a} t t' =
  ∀ {Δ} {ρ ρ' : Env Δ Γ} (ρ≃ρ' : ρ ≃E ρ')
  → a C∋ (eval t ρ) ≃ (eval t' ρ')


-- Variables are related.


⟦var⟧ : ∀{Γ a} (x : Var Γ a) → var x ≃T var x
⟦var⟧ zero    {Δ} {ρ , v} {ρ' , v'} (ρ≃ρ' , v≃v') =
  delay≃ v now⇓ v' now⇓ v≃v'
⟦var⟧ (suc x) {Δ} {ρ , v} {ρ' , v'} (ρ≃ρ' , v≃v') = ⟦var⟧ x ρ≃ρ'


{-
-- Trivial lemma, if you think about it. (UNUSED)
sound-β : ∀ {Δ Γ a b} (t t' : Tm (Γ , a) b)
  {ρ ρ' : Env Δ Γ} (ρ≃ρ' : ρ ≃E ρ')
  {u u' : Val Δ a} (u≃u' : VLR a u u')
  → b C∋ (eval t    (ρ , u)) ≃ (eval t'    (ρ' , u'))
  → b C∋ (apply (lam t ρ) u) ≃ (apply (lam t' ρ') u')
sound-β t t' ρ≃ρ' u≃u' eq = ≃later (≃delay eq)
-}

-- something more generic might be useful...
abs' : ∀ {Δ Γ a b} (t t' : Tm (Γ , a) b) -- (t≡t' : t ≡βη t')
       {ρ ρ' : Env Δ Γ} (ρ≃ρ' : ρ ≃E ρ') →
       ∀{Δ′}(η : Ren Δ′ Δ){u u' : Val Δ′ a}(u≃u' : VLR a u u') → 
       (Delay (λ v v' → b V∋ v ≃ v') ∋ eval t (renenv η ρ , u) ≃ eval t' (renenv η ρ' , u')) →
       (Delay (λ v v' → b V∋ v ≃ v') ∋ later (beta t (renenv η ρ) u) ≃ later (beta t' (renenv η ρ') u'))
abs' t t' ρ≃ρ' η u≃u' (delay≃ a₁ a⇓ b₁ b⇓ rab) = delay≃ a₁ (later⇓ a⇓) b₁ (later⇓ b⇓) rab


⟦abs⟧ : ∀ {Δ Γ a b} (t t' : Tm (Γ , a) b) -- (t≡t' : t ≡βη t')
  {ρ ρ' : Env Δ Γ} (ρ≃ρ' : ρ ≃E ρ') →
  (∀{Δ′}(η : Ren Δ′ Δ){u u' : Val Δ′ a}(u≃u' : VLR a u u')
   → b C∋ (eval t (renenv η ρ , u)) ≃ (eval t' (renenv η ρ' , u'))) →
  (a ⇒ b) C∋ (now (lam t ρ)) ≃ (now (lam t' ρ'))
⟦abs⟧ t t' {ρ}{ρ'} ρ≃ρ' ih =
  delay≃ (lam t ρ) now⇓ (lam t' ρ') now⇓ (λ η u u' u≃u' -> abs' t t' ρ≃ρ' η u≃u' (ih η u≃u'))

{-
⟦abs⟧' : ∀ {Γ a b} {t t' : Tm (Γ , a) b} → t ≃T t' → abs t ≃T abs t'
⟦abs⟧' {t = t}{t'} t≃t' ρ≃ρ' = ⟦abs⟧ t t' ρ≃ρ' (λ η u≃u' → t≃t' (renE≃ η ρ≃ρ' , u≃u'))

⟦app⟧'' : ∀{Γ a b}{f f' : Val Γ (a ⇒ b)}{v v' : Val Γ a} →
       (a ⇒ b) V∋ f ≃ f' → a V∋ v ≃ v' → b C∋ apply f v ≃ apply f' v'
⟦app⟧'' {Γ}{a}{b}{f}{f'}{v}{v'} p q =
  subst (λ X → b C∋ apply f v ≃ apply X v')
        (renvalid f')
        (subst (λ X → b C∋ apply X v ≃ apply (renval renId f') v')
               (renvalid f)
               (p renId _ _ q))

mutual
  ⟦app⟧' : ∀{Γ a b}{f f' : Val Γ (a ⇒ b)}{v v' : Delay ∞ (Val Γ a)} →
          (a ⇒ b) V∋ f ≃ f' → a C∋ v ≃ v' →
          b C∋ v >>= apply f ≃ (v' >>= apply f')
  ⟦app⟧' p (≃now a⇓ b⇓ aRb) =
    ≃trans (V∋≃trans _)
           (bindlem (C∋≃refl _ (⟦app⟧'' p aRb)) a⇓) (≃trans (V∋≃trans _) (⟦app⟧'' p aRb) (≃sym (V∋≃sym _) (bindlem (C∋≃refl _ (≃sym (V∋≃sym _) (⟦app⟧'' p aRb))) b⇓)))
  ⟦app⟧' p (≃later ∞p) = ≃later (∞⟦app⟧' p ∞p)

  ∞⟦app⟧' : ∀{Γ a b}{f f' : Val Γ (a ⇒ b)}{v v' : ∞Delay ∞ (Val Γ a)} →
       (a ⇒ b) V∋ f ≃ f' → ∞Delay VLR a ∋ v ≃ v' →
       ∞Delay VLR b ∋ v ∞>>= apply f ≃ (v' ∞>>= apply f')
  ≃force (∞⟦app⟧' f p) = ⟦app⟧' f (≃force p)

mutual
  ⟦app⟧ : ∀{Γ a b}{f f' : Delay ∞ (Val Γ (a ⇒ b))}{v v' : Delay ∞ (Val Γ a)} →
          (a ⇒ b) C∋ f ≃ f' → a C∋ v ≃ v' →
          b C∋ (f >>= λ f → v >>= apply f) ≃ (f' >>= λ f' → v' >>= apply f')
  ⟦app⟧ (≃now a⇓ b⇓ aRb) q = ≃trans (V∋≃trans _) (bindlem (C∋≃refl _ (⟦app⟧' aRb q)) a⇓) (≃trans (V∋≃trans _) (⟦app⟧' aRb q) (≃sym (V∋≃sym _) (bindlem (C∋≃refl _ (≃sym (V∋≃sym _) (⟦app⟧' aRb q))) b⇓) ))
  ⟦app⟧ (≃later ∞p) q = ≃later (∞⟦app⟧ ∞p q)

  ∞⟦app⟧ : ∀{Γ a b}{f f' : ∞Delay ∞ (Val Γ (a ⇒ b))}{v v' : Delay ∞ (Val Γ a)} →
          ∞Delay VLR (a ⇒ b) ∋ f ≃ f' → Delay VLR a ∋ v ≃ v' →
          ∞Delay VLR b ∋ (f ∞>>= λ f → v >>= apply f) ≃ (f' ∞>>= λ f' → v' >>= apply f')
  ≃force (∞⟦app⟧ p q) = ⟦app⟧ (≃force p) q

-- did Andreas say not to do it this way?
-}

⟦app⟧ : ∀{Γ a b}{f f' : Delay ∞ (Val Γ (a ⇒ b))}{v v' : Delay ∞ (Val Γ a)} →
        (a ⇒ b) C∋ f ≃ f' → a C∋ v ≃ v' →
        b C∋ (f >>= λ f → v >>= apply f) ≃ (f' >>= λ f' → v' >>= apply f')
⟦app⟧ {v = u}{v' = u'} (delay≃ f f⇓ f' f'⇓ rff') (delay≃ v v⇓ v' v'⇓ rvv') =
  let delay≃ x x⇓ x' x'⇓ rxx' = rff' renId v v' rvv'
  in  delay≃ x
             (bind⇓ (λ f -> u >>= apply f) f⇓ (bind⇓ (apply f) v⇓ (subst (λ X -> apply X v ⇓ x) (renvalid f) x⇓)))
             x'
             (bind⇓ (λ f' -> u' >>= apply f') f'⇓ (bind⇓ (apply f') v'⇓ (subst (λ X -> apply X v' ⇓ x') (renvalid f') x'⇓)))
             rxx'

idext : ∀{Γ a}(t : Tm Γ a) → t ≃T t
idext (var x)   p = ⟦var⟧ x p
idext (abs t)   p = ⟦abs⟧ _ _ p (λ η q → idext t (renE≃ η p , q))
idext (app t u) p = ⟦app⟧ (idext t p) (idext u p)

{-
-- Equal terms evaluate to equal values.
fund : ∀{Γ a}{t t' : Tm Γ a} →
  (t≡t' : t ≡βη t') → t ≃T t'
fund (var≡ {x = x} refl) ρ≃ρ' =  ⟦var⟧ x ρ≃ρ'
fund (abs≡ t≡t') ρ≃ρ' = ⟦abs⟧' (fund t≡t') ρ≃ρ'
fund (app≡ eq eq₁) ρ≃ρ' = ⟦app⟧ (fund eq ρ≃ρ') (fund eq₁ ρ≃ρ')
fund (beta≡ {t = t}{u = u}){Δ}{ρ}{ρ'} ρ≃ρ' =
  {!idext t !}
fund (eta≡ {t = t}) ρ≃ρ' = {!(idext t ρ≃ρ') !}
fund (sym≡ eq) ρ≃ρ' = ≃sym (V∋≃sym _) (fund eq (≃Esym ρ≃ρ'))
fund (trans≡ eq eq₁) ρ≃ρ' = ≃trans (V∋≃trans _) (fund eq (≃Erefl ρ≃ρ')) (fund eq₁ ρ≃ρ')
fund (refl≡ {t = t}) {ρ = ρ}{ρ'} p = idext t p


-- -}
-- -}
-- -}
-- -}
