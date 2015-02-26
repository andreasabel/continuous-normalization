{-# OPTIONS --copatterns --sized-types #-}

module Completeness where

open import Library
open import Delay
open import WeakBisim
open import Syntax
open import RenamingAndSubstitution
open import Evaluation
open import EquationalTheory

mutual

  -- Values v and v' are related at type a.

  _V∋_~_ : ∀{Γ}(a : Ty) (v v' : Val Γ a) → Set
  _V∋_~_         ★       (ne n) (ne n') = nereadback n ~ nereadback n'
  _V∋_~_ {Γ = Γ} (a ⇒ b) f     f'       = ∀{Δ}(ρ : Ren Δ Γ)(u u' : Val Δ a)
    (u~u' : a V∋ u ~ u') → b C∋ (apply (renval ρ f) u) ~ (apply (renval ρ f') u')

  VLR : ∀{Γ}(a : Ty) (v v' : Val Γ a) → Set
  VLR a v v' = _V∋_~_ a v v'

  -- Value computations v? and w? are related at type a.

  _C∋_~_ : ∀{Γ}(a : Ty) (v? w? : Delay ∞ (Val Γ a)) → Set
  a C∋ v? ~ w? = Delay (VLR a) ∋ v? ~ w?


V∋~sym : ∀{Γ}(a : Ty){v v' : Val Γ a} →
           a V∋ v ~ v' → a V∋ v' ~ v
V∋~sym ★       {ne _}{ne _} p  = ~sym sym p
V∋~sym (a ⇒ b)              p ρ u u' q =
  ~sym (V∋~sym b) (p ρ u' u (V∋~sym a q)) 

V∋~trans : ∀{Γ}(a : Ty){v v' v'' : Val Γ a} →
           a V∋ v ~ v' → a V∋ v' ~ v'' → a V∋ v ~ v''
V∋~trans ★ {ne n}{ne n'}{ne n''} p q = ~trans trans p q
V∋~trans (a ⇒ b) p q ρ u u' r =
  ~trans {R = VLR b} (V∋~trans b)
                     (p ρ u u (V∋~trans a r (V∋~sym a r)))
                     (q ρ u u' r)             

V∋~refl : ∀{Γ}(a : Ty){v v' : Val Γ a} →
           a V∋ v ~ v' → a V∋ v ~ v
V∋~refl a p = V∋~trans a p (V∋~sym a p)


-- Environments ρ and ρ' are related.

_~E_ : ∀{Γ Δ} (ρ ρ' : Env Δ Γ) → Set
ε       ~E ε         = ⊤
(ρ , v) ~E (ρ' , v') = (ρ ~E ρ') × (VLR _ v v')

-- Closure under renaming

renV~ : ∀{Δ Δ′} a (η : Ren Δ′ Δ) {v v' : Val Δ a} (v~v' : VLR a v v') →
        VLR a (renval η v) (renval η v')
renV~ ★       η {ne n}{ne n'} p =
  ~trans trans (~sym sym $ ≈→~ (rennereadback η n))
         (~trans trans (map~ (rennen η) (λ _ _ → cong (rennen η)) p)
                 (≈→~ (rennereadback η n')))
renV~ (a ⇒ b) η p ρ u u' q =
  ~trans (V∋~trans b) {!≈→~!} (~trans (V∋~trans b) (p (renComp ρ η) u u' q) {!!})

renE~ : ∀{Γ Δ Δ′} (η : Ren Δ′ Δ) {ρ ρ' : Env Δ Γ} (ρ~ρ' : ρ ~E ρ') → (renenv η ρ) ~E (renenv η ρ')
renE~ η {ε} {ε} ρ~ρ' = _
renE~ η {ρ , v} {ρ' , v'} (ρ~ρ' , v~v') = (renE~ η ρ~ρ') , (renV~ _ η v~v')

-- Substitution lemma.

DEnv : ∀ Γ Δ → Set
DEnv Γ Δ = ∀{a} → Var Δ a → Delay ∞ (Val Γ a)

sequence : ∀{Γ} Δ → DEnv Γ Δ → Delay ∞ (Env Γ Δ)
sequence ε f = now ε
sequence (Δ , a) f = _,_ <$> sequence Δ (f ∘ suc) <*> f zero

evalS₀ : ∀{Γ Δ Δ′} (σ : Sub Δ Δ′) (ρ : Env Γ Δ) → DEnv Γ Δ′
evalS₀ σ ρ = λ x → eval (looks σ x) ρ

evalS : ∀{Γ Δ Δ′} (σ : Sub Δ Δ′) (ρ : Env Γ Δ) → Delay ∞ (Env Γ Δ′)
evalS {Δ′ = Δ′} σ ρ = sequence Δ′ (evalS₀ σ ρ)

evalS-ε : ∀{Γ Δ} (σ : Sub Δ ε) (ρ : Env Γ Δ) → evalS σ ρ ≡ now ε
evalS-ε σ ρ = refl

substitution-var : ∀{Γ Δ Δ′ a} (x : Var Γ a) (σ : Sub Δ Γ) (ρ : Env Δ′ Δ) →
  a C∋ (lookup x <$> evalS σ ρ) ~ eval (looks σ x) ρ
-- substitution-var {Δ′ = ε} x σ ρ = {!!}
-- substitution-var {Δ′ = Δ′ , a} x σ ρ = {!!}
substitution-var {ε} () σ ρ
substitution-var {Γ , a} zero σ ρ = {!!}
  --  a C∋ lookup zero <$> evalS σ ρ ~ eval (σ zero) ρ
substitution-var {Γ , a} (suc x) σ ρ = {!!}

substitution : ∀{Γ Δ Δ′ a} (t : Tm Γ a) (σ : Sub Δ Γ) (ρ : Env Δ′ Δ) →
  a C∋ (eval t =<< evalS σ ρ) ~ eval (sub σ t) ρ
substitution (var x) σ ρ = {!!}
substitution (abs t) σ ρ = {!!}
substitution (app t t₁) σ ρ = {!!}

-- Extensional equality of typed terms (evaluate to bisimilar values).

_~T_ : ∀{Γ a} (t t' : Tm Γ a) → Set
_~T_ {Γ} {a} t t' =
  ∀ {Δ} {ρ ρ' : Env Δ Γ} (ρ~ρ' : ρ ~E ρ')
  → a C∋ (eval t ρ) ~ (eval t' ρ')

-- Variables are related.

-- ⟦var⟧ : ∀{Δ Γ a} (x : Var Γ a) {ρ ρ' : Env Δ Γ} (ρ~ρ' : ρ ~E ρ') →
--             a C∋ (now (lookup x ρ)) ~ (now (lookup x ρ'))
⟦var⟧ : ∀{Γ a} (x : Var Γ a) → var x ~T var x
⟦var⟧ zero    {Δ} {ρ , v} {ρ' , v'} (ρ~ρ' , v~v') = ~now now⇓ now⇓ v~v'
⟦var⟧ (suc x) {Δ} {ρ , v} {ρ' , v'} (ρ~ρ' , v~v') = ⟦var⟧ x ρ~ρ'

-- Trivial lemma, if you think about it. (UNUSED)
sound-β : ∀ {Δ Γ a b} (t t' : Tm (Γ , a) b)
  {ρ ρ' : Env Δ Γ} (ρ~ρ' : ρ ~E ρ')
  {u u' : Val Δ a} (u~u' : VLR a u u')
  → b C∋ (eval t    (ρ , u)) ~ (eval t'    (ρ' , u'))
  → b C∋ (apply (lam t ρ) u) ~ (apply (lam t' ρ') u')
sound-β t t' ρ~ρ' u~u' eq = ~later (~delay eq)

⟦abs⟧ : ∀ {Δ Γ a b} (t t' : Tm (Γ , a) b) -- (t≡t' : t ≡βη t')
  {ρ ρ' : Env Δ Γ} (ρ~ρ' : ρ ~E ρ') →
  (∀{Δ′}(η : Ren Δ′ Δ){u u' : Val Δ′ a}(u~u' : VLR a u u')
   → b C∋ (eval t (renenv η ρ , u)) ~ (eval t' (renenv η ρ' , u'))) →
  (a ⇒ b) C∋ (now (lam t ρ)) ~ (now (lam t' ρ'))
⟦abs⟧ t t' {ρ}{ρ'} ρ~ρ' ih = ~now now⇓ now⇓ (λ η u u' u~u' → ~later (~delay (ih η u~u')))

⟦abs⟧' : ∀ {Γ a b} {t t' : Tm (Γ , a) b} → t ~T t' → abs t ~T abs t'
⟦abs⟧' {t = t}{t'} t~t' ρ~ρ' = ⟦abs⟧ t t' ρ~ρ' (λ η u~u' → t~t' (renE~ η ρ~ρ' , u~u'))

-- Equal terms evaluate to equal values.

-- completeness : ∀{Γ Δ a}{t t' : Tm Γ a} →
--   (eq : t ≡βη t') {ρ ρ' : Env Δ Γ} (θ : ρ ~E ρ') → a C∋ eval t ρ ~ eval t' ρ'
completeness : ∀{Γ a}{t t' : Tm Γ a} →
  (t≡t' : t ≡βη t') → t ~T t'
completeness (var≡ {x = x} refl) ρ~ρ' =  ⟦var⟧ x ρ~ρ'
completeness (abs≡ t≡t') ρ~ρ' = ⟦abs⟧' (completeness t≡t') ρ~ρ'
completeness (app≡ eq eq₁) ρ~ρ' = {!completeness eq ρ~ρ'!}
completeness beta≡ ρ~ρ' = {!!}
completeness eta≡ ρ~ρ' = {!!}
completeness (sym≡ eq) ρ~ρ' = {!!}
completeness (trans≡ eq eq₁) ρ~ρ' = {!!}
completeness refl≡ p = {!!}
