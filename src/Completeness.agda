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
  -- ★ V∋ ne t ~ ne t' = nereadback t ~ nereadback t'
  _V∋_~_         ★       (ne t) (ne t') = nereadback t ~ nereadback t'
  _V∋_~_ {Γ = Γ} (a ⇒ b) f     f'       = ∀{Δ}(ρ : Ren Δ Γ)(u u' : Val Δ a)
    (u~u' : a V∋ u ~ u') → b C∋ (apply (renval ρ f) u) ~ (apply (renval ρ f') u')

  VLR : ∀{Γ}(a : Ty) (v v' : Val Γ a) → Set
  VLR a v v' = _V∋_~_ a v v'

  -- Value computations v? and w? are related at type a.

  _C∋_~_ : ∀{Γ}(a : Ty) (v? w? : Delay ∞ (Val Γ a)) → Set
  a C∋ v? ~ w? = Delay (VLR a) ∋ v? ~ w?

-- Environments ρ and ρ' are related.

_~E_ : ∀{Γ Δ} (ρ ρ' : Env Δ Γ) → Set
ε       ~E ε         = ⊤
(ρ , v) ~E (ρ' , v') = (ρ ~E ρ') × (VLR _ v v')

-- Closure under renaming

renV~ : ∀{Δ Δ′} a (η : Ren Δ′ Δ) {v v' : Val Δ a} (v~v' : VLR a v v') → VLR a (renval η v) (renval η v')
renV~ = {!!}

renE~ : ∀{Γ Δ Δ′} (η : Ren Δ′ Δ) {ρ ρ' : Env Δ Γ} (ρ~ρ' : ρ ~E ρ') → (renenv η ρ) ~E (renenv η ρ')
renE~ η {ε} {ε} ρ~ρ' = _
renE~ η {ρ , v} {ρ' , v'} (ρ~ρ' , v~v') = (renE~ η ρ~ρ') , (renV~ _ η v~v')

-- Substitution lemma.

DEnv : ∀ Γ Δ → Set
DEnv Γ Δ = ∀{a} → Var Δ a → Delay ∞ (Val Γ a)

evalS : ∀{Γ Δ Δ′} (σ : Sub Δ Δ′) (ρ : Env Γ Δ) → DEnv Γ Δ′
evalS σ ρ = λ x → eval (σ x) ρ


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
completeness (app≡ eq eq₁) ρ~ρ' = {!!}
completeness beta≡ ρ~ρ' = {!!}
completeness eta≡ ρ~ρ' = {!!}
completeness (sym≡ eq) ρ~ρ' = {!!}
completeness (trans≡ eq eq₁) ρ~ρ' = {!!}
