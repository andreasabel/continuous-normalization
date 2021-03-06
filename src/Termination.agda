-- This module defines a type semantics capturing those values
-- for which readback terminates.
-- These are the values coming from normalizing terms.

module Termination where

open import Library
open import Delay
open import Syntax
open import RenamingAndSubstitution
open import Evaluation

-- "Termination" type semantics.

-- A type is interpreted as a predicate on values,
-- entailing that the value can be read back to a normal form
-- (in finite time).

V⟦_⟧ : ∀{Γ }(a : Ty) → Val ∞ Γ a → Set

-- At base type, the predicate holds if the value can be read back.

V⟦ ★     ⟧ t = readback t ⇓

-- At function type, we do the usual Krikpe function space.

V⟦ a ⇒ b ⟧ f = ∀{Δ} (ρ : Ren Δ _) (u : Val ∞ Δ a)

    (u⇓ : V⟦ a ⟧ u) → V⟦ b ⟧ (apply (renval ρ f) u)

-- The predicates are closed under strong bisimilarity of values

substV⟦⟧ : ∀{Γ} a {v v' : Val ∞ Γ a} → Val∋ v ≈ v' → V⟦ a ⟧ v → V⟦ a ⟧ v'
substV⟦⟧ ★       p (n , q) = _ , subst≈⇓ q (readback-cong _ p)
substV⟦⟧ (a ⇒ b) p q       ρ u u⇓ =
  substV⟦⟧ b (apply-cong (renval-cong ρ p) (≈reflVal u)) (q ρ u u⇓)

-- ... and under "later".

stepV⟦⟧ : ∀{Γ} b (v : ∞Val ∞ Γ b) → V⟦ b ⟧ (force v) → V⟦ b ⟧ (later v)
stepV⟦⟧ ★       v (n , p)  = n , later⇓ p
stepV⟦⟧ (a ⇒ b) v p ρ u u⇓ = stepV⟦⟧ b _ (p ρ u u⇓)

-- Pointwise lifting of type semantics to contexts,
-- which are interpreted as predicates on environments.

E⟦_⟧_ : ∀{Δ}(Γ : Cxt) → Env ∞ Δ Γ → Set
E⟦ ε ⟧     ε       = ⊤
E⟦ Γ , a ⟧ (ρ , v) = E⟦ Γ ⟧ ρ × V⟦ a ⟧ v

-- Convergence of readback is closed under renaming.

rennereadback⇓ : ∀{Γ Δ a}(η : Ren Δ Γ)(t : NeVal ∞ Γ a){n : Ne Γ a} →
                 nereadback t ⇓ n → nereadback (rennev η t) ⇓ rennen η n
rennereadback⇓ η t {n} p = subst≈⇓ (map⇓ (rennen η) p) (rennereadback η t)

rennfreadback⇓ : ∀{Γ Δ a}(η : Ren Δ Γ)(t : Val ∞ Γ a){n : Nf Γ a} →
                 readback t ⇓ n → readback (renval η t) ⇓ rennf η n
rennfreadback⇓ η t {n} p = subst≈⇓ (map⇓ (rennf η) p) (renreadback _ η t)

-- Termination semantics is closed under renaming.

renV⟦⟧ : ∀{Δ Δ′} a (η : Ren Δ′ Δ)(v : Val ∞ Δ a)(⟦v⟧ : V⟦ a ⟧ v) →
         V⟦ a ⟧ (renval η v)
renV⟦⟧ ★       η t (n , p) = rennf η n , rennfreadback⇓ η t p
renV⟦⟧ (a ⇒ b) η v ih ρ u u⇓ =
  substV⟦⟧ b (apply-cong (≈symVal (renvalcomp ρ η v)) (≈reflVal u))
             (ih (renComp ρ η) u u⇓)

renE⟦⟧ : ∀{Γ Δ Δ′} (η : Ren Δ′ Δ) (ρ : Env ∞ Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
         E⟦ Γ ⟧ (renenv η ρ)
renE⟦⟧ η ε       θ        = _
renE⟦⟧ η (ρ , v) (θ , ⟦v⟧) = renE⟦⟧ η ρ θ , renV⟦⟧ _ η v ⟦v⟧

-- Lemmata for the fundamental theorem.

⟦var⟧ : ∀{Δ Γ a} (x : Var Γ a) (ρ : Env ∞ Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
        V⟦ a ⟧ (lookup x ρ)
⟦var⟧ zero   (_ , v) (_ , v⇓) = v⇓
⟦var⟧(suc x) (ρ , _) (θ , _ ) = ⟦var⟧ x ρ θ

⟦abs⟧ : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env ∞ Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
        (∀{Δ′}(η : Ren Δ′ Δ)(u : Val ∞ Δ′ a)(u⇓ : V⟦ a ⟧ u) →
        V⟦ b ⟧ (eval t (renenv η ρ , u))) →
        V⟦ a ⇒ b ⟧ (lam t ρ)
⟦abs⟧ t ρ θ ih η u p = stepV⟦⟧ _ _ (ih η u p)

⟦app⟧ : ∀ {Δ a b} (f? : Val ∞ Δ (a ⇒ b))(u? : Val ∞ Δ a) →
        V⟦ a ⇒ b ⟧ f? → V⟦ a ⟧ u? → V⟦ b ⟧ (apply f? u?)
⟦app⟧ f? u? p q =
  substV⟦⟧ _ (apply-cong (renvalid f?) (≈reflVal u?) ) (p renId u? q)

-- Fundamental theorem for the termination semantics.

term : ∀ {Δ Γ a} (t : Tm Γ a) (ρ : Env ∞ Δ Γ) (θ : E⟦ Γ ⟧ ρ) → V⟦ a ⟧ (eval t ρ)
term (var x)   ρ θ = ⟦var⟧ x ρ θ
term (abs t)   ρ θ = ⟦abs⟧ t ρ θ (λ η u p →
  term t (renenv η ρ , u) (renE⟦⟧ η ρ θ , p))
term (app t u) ρ θ =
  ⟦app⟧ (eval t ρ) (eval u ρ) (term t ρ θ) (term u ρ θ)

-- Reflection and reification for termination semantics.

mutual
  reify : ∀{Γ} a (v : Val ∞ Γ a) → V⟦ a ⟧ v → readback v ⇓
  reify ★        _      p  = p
  reify (a ⇒ b)  f      ⟦f⟧ =
    let f0 = ⟦f⟧ (wkr renId)
                 (ne (var zero))
                 (reflect a (var zero) (var zero , now⇓))
        n , ⇓n = reify b _ f0
    in abs n , later⇓ (map⇓ abs ⇓n)

  reflect : ∀{Γ} a (w : NeVal ∞ Γ a) → nereadback w ⇓ → V⟦ a ⟧ (ne w)
  reflect ★ w (n , n⇓) = ne n , map⇓ ne n⇓
  reflect (a ⇒ b) w (m , w⇓m) η u ⟦u⟧ =
    let n , ⇓n = reify a u ⟦u⟧
        m′     = rennen η m
        ⇓m     = rennereadback⇓ η w w⇓m
        wu     = GNe.app (rennev η w) u
    in reflect b wu (app m′ n , map2⇓ app ⇓m ⇓n)

-- Reflecting variables into the semantics.

var↑ : ∀{Γ a}(x : Var Γ a) → V⟦ a ⟧ (ne (var x))
var↑ x = reflect _ (var x) (var x , now⇓)

-- Identity environment is in the semantics.

⟦ide⟧ : ∀ Γ → E⟦ Γ ⟧ (ide Γ)
⟦ide⟧ ε       = _
⟦ide⟧ (Γ , a) = renE⟦⟧ (wkr renId) (ide Γ) (⟦ide⟧ Γ) , var↑ zero

-- Normalization is reification after evaluation.
-- It terminates because of the fundamental theorem.

normalize : ∀ Γ a (t : Tm Γ a) → ∃ λ n → nf t ⇓ n
normalize Γ a t = reify a (eval t (ide Γ)) (term t (ide Γ) (⟦ide⟧ Γ))
