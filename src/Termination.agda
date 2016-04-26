{-# OPTIONS --copatterns --sized-types #-}

module Termination where

open import Library
open import Delay
open import Syntax
open import RenamingAndSubstitution
open import Evaluation

V⟦_⟧ : ∀{Γ }(a : Ty) → Val ∞ Γ a → Set
V⟦ ★     ⟧ t = readback t ⇓
V⟦ a ⇒ b ⟧ f = ∀{Δ}(ρ : Ren Δ _)(u : Val ∞ Δ a)
    (u⇓ : V⟦ a ⟧ u) → V⟦ b ⟧ (apply (renval ρ f) u)

-- can't use subst anymore, so need a special thing for substituting
-- by strong bisim.

substV⟦⟧ : ∀{Γ} a {v v' : Val ∞ Γ a} → Val∋ v ≈ v' → V⟦ a ⟧ v → V⟦ a ⟧ v'
substV⟦⟧ ★       p (n , q) = _ , subst≈⇓ q (readback-cong _ p) 
substV⟦⟧ (a ⇒ b) p q       ρ u u⇓ =
  substV⟦⟧ b (apply-cong (renval-cong ρ p) (≈reflVal u)) (q ρ u u⇓)

stepV⟦⟧ : ∀{Γ} b (v : ∞Val ∞ Γ b) → V⟦ b ⟧ (∞Val.force v) → V⟦ b ⟧ (later v)
stepV⟦⟧ ★       v (n , p)  = n , later⇓ p
stepV⟦⟧ (a ⇒ b) v p ρ u u⇓ = stepV⟦⟧ b _ (p ρ u u⇓)

{-
infix 8 C⟦_⟧_ E⟦_⟧_
C⟦_⟧_ : ∀{Γ}(a : Ty) → Delay ∞ (Val Γ a) → Set
C⟦ a ⟧ v? = Delay⇓ V⟦ a ⟧ v? -- ∃ λ v → v? ⇓ v × V⟦ a ⟧ v
-}

E⟦_⟧_ : ∀{Δ}(Γ : Cxt) → Env ∞ Δ Γ → Set
E⟦ ε ⟧     ε       = ⊤
E⟦ Γ , a ⟧ (ρ , v) = E⟦ Γ ⟧ ρ × V⟦ a ⟧ v

{-
rennereadback⇓ : ∀{Γ Δ a}(η : Ren Δ Γ)(t : NeVal ∞ Γ a){n : Ne Γ a} →
              nereadback t ⇓ n → nereadback (rennev η t) ⇓ rennen η n
rennereadback⇓ η t {n} p = subst≈⇓ (map⇓ (rennen η) p) (rennereadback η t)
-}

rennfreadback⇓ : ∀{Γ Δ a}(η : Ren Δ Γ)(t : Val ∞ Γ a){n : Nf Γ a} →
              readback t ⇓ n → readback (renval η t) ⇓ rennf η n
rennfreadback⇓ η t {n} p = subst≈⇓ (map⇓ (rennf η) p) (renreadback _ η t)

renV⟦⟧ : ∀{Δ Δ′} a (η : Ren Δ′ Δ)(v : Val ∞ Δ a)(⟦v⟧ : V⟦ a ⟧ v) →
         V⟦ a ⟧ (renval η v)
renV⟦⟧ (a ⇒ b) η v ih ρ u u⇓ =
  substV⟦⟧ b (apply-cong (≈symVal (renvalcomp ρ η v)) (≈reflVal u))
             (ih (renComp ρ η) u u⇓) 
renV⟦⟧ ★       η t (n , p) = rennf η n , rennfreadback⇓ η t p

renE⟦⟧ : ∀{Γ Δ Δ′} (η : Ren Δ′ Δ) (ρ : Env ∞ Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
         E⟦ Γ ⟧ (renenv η ρ)
renE⟦⟧ η ε       θ        = _
renE⟦⟧ η (ρ , v) (θ , ⟦v⟧) = renE⟦⟧ η ρ θ , renV⟦⟧ _ η v ⟦v⟧

⟦var⟧ : ∀{Δ Γ a} (x : Var Γ a) (ρ : Env ∞ Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
            V⟦ a ⟧ (lookup x ρ)
⟦var⟧ zero   (_ , v) (_ , v⇓) = v⇓
⟦var⟧(suc x) (ρ , _) (θ , _ ) = ⟦var⟧ x ρ θ

sound-β : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env ∞ Δ Γ) (u : Val ∞ Δ a) →
          V⟦ b ⟧ (eval t  (ρ , u)) → V⟦ b ⟧ (apply (lam t ρ) u)
sound-β t ρ u p = stepV⟦⟧ _ _ p

⟦abs⟧ : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env ∞ Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
        (∀{Δ′}(η : Ren Δ′ Δ)(u : Val ∞ Δ′ a)(u⇓ : V⟦ a ⟧ u) →
         V⟦ b ⟧ (eval t (renenv η ρ , u))) →
        V⟦ a ⇒ b ⟧ (lam t ρ)
⟦abs⟧ t ρ θ ih η u p = sound-β t (renenv η ρ) u (ih η u p)

⟦app⟧ : ∀ {Δ a b} (f? : Val ∞ Δ (a ⇒ b))(u? : Val ∞ Δ a) →
          V⟦ a ⇒ b ⟧ f? → V⟦ a ⟧ u? → V⟦ b ⟧ (apply f? u?)
⟦app⟧ f? u? p q =
  substV⟦⟧ _ (apply-cong (renvalid f?) (≈reflVal u?) ) (p renId u? q)

term : ∀ {Δ Γ a} (t : Tm Γ a) (ρ : Env ∞ Δ Γ) (θ : E⟦ Γ ⟧ ρ) → V⟦ a ⟧ (eval t ρ)
term (var x)   ρ θ = ⟦var⟧ x ρ θ
term (abs t)   ρ θ = ⟦abs⟧ t ρ θ (λ η u p →
  term t (renenv η ρ , u) (renE⟦⟧ η ρ θ , p))
term (app t u) ρ θ =
  ⟦app⟧ (eval t ρ) (eval u ρ) (term t ρ θ) (term u ρ θ)

{-
mutual
  reify : ∀{Γ} a (v : Val Γ a) → V⟦ a ⟧ v → readback v ⇓
  reify ★        (ne _) (m , ⇓m) = ne m , map⇓ ne ⇓m
  reify (a ⇒ b)  f      ⟦f⟧      =
    let u           = ne (var zero)
        ⟦u⟧          = reflect a (var zero) (var zero , now⇓)
        delay⇓ v v⇓ ⟦v⟧ = ⟦f⟧ (wkr renId) u ⟦u⟧
        n , ⇓n = reify b v ⟦v⟧
        ⇓λn    = later⇓ (bind⇓ (λ x → now (abs x))
                               (bind⇓ readback v⇓ ⇓n)
                               now⇓)
    in  abs n , ⇓λn

  reflect : ∀{Γ} a (w : NeVal Γ a) → nereadback w ⇓ → V⟦ a ⟧ (ne w)
  reflect ★ w w⇓ = w⇓
  reflect (a ⇒ b) w (m , w⇓m) η u ⟦u⟧ =
    let n , ⇓n = reify a u ⟦u⟧
        m′      = rennen η m
        ⇓m     = rennereadback⇓ η w w⇓m
        wu     = app (rennev η w) u
        ⟦wu⟧   = reflect b wu (app m′ n ,
                   bind⇓ (λ m → app m <$> readback u)
                        ⇓m
                        (bind⇓ (λ n → now (app m′ n)) ⇓n now⇓))
    in  delay⇓ (ne wu) now⇓ ⟦wu⟧


var↑ : ∀{Γ a}(x : Var Γ a) → V⟦ a ⟧ (ne (var x))
var↑ x = reflect _ (var x) (var x , now⇓)


⟦ide⟧ : ∀ Γ → E⟦ Γ ⟧ (ide Γ)
⟦ide⟧ ε       = _
⟦ide⟧ (Γ , a) = renE⟦⟧ (wkr renId) (ide Γ) (⟦ide⟧ Γ) , var↑ zero

normalize : ∀ Γ a (t : Tm Γ a) → ∃ λ n → nf t ⇓ n
normalize Γ a t = let delay⇓ v v⇓ ⟦v⟧ = term t (ide Γ) (⟦ide⟧ Γ)
                      n , ⇓n      = reify a v ⟦v⟧
                  in  n , bind⇓ readback v⇓ ⇓n
-}
