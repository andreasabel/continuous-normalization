{-# OPTIONS --copatterns --sized-types #-}

module Termination where

open import Library
open import Delay
open import Syntax
open import RenamingAndSubstitution
open import Evaluation

mutual
  V⟦_⟧ : ∀{Γ}(a : Ty) → Val Γ a → Set
  V⟦ ★ ⟧ (ne t) = nereadback t ⇓
  V⟦_⟧ {Γ = Γ} (a ⇒ b) f = ∀{Δ}(ρ : Ren Δ Γ)(u : Val Δ a)
    (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (apply (renval ρ f) u)

  C⟦_⟧_ : ∀{Γ}(a : Ty) → Delay ∞ (Val Γ a) → Set
  C⟦ a ⟧ v? = Delay⇓ V⟦ a ⟧ v? -- ∃ λ v → v? ⇓ v × V⟦ a ⟧ v

E⟦_⟧_ : ∀{Δ}(Γ : Cxt) → Env Δ Γ → Set
E⟦ ε ⟧     ε       = ⊤
E⟦ Γ , a ⟧ (ρ , v) = E⟦ Γ ⟧ ρ × V⟦ a ⟧ v


rennereadback⇓ : ∀{Γ Δ a}(η : Ren Δ Γ)(t : NeVal Γ a){n : Ne Γ a} →
              nereadback t ⇓ n → nereadback (rennev η t) ⇓ rennen η n
rennereadback⇓ η t {n} p = subst≈⇓ (map⇓ (rennen η) p) (rennereadback η t)

renV⟦⟧ : ∀{Δ Δ′} a (η : Ren Δ′ Δ)(v : Val Δ a)(⟦v⟧ : V⟦ a ⟧ v) → V⟦ a ⟧ (renval η v)
renV⟦⟧ ★       η (ne t) (n , p)        = rennen η n , rennereadback⇓ η t p
renV⟦⟧ (a ⇒ b) η v      ih       ρ u u⇓ =
  let delay⇓ v′ v⇓ pv = ih (renComp ρ η) u u⇓
      v⇓′ = (subst (λ X → apply X u ⇓ Delay⇓.a (ih (renComp ρ η) u u⇓))
                 ((sym (renvalcomp ρ η v)))
                 v⇓)
  in  delay⇓ v′ v⇓′ pv


renE⟦⟧ : ∀{Γ Δ Δ′} (η : Ren Δ′ Δ) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) → E⟦ Γ ⟧ (renenv η ρ)
renE⟦⟧ η ε       θ        = _
renE⟦⟧ η (ρ , v) (θ , ⟦v⟧) = renE⟦⟧ η ρ θ , renV⟦⟧ _ η v ⟦v⟧


⟦var⟧ : ∀{Δ Γ a} (x : Var Γ a) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
            C⟦ a ⟧ (now (lookup x ρ))
⟦var⟧ zero   (_ , v) (_ , v⇓) = delay⇓ v now⇓ v⇓
⟦var⟧(suc x) (ρ , _) (θ , _ ) = ⟦var⟧ x ρ θ


sound-β : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (u : Val Δ a) →
          C⟦ b ⟧ (eval t  (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)
sound-β t ρ u (delay⇓ v v⇓ ⟦v⟧) = delay⇓ v (later⇓ v⇓) ⟦v⟧


⟦abs⟧ : ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
  (∀{Δ′}(η : Ren Δ′ Δ)(u : Val Δ′ a)(u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (eval t (renenv η ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))
⟦abs⟧ t ρ θ ih = delay⇓ (lam t ρ) now⇓ (λ η u p → sound-β t (renenv η ρ) u (ih η u p))


⟦app⟧ : ∀ {Δ a b} {f? : Delay _ (Val Δ (a ⇒ b))} {u? : Delay _ (Val Δ a)} →
          C⟦ a ⇒ b ⟧ f? → C⟦ a ⟧ u? → C⟦ b ⟧ (f? >>= λ f → u? >>= apply f)
⟦app⟧ {u? = u?} (delay⇓ f f⇓ ⟦f⟧) (delay⇓ u u⇓ ⟦u⟧) =
  let delay⇓ v v⇓ ⟦v⟧ = ⟦f⟧ renId u ⟦u⟧
      v⇓′          = bind⇓ (λ f′ → u? >>= apply f′)
                    f⇓
                    (bind⇓ (apply f)
                          u⇓
                          (subst (λ X → apply X u ⇓ v)
                                 (renvalid f)
                                 v⇓))
  in  delay⇓ v v⇓′ ⟦v⟧


term : ∀ {Δ Γ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) → C⟦ a ⟧ (eval t ρ)
term (var x)   ρ θ = ⟦var⟧ x ρ θ
term (abs t)   ρ θ = ⟦abs⟧ t ρ θ (λ η u p →
  term t (renenv η ρ , u) (renE⟦⟧ η ρ θ , p))
term (app t u) ρ θ = ⟦app⟧ (term t ρ θ) (term u ρ θ)


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

nf : ∀{Γ a}(t : Tm Γ a) → Delay ∞ (Nf Γ a)
nf t = eval t (ide _) >>= readback

normalize : ∀ Γ a (t : Tm Γ a) → ∃ λ n → nf t ⇓ n
normalize Γ a t = let delay⇓ v v⇓ ⟦v⟧ = term t (ide Γ) (⟦ide⟧ Γ)
                      n , ⇓n      = reify a v ⟦v⟧
                  in  n , bind⇓ readback v⇓ ⇓n
