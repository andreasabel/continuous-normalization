module Spine where

open import Library
open import Delay

infixr 6 _⇒_
infixl 1 _,_

-- Types and contexts.

data Ty : Set where
  ★   : Ty
  _⇒_ : (a b : Ty) → Ty

data Cxt : Set where
  ε   : Cxt
  _,_ : (Γ : Cxt) (a : Ty) → Cxt

-- Generic reversed Spines (last application available first).

data RSpine (V : Ty → Set) (a : Ty) : (c : Ty) → Set where
  ε   : RSpine V a a
  _,_ : ∀ {b c} → RSpine V a (b ⇒ c) → V b → RSpine V a c

-- Functoriality for RSpine

mapRSp : ∀ {V W : Ty → Set} →
  (∀ {d} → V d → W d) →
  ∀ {a c} → RSpine V a c → RSpine W a c
mapRSp f ε        = ε
mapRSp f (rs , r) = mapRSp f rs , f r

-- Functor law 1.

mapRSp-id : ∀ {V : Ty → Set}{f : ∀ {a} → V a → V a} →
  (∀ {a}   (r  : V a         ) → f r         ≡ r) →
   ∀ {a c} (rs : RSpine V a c) → mapRSp f rs ≡ rs
mapRSp-id f-id ε = refl
mapRSp-id f-id (rs , r) = cong₂ _,_ (mapRSp-id f-id rs) (f-id r)

-- Functor law 2.

mapRSp-∘ :  ∀ {V W X : Ty → Set}
  {f : ∀ {a} → W a → X a}
  {g : ∀ {a} → V a → W a}
  {h : ∀ {a} → V a → X a} →
  (∀ {a}   (r  : V a         ) → f (g r)                ≡ h r) →
   ∀ {a c} (rs : RSpine V a c) → mapRSp f (mapRSp g rs) ≡ mapRSp h rs
mapRSp-∘ fg ε        = refl
mapRSp-∘ fg (rs , r) = cong₂ _,_ (mapRSp-∘ fg rs) (fg r)

-- Traversability of RSpine

mapRSpM : ∀ {i} {V W : Ty → Set} → (∀ {d} → V d → Delay (W d) i) →
  ∀ {a c} → RSpine V a c → Delay (RSpine W a c) i
mapRSpM f ε        = return ε
mapRSpM f (rs , r) = _,_ <$> mapRSpM f rs <*> f r

-- Folding RSpine

foldRSp : ∀ {V W : Ty → Set} →
  (ap : ∀ {b c} → W (b ⇒ c) → V b → W c) →
  ∀ {a} → W a → ∀ {c} → RSpine V a c → W c
foldRSp {V = V} {W = W} ap {a = a} h = loop
  where
    loop : ∀ {c} → RSpine V a c → W c
    loop ε        = h
    loop (rs , r) = ap (loop rs) r

-- Currently not used: left-to-right spines.

module _ (V : Ty → Set) where

  data SpineF : (a c : Ty) → Set where
    []  : ∀ {c}                        → SpineF c c
    _∷_ : ∀ {a b c} → V a → SpineF b c → SpineF (a ⇒ b) c


