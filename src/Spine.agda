module Spine where

open import Term
open import Delay

-- Functoriality for RSpine

mapRSp : ∀ {V W : Ty → Set} →
  (∀ {d} → V d → W d) →
  ∀ {a c} → RSpine V a c → RSpine W a c
mapRSp f ε        = ε
mapRSp f (rs , r) = mapRSp f rs , f r

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

  mutual
    SpineF : (a c : Ty) → Set
    SpineF a c = SpineF' c a

    data SpineF' (c : Ty) : (a : Ty) → Set where
      []  : SpineF c c
      _∷_ : ∀ {a b} → V a → SpineF b c → SpineF (a ⇒ b) c


