module DBLevel where

open import Data.Maybe using (Maybe; just; nothing) renaming (map to fmap)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality

open import Term

-- De Bruijn Level

Lev = ℕ

-- Valid de Bruijn levels.

data LookupLev : (x : Lev) (Γ : Cxt) (a : Ty) (i : Var Γ a) → Set where
  lookupFound : ∀ {a} →
    LookupLev zero (ε , a) a zero

  lookupZero : ∀ {Γ a b i} →
    LookupLev zero Γ a i →
    LookupLev zero (Γ , b) a (suc i)

  lookupSuc : ∀ {Γ a b x i} →
    LookupLev x Γ a i →
    LookupLev (suc x) (Γ , b) a (suc i)

-- Implementation of level lookup.

sucVar : ∀ {Γ a} → (∃ λ c → Var Γ c) → ∃ λ c → Var (Γ , a) c
sucVar (c , x) = (c , suc x)

-- Lookup level 0 in context (Γ , a): always succeeds.

lookupLev0 : (Γ : Cxt) (a : Ty) → ∃ λ c → Var (Γ , a) c
lookupLev0  ε      a = (a , zero)
lookupLev0 (Γ , b) a = sucVar (lookupLev0 Γ b)

-- Lookup level x in context Γ: may fail (unbound variable).

lookupLev : ∀ (x : Lev) (Γ : Cxt) → Maybe (∃ λ a → Var Γ a)
lookupLev x        ε      = nothing
lookupLev zero    (Γ , a) = just (lookupLev0 Γ a)
lookupLev (suc x) (Γ , a) = fmap sucVar (lookupLev x Γ)

-- Completeness of de Bruijn level lookup

lookupCompl0 : ∀ {Γ a b i} → LookupLev zero Γ a i → lookupLev0 Γ b ≡ (a , suc i)
lookupCompl0 lookupFound    = refl
lookupCompl0 (lookupZero d) = cong sucVar (lookupCompl0 d)

lookupCompl : ∀ {x Γ a i} → LookupLev x Γ a i → lookupLev x Γ ≡ just (a , i)
lookupCompl lookupFound                          = refl
lookupCompl (lookupZero d)                       = cong just (lookupCompl0 d)
lookupCompl (lookupSuc  d) rewrite lookupCompl d = refl

-- Soundness of de Bruijn level lookup

lookupSound0 : ∀ Γ {a b i} → lookupLev0 Γ b ≡ (a , suc i) → LookupLev zero Γ a i
lookupSound0 ε ()
lookupSound0 (ε , a)       refl = lookupFound
lookupSound0 ((Γ , a) , b) refl = lookupZero (lookupSound0  (Γ , a) {b = b} refl)

lookupSound : ∀ x Γ {a i} → lookupLev x Γ ≡ just (a , i) → LookupLev x Γ a i
lookupSound x        ε      ()
lookupSound zero    (Γ , a) refl = lookupSound0 (Γ , a) {b = a} refl
lookupSound (suc x) (Γ , a) d    with lookupLev x Γ | inspect (lookupLev x) Γ
lookupSound (suc x) (Γ , a) refl | just _  | [ eq ] = lookupSuc (lookupSound x Γ eq)
lookupSound (suc x) (Γ , a) ()   | nothing | _
