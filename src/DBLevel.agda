module DBLevel where

open import Data.Maybe using (Maybe; just; nothing) renaming (map to fmap)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (∃; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum using (_⊎_; [_,_]′) renaming (inj₁ to inl; inj₂ to inr)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality

open import Term

-- De Bruijn Level

Lev = ℕ

{-
lev≤ : ∀ {Γ Δ} (η : Γ ≤ Δ) (x : Lev) → Lev
lev≤ ε        x = x -- dont care
lev≤ (weak η) x = lev≤ η x
lev≤ (lift {Γ = Γ} {Δ = Δ} η) x with x ≟ len Δ
... | yes _ = len Γ
... | no  _ = x
  -- the last variable is affected by lift
  -- if x = |Δ|, then the result should be |Γ|
-}

-- Valid de Bruijn levels.

data LookupLev : (x : Lev) (Γ : Cxt) (a : Ty) (i : Var Γ a) → Set where
  lookupZero : ∀ {Γ a} →
    LookupLev (len Γ) (Γ , a) a zero

  lookupSuc : ∀ {Γ a b x i} →
    LookupLev x Γ a i →
    LookupLev x (Γ , b) a (suc i)

record ValidLev (x : Lev) (Γ : Cxt) : Set where
  constructor validLev
  field
    {type } : Ty
    {index} : Var Γ type
    valid   : LookupLev x Γ type index

weakLev : ∀ {x Γ a} → ValidLev x Γ → ValidLev x (Γ , a)
weakLev (validLev d) = validLev (lookupSuc d)

strengthLev : ∀ {x Γ a} → ValidLev x (Γ , a) → (x ≡ len Γ) ⊎ ValidLev x Γ
strengthLev (validLev lookupZero)        = inl refl
strengthLev (validLev (lookupSuc valid)) = inr (validLev valid)

-- Looking up a de Bruijn level.

lookupLev : ∀ (x : Lev) (Γ : Cxt) → Dec (ValidLev x Γ)
lookupLev x   ε                                  = no λ { (validLev ()) }
lookupLev x  (Γ , a) with x ≟ len Γ
lookupLev ._ (Γ , a) | yes refl                  = yes (validLev lookupZero)
lookupLev x  (Γ , a) | no _  with lookupLev x Γ
lookupLev x  (Γ , a) | no ¬p | yes d             = yes (weakLev d)
lookupLev x  (Γ , a) | no ¬p | no ¬d             = no (λ d → [ ¬p , ¬d ]′ (strengthLev d))

-- lookupInv : lookupLev x Γ a zero
lev≤ : ∀ {Γ Δ a i} (η : Γ ≤ Δ) (x : Lev) (d : LookupLev x Δ a i) → Lev
lev≤ ε                        x         d            = x -- dont care
lev≤ (weak η)                 x         d            = lev≤ η x d -- lev≤ η ? x
lev≤ (lift {Γ = Γ} {Δ = Δ} η) .(len Δ)  lookupZero   = len Γ
lev≤ (lift η)                 x        (lookupSuc d) = lev≤ η x d
{-
lev≤ (lift {Γ = Γ} η) .0  lookupFound          = len Γ
lev≤ (lift η)         .0 (lookupZero d)        = lev≤ η 0 d
lev≤ (lift η)   .(suc x) (lookupSuc {x = x} d) = lev≤ η x d
-}
  -- the last variable is affected by lift
  -- if x = |Δ|, then the result should be |Γ|

-- Monotonicity.

lookupLev≤ : ∀ {Γ Δ x a i} (η : Γ ≤ Δ) (d : LookupLev x Δ a i) → LookupLev (lev≤ η x d) Γ a (var≤ η i)
lookupLev≤ ε ()
lookupLev≤ (lift η) lookupZero    = lookupZero
lookupLev≤ (lift η) (lookupSuc d) = lookupSuc (lookupLev≤ η d)
lookupLev≤ (weak η) d = lookupSuc (lookupLev≤ η d)

{-
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

lookupLev : ∀ (x : Lev) (Γ : Cxt) → Maybe (∃ λ a → Var Γ a)


-- Completeness of de Bruijn level lookup

{-
lookupCompl0 : ∀ {Γ a b i} → LookupLev zero Γ a i → lookupLev0 Γ b ≡ (a , suc i)
lookupCompl0 lookupZero    = refl
lookupCompl0 (lookupSuc d) = cong sucVar (lookupCompl0 d)
-}

lookupLast : ∀ Γ {a} → lookupLev (len Γ) (Γ , a) ≡ just (a , zero)
lookupLast ε       = refl
lookupLast (Γ , a) = {!!}

lookupCompl : ∀ {x Γ a i} → LookupLev x Γ a i → lookupLev x Γ ≡ just (a , i)
lookupCompl lookupZero                          = {!!}
lookupCompl (lookupSuc d)                       = {!!} -- cong just (lookupCompl0 d)
-- lookupCompl (lookupSuc  d) rewrite lookupCompl d = refl

{-
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
-}
-}
