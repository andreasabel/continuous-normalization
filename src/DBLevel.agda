module DBLevel where

open import Library
open import Term

-- De Bruijn Level

Lev = ℕ

-- Connection between de Bruijn indices and levels.

data LookupLev {a : Ty} : (x : Lev) (Γ : Cxt) (i : Var Γ a) → Set where
  lookupZero : ∀ {Γ} →
    LookupLev (len Γ) (Γ , a) zero

  lookupSuc : ∀ {Γ b x i} →
    LookupLev x Γ i →
    LookupLev x (Γ , b) (suc i)

-- Monotonicity.

lev≤ : ∀ {Γ Δ a} {i : Var Δ a} (η : Γ ≤ Δ) (x : Lev) (d : LookupLev x Δ i) → Lev
lev≤ id                       x         d            = x -- dont care
lev≤ (weak η)                 x         d            = lev≤ η x d -- lev≤ η ? x
lev≤ (lift {Γ = Γ} {Δ = Δ} η) .(len Δ)  lookupZero   = len Γ
lev≤ (lift η)                 x        (lookupSuc d) = lev≤ η x d
  -- the last variable is affected by lift
  -- if x = |Δ|, then the result should be |Γ|

lookupLev≤ : ∀ {Γ Δ x a} {i : Var Δ a} (η : Γ ≤ Δ) (d : LookupLev x Δ i) → LookupLev (lev≤ η x d) Γ (var≤ η i)
lookupLev≤ id        d            = d
lookupLev≤ (weak η)  d            = lookupSuc (lookupLev≤ η d)
lookupLev≤ (lift η)  lookupZero   = lookupZero
lookupLev≤ (lift η) (lookupSuc d) = lookupSuc (lookupLev≤ η d)

-- First functor law.

lev≤-id : ∀ {Δ a} {i : Var Δ a} (x : Lev) (d : LookupLev x Δ i) → lev≤ id x d ≡ x
lev≤-id x d = refl

lookupLev≤-id : ∀ {Γ x a} {i : Var Γ a} (d : LookupLev x Γ i) → lookupLev≤ id d ≡ d
lookupLev≤-id d = refl

-- Second functor law.

lev≤-• : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃)
  {i : Var Δ₃ a} (x : Lev) (d : LookupLev x Δ₃ i) →
  lev≤ η (lev≤ η' x d) (lookupLev≤ η' d) ≡ lev≤ (η • η') x d
lev≤-• id       η'        x   d            = refl
lev≤-• (weak η) η'        x   d            = lev≤-• η η' x d
lev≤-• (lift η) id        x   d            = refl
lev≤-• (lift η) (weak η') x   d            = lev≤-• η η' x d
lev≤-• (lift η) (lift η') ._  lookupZero   = refl
lev≤-• (lift η) (lift η') x  (lookupSuc d) = lev≤-• η η' x d

lookupLev≤-• : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃)
  {i : Var Δ₃ a} {x : Lev} (d : LookupLev x Δ₃ i) →

      lookupLev≤ η (lookupLev≤ η' d) ≅

      lookupLev≤ (η • η') d

lookupLev≤-• id       η'        d = refl
lookupLev≤-• (weak η) η'        d = {! hcong lookupSuc {!(lookupLev≤-• η η' d)!}!}
lookupLev≤-• (lift η) id        d = refl
lookupLev≤-• (lift η) (weak η') d = {!hcong lookupSuc (lookupLev≤-• η η' d)!}
lookupLev≤-• (lift η) (lift η') lookupZero = refl
lookupLev≤-• (lift η) (lift η') (lookupSuc d) = {!hcong lookupSuc (lookupLev≤-• η η' d)!}

{-
-- Need heterogeneous equality for that:

lookupLev≤-• : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃)
  {i : Var Δ₃ a} {x : Lev} (d : LookupLev x Δ₃ i) →

  _≡_ {A = LookupLev (lev≤ (η • η') x d) Δ₁ (var≤ (η • η') i) }
    (subst (λ z → LookupLev z Δ₁ (var≤ (η • η') i)) (lev≤-• η η' x d)
     (subst (λ z → LookupLev (lev≤ η (lev≤ η' x d) (lookupLev≤ η' d)) Δ₁ z) (var≤-• η η' i)

      (lookupLev≤ η (lookupLev≤ η' d))))

      (lookupLev≤ (η • η') d)

lookupLev≤-• id η' d = refl
lookupLev≤-• (weak η) η' d = {! cong lookupSuc (lookupLev≤-• η η' d)!}
lookupLev≤-• (lift η) id d = refl
lookupLev≤-• (lift η) (weak η') d = {!!}
lookupLev≤-• (lift η) (lift η') d = {!!}
-}

-- Valid de Bruijn levels.

record ValidLev (x : Lev) (Γ : Cxt) : Set where
  constructor validLev
  field
    {type } : Ty
    {index} : Var Γ type
    valid   : LookupLev x Γ index
open ValidLev public

strengthLev : ∀ {x Γ a} → ValidLev x (Γ , a) → (x ≡ len Γ) ⊎ ValidLev x Γ
strengthLev (validLev lookupZero)        = inl refl
strengthLev (validLev (lookupSuc valid)) = inr (validLev valid)

-- Monotonicity.

weakLev : ∀ {x Γ a} → ValidLev x Γ → ValidLev x (Γ , a)
weakLev (validLev d) = validLev (lookupSuc d)

validLev≤ : ∀ {Γ Δ x} (η : Γ ≤ Δ) (d : ValidLev x Δ) → ValidLev (lev≤ η x (valid d)) Γ
validLev≤ η (validLev d) = validLev (lookupLev≤ η d)

-- Looking up a de Bruijn level.

lookupLev : ∀ (x : Lev) (Γ : Cxt) → Dec (ValidLev x Γ)
lookupLev x   ε                                  = no λ { (validLev ()) }
lookupLev x  (Γ , a) with x ≟ len Γ
lookupLev ._ (Γ , a) | yes refl                  = yes (validLev lookupZero)
lookupLev x  (Γ , a) | no _  with lookupLev x Γ
lookupLev x  (Γ , a) | no ¬p | yes d             = yes (weakLev d)
lookupLev x  (Γ , a) | no ¬p | no ¬d             = no (λ d → [ ¬p , ¬d ]′ (strengthLev d))

-- Typed de Bruijn Levels.

record Lvl (Γ : Cxt) (a : Ty) : Set where
  constructor lvl
  field
    lev  : ℕ
    ind  : Var Γ a
    corr : LookupLev lev Γ ind
open Lvl public

-- Newest binding

newLvl : ∀ Γ {a} → Lvl (Γ , a) a
newLvl Γ = lvl (len Γ) zero lookupZero

-- Monotonicity

weakLvl : ∀ {Γ a b} (x : Lvl Γ a) → Lvl (Γ , b) a
weakLvl (lvl x i d) = lvl x (suc i) (lookupSuc d)

lvl≤ : ∀ {Γ Δ a} → (η : Γ ≤ Δ) (x : Lvl Δ a) → Lvl Γ a
lvl≤ η (lvl x i d) = lvl (lev≤ η x d) (var≤ η i) (lookupLev≤ η d)

-- First functor law.

lvl≤-id : ∀ {Δ a} (x : Lvl Δ a) → lvl≤ id x ≡ x
lvl≤-id x = refl

-- Second functor law.

lvl≤-• : ∀ {Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (x : Lvl Δ₃ a) →
  lvl≤ η (lvl≤ η' x) ≡ lvl≤ (η • η') x
lvl≤-• η η' (lvl x i d) = {!cong₃ (lev≤-• η η' x d) (var≤-• η η' i) (lookupLev≤-• η η' d) !}







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
