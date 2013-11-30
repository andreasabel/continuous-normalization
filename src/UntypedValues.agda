{-# OPTIONS --copatterns --sized-types #-}

module UntypedValues where

open import Function
open import Level using () renaming (zero to lzero; suc to lsuc)
open import Size

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to fmap)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality

open import Term
open import DelayError
open import Spine
open import DBLevel

-- Reversed list

data RList (A : Set) : Set where
  ε   : RList A
  _,_ : (rs : RList A) (r : A) → RList A

-- Values and environments

mutual
  data Env : (Γ : Cxt) → Set where
    ε   : Env ε
    _,_ : ∀ {Γ a} (ρ : Env Γ) (v : Val) → Env (Γ , a)

  data Val : Set where
    ne  : ∀         (x : Lev) (vs : ValSpine)      → Val
    lam : ∀ {Γ a b} (t : Tm (Γ , a) b) (ρ : Env Γ) → Val

  ValSpine = RList Val

lookup : ∀ {Γ a} → Var Γ a → Env Γ → Val
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

-- Lifting.

var0 : Val
var0 = ne 0 ε

liftEnv : ∀ {Γ a} → Env Γ → Env (Γ , a)
liftEnv ρ = ρ , var0

-- Call-by-value evaluation.

mutual
  〖_〗  : ∀ {i} {Γ : Cxt} {a : Ty} → Tm Γ a → Env Γ → Delay Val i
  〖 var x   〗 ρ = now (lookup x ρ)
  〖 abs t   〗 ρ = now (lam t ρ)
  〖 app t u 〗 ρ = apply* (〖 t 〗 ρ) (〖 u 〗 ρ)

  apply* : ∀ {i} → Delay Val i → Delay Val i → Delay Val i
  apply* f⊥ v⊥ = apply =<<2 f⊥ , v⊥

  apply : ∀ {i} → Val → Val → Delay Val i
  apply f v = later (∞apply f v)

  ∞apply : ∀ {i} → Val → Val → ∞Delay Val i
  force (∞apply (lam t ρ) v) = 〖 t 〗 (ρ , v)
  force (∞apply (ne x sp) v) = now (ne x (sp , v))

β-expand : ∀ {Γ a b} {t : Tm (Γ , a) b} {ρ : Env Γ} {u v : Val} →
  (h : 〖 t 〗 (ρ , u) ⇓ v) → apply (lam t ρ) u ⇓ v
β-expand h = later⇓ h

-- Check that something is at base type.

ensure★ : ∀ {i}{V : Ty → Set} → ∃ V → Delay (V ★) i
ensure★ (★       , x) = now x
ensure★ ((_ ⇒ _) , _) = fail

NfSpine : (Γ : Cxt) (a : Ty) → Set
NfSpine Γ a = ∃ λ c → RSpine (Nf Γ) a c

mutual

  -- Type-directed readback.

  readback : ∀ {i} Γ a → Val → Delay (Nf Γ a) i
  readback Γ (a ⇒ b) v   = lam <$> (readback (Γ , a) b =<< apply v (var0 (length Γ)))
  readback Γ ★ (lam t ρ) = fail
  readback Γ ★ (ne x vs) = case lookupLev x Γ of λ
    { nothing        -> fail
    ; (just (a , i)) -> ne i <$> (ensure★ =<< readbackSp Γ a vs)
    }

  -- Structural readback of spines.

  readbackSp : ∀ {i} Γ (a : Ty) → RList Val → Delay (NfSpine Γ a) i
  readbackSp Γ a ε        = now (a , ε)
  readbackSp Γ a (vs , v) = later ∘ readbackApp Γ v =<< readbackSp Γ a vs

  readbackApp : ∀ {i} {a} Γ → Val → NfSpine Γ a → ∞Delay (NfSpine Γ a) i
  force (readbackApp Γ v (★ , vs))     = fail
  force (readbackApp Γ v (b ⇒ c , vs)) = (λ v → c , (vs , v)) <$> readback Γ b v

-- Readable values

mutual

  data CanRead (Γ : Cxt) : (a : Ty) (v : Val) → Set where

    canReadFun : ∀ {a b f v} →

      apply f var0 ⇓ v →
      CanRead (Γ , a) b v →
      ---------------------
      CanRead Γ (a ⇒ b) f

    canReadBase : ∀ {a x vs i} →

      LookupLev x Γ a i →
      CanReadSpine Γ a vs ★ →
      -----------------------
      CanRead Γ ★ (ne x vs)

  data CanReadSpine (Γ : Cxt) : (a : Ty) (vs : ValSpine) (c : Ty) → Set where

    canReadε : ∀ {a} →

      --------------------
      CanReadSpine Γ a ε a

    canReadApp : ∀ {a b c vs v} →

      CanReadSpine Γ a vs (b ⇒ c) →
      CanRead Γ b v →
      -----------------------------
      CanReadSpine Γ a (vs , v) c

-- Monotonicity

mutual
  canRead≤ : ∀ {Γ Δ a v} → (η : Γ ≤ Δ) (d : CanRead Δ a v) → CanRead Γ a v
  canRead≤ η (canReadFun x d) = canReadFun x (canRead≤ (lift η) d)
  canRead≤ η (canReadBase x d) = canReadBase {!!} (canReadSpine≤ η d)

  canReadSpine≤ : ∀ {Γ Δ a vs c} → (η : Γ ≤ Δ) (d : CanReadSpine Δ a vs c) → CanReadSpine Γ a vs c
  canReadSpine≤ η canReadε = canReadε
  canReadSpine≤ η (canReadApp d e) = canReadApp (canReadSpine≤ η d) (canRead≤ η e)

-- Type interpretation

mutual
  V⟦_⟧  : (a : Ty) → (Γ : Cxt) (v : Val) → Set
  V⟦ ★     ⟧ Γ v = CanRead Γ ★ v
  V⟦ a ⇒ b ⟧ Γ f = {u : Val} (u⇓ : V⟦ a ⟧ Γ u) → C⟦ b ⟧ Γ (apply f u)

  C⟦_⟧  : (a : Ty) → (Γ : Cxt) (v? : Delay Val ∞) → Set
  C⟦ a ⟧ Γ v? = ∃ λ v → v? ⇓ v × V⟦ a ⟧ Γ v


⟪_⟫_ : (Γ : Cxt) → Env Γ → Set
⟪ ε ⟫     ε       = ⊤
⟪ Γ , a ⟫ (ρ , v) = ⟪ Γ ⟫ ρ × V⟦ a ⟧ Γ v

{-

-- Type soundness

〖var〗 : ∀ {Γ a} (x : Var Γ a) (ρ : Env Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ Γ (now (lookup x ρ))
〖var〗 zero    (_ , v) (_ , v⇓) = v , now⇓ , v⇓
〖var〗 (suc x) (ρ , _) (θ , _ ) = 〖var〗 x ρ θ

sound-β : ∀ {Γ a b} {t : Tm (Γ , a) b} {ρ : Env Γ} {u : Val a} →

  C⟦ b ⟧ (〖 t 〗 (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)

sound-β (v , v⇓ , ⟦v⟧) = v , β-expand v⇓ , ⟦v⟧


〖abs〗 : ∀ {Γ a b} (t : Tm (Γ , a) b) (ρ : Env Γ) (θ : ⟪ Γ ⟫ ρ) →

  ({u : Val a} (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (〖 t 〗 (ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))

〖abs〗 t ρ θ ih = lam t ρ , now⇓ , λ u⇓ → sound-β (ih u⇓)

sound-app' : ∀ {a b} (f : Val (a ⇒ b)) →
  {u* : Delay (Val a) _} {u : Val a} (u⇓ : u* ⇓ u) →
  {v : Val b} →  later (∞apply f u) ⇓ v → (u* >>= λ u → apply f u) ⇓ v
sound-app' f (later⇓ u⇓) h = later⇓ (sound-app' f u⇓ h)
sound-app' f  now⇓       h = h

sound-app : ∀ {a b} →
  {f* : Delay (Val (a ⇒ b)) _} {f : Val (a ⇒ b)} (f⇓ : f* ⇓ f) →
  {u* : Delay (Val a)       _} {u : Val a}       (u⇓ : u* ⇓ u) →
  {v : Val b} →  later (∞apply f u) ⇓ v → apply* f* u* ⇓ v
sound-app  (later⇓ f⇓) u⇓ h = later⇓ (sound-app f⇓ u⇓ h)
sound-app {f = f} now⇓ u⇓ h = sound-app' f u⇓ h

〖app〗 : ∀ {a b} {f : Delay (Val (a ⇒ b)) _} {u : Delay (Val a) _} →

  C⟦ a ⇒ b ⟧ f → C⟦ a ⟧ u → C⟦ b ⟧ (apply* f u)

〖app〗 (f , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) = let v , v⇓                 , ⟦v⟧ = ⟦f⟧ ⟦u⟧
                                       in  v , sound-app f⇓ u⇓ v⇓ , ⟦v⟧

norm : ∀ {Γ a} (t : Tm Γ a) (ρ : Env Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (〖 t 〗 ρ)
norm (var x)   ρ θ = 〖var〗 x ρ θ
norm (abs t)   ρ θ = 〖abs〗 t ρ θ (λ {u} u⇓ → norm t (ρ , u) (θ , u⇓))
norm (app t u) ρ θ = 〖app〗 (norm t ρ θ) (norm u ρ θ)

-}
