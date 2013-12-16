{-# OPTIONS --copatterns --sized-types #-}

module LocallyNamelessValues where

open import Library
open import Term
open import Delay
open import Spine
open import DBLevel
open import LocallyNameless.Values
open import LocallyNameless.Eval


-- Things we can read back.

Read : ∀ {Δ a} (v : Val Δ a) (n : Nf Δ a) → Set
Read {Δ} v n = {Γ : Cxt} (η : Γ ≤ Δ) → readback (val≤ η v) ⇓ (nf≤ η n)

read≤ : ∀ {Γ Δ a} (η : Γ ≤ Δ) {v : Val Δ a} {n : Nf Δ a} →
  Read v n → Read (val≤ η v) (nf≤ η n)
read≤ η {v} {n} r η' rewrite val≤-• η' η v | nf≤-• η' η n = r (η' • η)

data ReadSpine {Δ a} : ∀ {c} (vs : ValSpine Δ a c) (ns : NfSpine Δ a c) → Set where
    ε   : ReadSpine ε ε
    _,_ : ∀ {b c} {vs : ValSpine Δ a (b ⇒ c)}
                  {ns : NfSpine  Δ a (b ⇒ c)}
                  {v  : Val      Δ b}
                  {n  : Nf       Δ b} →
          ReadSpine vs ns → Read v n → ReadSpine (vs , v) (ns , n)

readSpine : ∀ {Δ a c} {vs : ValSpine Δ a c} {ns : NfSpine  Δ a c} →
  ReadSpine vs ns → readbackSpine vs ⇓ ns
readSpine ε        = now⇓
readSpine (rs , r) = {!!}

readSpine≤ : ∀ {Δ a c} {vs : ValSpine Δ a c} {ns : NfSpine  Δ a c}
  {Γ : Cxt} (η : Γ ≤ Δ) →

  ReadSpine vs ns → ReadSpine (valSpine≤ η vs) (nfSpine≤ η ns)

readSpine≤ η ε        = ε
readSpine≤ η (rs , r) = readSpine≤ η rs , read≤ η r

read★ : ∀ {Δ a} (x : Lvl Δ a) {vs : ValSpine Δ a ★} {ns : NfSpine Δ a ★} →
  ReadSpine vs ns → Read (ne x vs) (ne (ind x) ns)
read★ x {vs} {ns} rs η = map⇓ (ne i') (readSpine rs')
  where
    i'  = var≤       η (ind x)
    vs' = valSpine≤  η vs
    ns' = nfSpine≤   η ns
    rs' = readSpine≤ η rs


CanRead : ∀ {Δ a} (v : Val Δ a) → Set
CanRead v = ∃ λ n → Read v n

canRead≤ : ∀ {Γ Δ a} (η : Γ ≤ Δ) {v : Val Δ a} (c : CanRead v) → CanRead (val≤ η v)
canRead≤ η (n , r) = nf≤ η n , read≤ η r

canRead★ : ∀ {Δ a} (x : Lvl Δ a) {vs : ValSpine Δ a ★} {ns : NfSpine Δ a ★} →
  ReadSpine vs ns → CanRead (ne x vs)
canRead★ x {vs} {ns} rs = ne (ind x) ns , read★ x rs

data CanReadSpine {Δ a} : ∀ {c} (vs : ValSpine Δ a c) → Set where
  ε   : CanReadSpine ε
  _,_ : ∀ {b c} {vs : ValSpine Δ a (b ⇒ c)} {v : Val Δ b} →
        CanReadSpine vs → CanRead v → CanReadSpine (vs , v)

{-

canRead★ : ∀ {Δ a} (x : Lvl Δ a) {vs : ValSpine Δ a ★} →
  CanReadSpine vs → CanRead (ne x vs)
canRead★ (lvl x i x~i) cvs η = (ne i' {!!}) , later⇓ (map⇓ (ne i') {!cvs !})
  where
    i' = var≤ η i

canReadApp : ∀ {Δ a b c} {x : Lvl Δ a} {vs : ValSpine Δ a (b ⇒ c)} {v : Val Δ b} →
  CanRead (ne x vs) → CanRead v → CanRead (ne x (vs , v))
canReadApp {x = x} cr crv η with cr η | crv η
canReadApp {Δ} {a} {b} {c} {lvl x i corr} cr crv η | lam t , ⇓t | u , ⇓u = {!!}
-}

{-let
    n , r⇓ = cr η

  in {!n!} , {!!}
-}

-- Type interpretation

mutual
  V⟦_⟧ : (a : Ty) {Δ : Cxt} (v : Val Δ a) → Set
  V⟦ ★     ⟧ {Δ = Δ} v = CanRead v
  V⟦ a ⇒ b ⟧ {Δ = Δ} f = {Γ : Cxt} (η : Γ ≤ Δ) →
    {u : Val Γ a} (〖u〗 : V⟦ a ⟧ u) → C⟦ b ⟧ (apply (val≤ η f) u)

  record C⟦_⟧ (a : Ty) {Δ : Cxt} (v? : Delay (Val Δ a) ∞) : Set where
    constructor computation
    field
      v  : Val Δ a
      v⇓ : v? ⇓ v
      〖v〗 : V⟦ a ⟧ v

⟪_⟫ : (Γ : Cxt) {Δ : Cxt} (ρ : Env Δ Γ) → Set
⟪ ε ⟫     ε       = ⊤
⟪ Γ , a ⟫ (ρ , v) = ⟪ Γ ⟫ ρ × V⟦ a ⟧ v

-- Monotonicity

mutual
  V≤ : ∀ {Δ Δ′ a} (η : Δ′ ≤ Δ) (v : Val Δ a) (〖v〗 : V⟦ a ⟧ v) → V⟦ a ⟧ (val≤ η v)
  V≤ {a = ★}     η v 〖v〗             = canRead≤ η {v} 〖v〗
  V≤ {a = a ⇒ b} η f 〖f〗 η′ {u} 〖u〗 =
    let computation v v⇓ 〖v〗 = 〖f〗 (η′ • η) 〖u〗
        v⇓'           = subst (λ f' → apply f' u ⇓ v) (sym (val≤-• η′ η f)) v⇓
    in  computation v v⇓' 〖v〗

  C≤ : ∀ {Δ Δ′ a} (η : Δ′ ≤ Δ) {v? : Delay (Val Δ a) ∞} (v⇓ : C⟦ a ⟧ v?) → C⟦ a ⟧ (val≤ η <$> v?)
  C≤ η (computation v v⇓ 〖v〗) = computation (val≤ η v) (map⇓ (val≤ η) v⇓) (V≤ η v 〖v〗)

CXT≤ : ∀ {Γ Δ Δ′} (η : Δ′ ≤ Δ) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → ⟪ Γ ⟫ (env≤ η ρ)
CXT≤ η ε       θ        = _
CXT≤ η (ρ , v) (θ , 〖v〗) = CXT≤ η ρ θ , V≤ η v 〖v〗

-- Type soundness

〖var〗 : ∀ {Γ Δ a} (x : Var Γ a) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (now (lookup x ρ))
〖var〗 zero    (_ , v) (_ , v⇓) = computation v now⇓ v⇓
〖var〗 (suc x) (ρ , _) (θ , _ ) = 〖var〗 x ρ θ

sound-β : ∀ {Γ Δ a b} {t : Tm (Γ , a) b} {ρ : Env Δ Γ} {u : Val Δ a} →

  C⟦ b ⟧ (〖 t 〗 (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)

sound-β (computation v v⇓ ⟦v⟧) = computation v (later⇓ v⇓) ⟦v⟧

〖abs〗 : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) →

  ({Δ′ : Cxt} (η : Δ′ ≤ Δ) {u : Val Δ′ a} (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (〖 t 〗 (env≤ η ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))

〖abs〗 t ρ θ ih = computation (lam t ρ) now⇓ (λ η u⇓ → sound-β (ih η u⇓))

sound-app' : ∀ {Δ a b} (f : Val Δ (a ⇒ b)) →
  {u* : Delay (Val Δ a) _} {u : Val Δ a} (u⇓ : u* ⇓ u) →
  {v : Val Δ b} →  later (∞apply f u) ⇓ v → (u* >>= λ u → apply f u) ⇓ v
sound-app' f (later⇓ u⇓) h = later⇓ (sound-app' f u⇓ h)
sound-app' f  now⇓       h = h

sound-app : ∀ {Δ a b} →
  {f* : Delay (Val Δ (a ⇒ b)) _} {f : Val Δ (a ⇒ b)} (f⇓ : f* ⇓ f) →
  {u* : Delay (Val Δ a)       _} {u : Val Δ a}       (u⇓ : u* ⇓ u) →
  {v : Val Δ b} →  later (∞apply f u) ⇓ v → apply* f* u* ⇓ v
sound-app  (later⇓ f⇓) u⇓ h = later⇓ (sound-app f⇓ u⇓ h)
sound-app {f = f} now⇓ u⇓ h = sound-app' f u⇓ h


〖app〗 : ∀ {Δ a b} {f : Delay (Val Δ (a ⇒ b)) _} {u : Delay (Val Δ a) _} →

  C⟦ a ⇒ b ⟧ f → C⟦ a ⟧ u → C⟦ b ⟧ (apply* f u)

〖app〗 (computation f f⇓ ⟦f⟧) (computation u u⇓ ⟦u⟧) =
  let computation v v⇓ ⟦v⟧ = ⟦f⟧ id ⟦u⟧
      v⇓'                  = subst (λ f' → later (∞apply f' u) ⇓ _) (val≤-id f) v⇓
  in  computation v (sound-app f⇓ u⇓ v⇓') ⟦v⟧

sound : ∀ {Γ Δ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (〖 t 〗 ρ)
sound (var x)   ρ θ = 〖var〗 x ρ θ
sound (abs t)   ρ θ = 〖abs〗 t ρ θ (λ {Δ′} η {u} u⇓ → sound t (env≤ η ρ , u) (CXT≤ η ρ θ , u⇓))
sound (app t u) ρ θ = 〖app〗 (sound t ρ θ) (sound u ρ θ)

-- Reflection and reification

readbackLem :
  ∀ {Δ a b} (f : Val Δ (a ⇒ b)) (v : Val (Δ , a) b) →
  apply (val≤ (weak id) f) var0 ⇓ v →
  V⟦ b ⟧ v →
  (n : Nf (Δ , a) b) →
  Read v n →
  ∀ {Γ} (η : Γ ≤ Δ) →
  (readback =<< apply (val≤ (weak η) f) var0) ⇓ nf≤ (lift' η) n
readbackLem f v ap 〖v〗 n r η = {!!}

mutual
  reflect : ∀{Γ a} c (x : Lvl Γ a) {vs : ValSpine Γ a c} {ns : NfSpine Γ a c} →
           ReadSpine vs ns → V⟦ c ⟧ (ne x vs)
  reflect ★ x rs = canRead★ x rs
  reflect (a ⇒ b) x {vs} rs η {u} 〖u〗 = let
       x'  = lvl≤ η x
       vs' = valSpine≤ η vs , u
       rs' = readSpine≤ η rs
       n , r = reify a u 〖u〗
    in computation (ne x' vs') (later⇓ now⇓) (reflect b x' (rs' , r))

  reflect0 : ∀{Γ a} (x : Lvl Γ a) → V⟦ a ⟧ (ne x ε)
  reflect0 {a = a} x = reflect a x ε

  reify : ∀{Γ} a (v : Val Γ a) (〖v〗 : V⟦ a ⟧ v) → CanRead v
  reify ★       v 〖v〗 = 〖v〗
  reify {Γ} (b ⇒ c) f 〖f〗 =
    let
      〖u〗  = reflect0 (newLvl Γ)
      computation v v⇓ 〖v〗 = 〖f〗 (weak id) {var0} 〖u〗
      n , r = reify c v 〖v〗
    in lam n , λ {Δ} η → let
      f' = val≤ η f
      n' = nf≤ (lift' η) n
{-
--      η' = lift' η
      have : readback (val≤ (lift' η) v) ⇓ n'
      have = r (lift' η)

      v⇓' : (val≤ (lift' η) <$> later (∞apply (val≤ (weak id) f) var0)) ⇓ val≤ (lift' η) v
      v⇓' = map⇓ (val≤ (lift' η)) v⇓

      lem : apply (val≤ (weak η) f) var0 ⇓ val≤ (lift' η) v
      lem = {!map⇓ (val≤ (lift' η)) v⇓!}
-}
      goal₃ : (readback =<< apply (val≤ (weak η) f) var0) ⇓ n'
      goal₃ =  readbackLem f v v⇓  〖v〗 n r η

      goal₂ : (readback =<< apply (val≤ (weak id) f') var0) ⇓ n'
      goal₂ =  subst (λ z → (readback =<< apply z var0) ⇓ n')
                    (sym (val≤-• (weak id) η f))
                    goal₃

      goal₁ : (readback =<< apply (weakVal f') var0) ⇓ n'
      goal₁ = subst (λ z → (readback =<< apply z var0) ⇓ n')
                    (sym (weakValLem f'))
                    goal₂
      goal : force (∞readback f') ⇓ nf≤ η (lam n)
      goal =  map⇓ lam goal₁
    in later⇓ goal

