{-# OPTIONS --copatterns --sized-types #-}

module LocallyNamelessValues where

open import Library
open import Term
open import Delay
open import Spine
open import DBLevel

-- Values and environments

mutual
  data Env {i : Size} (Δ : Cxt) : (Γ : Cxt) → Set where
    ε   : Env Δ ε
    _,_ : ∀ {Γ a} (ρ : Env {i = i} Δ Γ) (v : Val {i = i} Δ a) → Env Δ (Γ , a)

  data Val {i : Size} (Δ : Cxt) : (a : Ty) → Set where
    ne  : ∀ {j : Size< i}{a c} (x : Lvl Δ a) (vs : ValSpine {i = j} Δ a c) → Val Δ c
    lam : ∀ {Γ a b}            (t : Tm (Γ , a) b) (ρ : Env {i = i} Δ Γ)    → Val Δ (a ⇒ b)

  ValSpine : {i : Size} (Δ : Cxt) (a c : Ty) → Set
  ValSpine {i = i} Δ = RSpine (Val {i = i} Δ)

lookup : ∀ {i Γ Δ a} → Var Γ a → Env {i = i} Δ Γ → Val {i = i} Δ a
lookup zero    (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

-- Weakening.

mutual
  weakEnv : ∀ {i Γ Δ a} → Env {i = i} Δ Γ → Env {i = i} (Δ , a) Γ
  weakEnv ε        = ε
  weakEnv (ρ , v)  = weakEnv ρ , weakVal v

  weakVal : ∀ {i Δ a c} → Val {i = i} Δ c → Val {i = i} (Δ , a) c
  weakVal (ne {j = j} x vs)  = ne (weakLvl x) (weakValSpine {i = j} vs)
  weakVal (lam t ρ)          = lam t (weakEnv ρ)

  weakValSpine : ∀ {i Δ a b c} → ValSpine {i = i} Δ b c → ValSpine {i = i} (Δ , a) b c
  weakValSpine = mapRSp weakVal

-- Lifting.

var0 : ∀ {Δ a} → Val (Δ , a) a
var0 = ne (newLvl _) ε

liftEnv : ∀ {Γ Δ a} → Env Δ Γ → Env (Δ , a) (Γ , a)
liftEnv {Δ = Δ} ρ = weakEnv ρ , var0

-- Call-by-value evaluation.

mutual
  〖_〗  : ∀ {i} {Γ : Cxt} {a : Ty} → Tm Γ a → {Δ : Cxt} → Env Δ Γ → Delay (Val Δ a) i
  〖 var x   〗 ρ = now (lookup x ρ)
  〖 abs t   〗 ρ = now (lam t ρ)
  〖 app t u 〗 ρ = apply* (〖 t 〗 ρ) (〖 u 〗 ρ)

  apply* : ∀ {i Δ a b} → Delay (Val Δ (a ⇒ b)) i → Delay (Val Δ a) i → Delay (Val Δ b) i
  apply* f⊥ v⊥ = apply =<<2 f⊥ , v⊥

  apply : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay (Val Δ b) i
  apply f v = later (∞apply f v)

  ∞apply : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → ∞Delay (Val Δ b) i
  force (∞apply (lam t ρ) v) = 〖 t 〗 (ρ , v)
  force (∞apply (ne x sp) v) = now (ne x (sp , v))

-- beta quote
mutual
  β-readback : ∀{i Γ a} → Val Γ a → Delay (βNf Γ a) i
  β-readback v = later (∞β-readback v)

  ∞β-readback : ∀{i Γ a} → Val Γ a → ∞Delay (βNf Γ a) i
  force (∞β-readback (lam t ρ)) = lam  <$> (β-readback =<< 〖 t 〗 (liftEnv ρ))
  force (∞β-readback (ne x rs)) = ne (ind x) <$> mapRSpM β-readback rs


-- beta-eta quote

mutual

  readback : ∀{i j Γ a} → Val {j} Γ a → Delay (Nf Γ a) i
  readback {a = ★} (ne x vs) = ne (ind x) <$> readbackSpine vs
  readback {a = b ⇒ c}     v = later (∞readback v)

  ∞readback : ∀{i Γ b c} → Val Γ (b ⇒ c) → ∞Delay (Nf Γ (b ⇒ c)) i
  force (∞readback v) = lam <$> (readback =<< apply (weakVal v) var0)

  readbackSpine : ∀{i j Γ a c} → ValSpine {j} Γ a c → Delay (NfSpine Γ a c) i
  readbackSpine = mapRSpM readback

-- Monotonicity

mutual
  env≤ : ∀ {i Γ Δ Δ′} (η : Δ′ ≤ Δ) (ρ : Env {i = i} Δ Γ) → Env {i = i} Δ′ Γ
  env≤ η ε        = ε
  env≤ η (ρ , v)  = env≤ η ρ , val≤ η v

  val≤ : ∀ {i Γ Δ a} (η : Γ ≤ Δ) (v : Val {i = i} Δ a) → Val {i = i} Γ a
  val≤ η (ne {j = j} x vs)  = ne (lvl≤ η x) (valSpine≤ η vs)
  val≤ η (lam t ρ)          = lam t (env≤ η ρ)

  valSpine≤ : ∀ {i Γ Δ a c} (η : Γ ≤ Δ) (vs : ValSpine {i = i} Δ a c) → ValSpine {i = i} Γ a c
  valSpine≤ η vs = mapRSp (val≤ η) vs

-- First functor law.

mutual
  env≤-id : ∀ {i Γ Δ} (ρ : Env {i} Δ Γ) → env≤ id ρ ≡ ρ
  env≤-id ε         = refl
  env≤-id (ρ , v)   = cong₂ _,_ (env≤-id ρ) (val≤-id v)

  val≤-id : ∀ {i Δ a} (v : Val {i} Δ a) → val≤ id v ≡ v
  val≤-id (ne x vs) = cong₂ ne refl (valSpine≤-id vs)
  val≤-id (lam t ρ) = cong (lam t) (env≤-id ρ)

  valSpine≤-id : ∀ {i Δ a c} (vs : ValSpine {i} Δ a c) → valSpine≤ id vs ≡ vs
  valSpine≤-id = mapRSp-id val≤-id
{-
  valSpine≤-id ε         = refl
  valSpine≤-id (vs , v)  = cong₂ _,_ (valSpine≤-id vs) (val≤-id v)
-}

-- Second functor law.

mutual
  env≤-• : ∀ {i Γ Δ₁ Δ₂ Δ₃} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (ρ : Env {i} Δ₃ Γ) →
    env≤ η (env≤ η' ρ) ≡ env≤ (η • η') ρ
  env≤-• η η' ε       = refl
  env≤-• η η' (ρ , v) = cong₂ _,_ (env≤-• η η' ρ) (val≤-• η η' v)

  val≤-• : ∀ {i Δ₁ Δ₂ Δ₃ a} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (v : Val {i} Δ₃ a) →
    val≤ η (val≤ η' v) ≡ val≤ (η • η') v
  val≤-• η η' (ne x vs) = cong₂ ne (lvl≤-• η η' x) (valSpine≤-• η η' vs)
  val≤-• η η' (lam t ρ) = cong (lam t) (env≤-• η η' ρ)

  valSpine≤-• : ∀ {i Δ₁ Δ₂ Δ₃ a c} (η : Δ₁ ≤ Δ₂) (η' : Δ₂ ≤ Δ₃) (vs : ValSpine {i} Δ₃ a c) →
    valSpine≤ η (valSpine≤ η' vs) ≡ valSpine≤ (η • η') vs
  valSpine≤-• η η' = mapRSp-∘ (val≤-• η η')

-- weakVal and weakEnv are special cases

mutual
  weakEnvLem : ∀ {i Γ Δ a} (ρ : Env {i = i} Δ Γ) → weakEnv ρ ≡ env≤ (weak {a = a} id) ρ
  weakEnvLem ε       = refl
  weakEnvLem (ρ , v) = cong₂ _,_ (weakEnvLem ρ) (weakValLem v)

  weakValLem : ∀ {i Δ a c} (v : Val {i = i} Δ c) → weakVal v ≡ val≤ (weak {a = a} id) v
  weakValLem (ne x vs) = cong₂ ne (weakLvlLem x) (weakValSpineLem vs)
  weakValLem (lam t ρ) = cong (lam t) (weakEnvLem ρ)

  weakValSpineLem : ∀ {i Δ a b c} (vs : ValSpine {i = i} Δ b c) → weakValSpine vs ≡ valSpine≤ (weak {a = a} id) vs
  weakValSpineLem ε = refl
  weakValSpineLem (vs , v) = cong₂ _,_ (weakValSpineLem vs) (weakValLem v)

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

  C⟦_⟧ : (a : Ty) {Δ : Cxt} (v? : Delay (Val Δ a) ∞) → Set
  C⟦ a ⟧ v? = ∃ λ v → v? ⇓ v × V⟦ a ⟧ v

⟪_⟫ : (Γ : Cxt) {Δ : Cxt} (ρ : Env Δ Γ) → Set
⟪ ε ⟫     ε       = ⊤
⟪ Γ , a ⟫ (ρ , v) = ⟪ Γ ⟫ ρ × V⟦ a ⟧ v

-- Monotonicity

mutual
  V≤ : ∀ {Δ Δ′ a} (η : Δ′ ≤ Δ) (v : Val Δ a) (〖v〗 : V⟦ a ⟧ v) → V⟦ a ⟧ (val≤ η v)
  V≤ {a = ★}     η v 〖v〗             = canRead≤ η {v} 〖v〗
  V≤ {a = a ⇒ b} η f 〖f〗 η′ {u} 〖u〗 =
    let v , v⇓ , 〖v〗 = 〖f〗 (η′ • η) 〖u〗
        v⇓'           = subst (λ f' → apply f' u ⇓ v) (sym (val≤-• η′ η f)) v⇓
    in  v , v⇓' , 〖v〗

  C≤ : ∀ {Δ Δ′ a} (η : Δ′ ≤ Δ) {v? : Delay (Val Δ a) ∞} (v⇓ : C⟦ a ⟧ v?) → C⟦ a ⟧ (val≤ η <$> v?)
  C≤ η (v , v⇓ , 〖v〗) = val≤ η v , map⇓ (val≤ η) v⇓ , V≤ η v 〖v〗

CXT≤ : ∀ {Γ Δ Δ′} (η : Δ′ ≤ Δ) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → ⟪ Γ ⟫ (env≤ η ρ)
CXT≤ η ε       θ        = _
CXT≤ η (ρ , v) (θ , 〖v〗) = CXT≤ η ρ θ , V≤ η v 〖v〗

-- Type soundness

〖var〗 : ∀ {Γ Δ a} (x : Var Γ a) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (now (lookup x ρ))
〖var〗 zero    (_ , v) (_ , v⇓) = v , now⇓ , v⇓
〖var〗 (suc x) (ρ , _) (θ , _ ) = 〖var〗 x ρ θ

sound-β : ∀ {Γ Δ a b} {t : Tm (Γ , a) b} {ρ : Env Δ Γ} {u : Val Δ a} →

  C⟦ b ⟧ (〖 t 〗 (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)

sound-β (v , v⇓ , ⟦v⟧) = v , later⇓ v⇓ , ⟦v⟧

〖abs〗 : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) →

  ({Δ′ : Cxt} (η : Δ′ ≤ Δ) {u : Val Δ′ a} (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (〖 t 〗 (env≤ η ρ , u))) →
  C⟦ a ⇒ b ⟧ (now (lam t ρ))

〖abs〗 t ρ θ ih = lam t ρ , now⇓ , λ η u⇓ → sound-β (ih η u⇓)

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

〖app〗 (f , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) =
  let v , v⇓ , ⟦v⟧ = ⟦f⟧ id ⟦u⟧
      v⇓'          = subst (λ f' → later (∞apply f' u) ⇓ _) (val≤-id f) v⇓
  in  v , sound-app f⇓ u⇓ v⇓' , ⟦v⟧

sound : ∀ {Γ Δ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : ⟪ Γ ⟫ ρ) → C⟦ a ⟧ (〖 t 〗 ρ)
sound (var x)   ρ θ = 〖var〗 x ρ θ
sound (abs t)   ρ θ = 〖abs〗 t ρ θ (λ {Δ′} η {u} u⇓ → sound t (env≤ η ρ , u) (CXT≤ η ρ θ , u⇓))
sound (app t u) ρ θ = 〖app〗 (sound t ρ θ) (sound u ρ θ)

-- Reflection and reification

mutual
  reflect : ∀{Γ a} c (x : Lvl Γ a) {vs : ValSpine Γ a c} {ns : NfSpine Γ a c} →
           ReadSpine vs ns → V⟦ c ⟧ (ne x vs)
  reflect ★ x rs = canRead★ x rs
  reflect (a ⇒ b) x {vs} rs η {u} 〖u〗 = let
       x'  = lvl≤ η x
       vs' = valSpine≤ η vs , u
       rs' = readSpine≤ η rs
       n , r = reify a u 〖u〗
    in ne x' vs' , later⇓ now⇓ , reflect b x' (rs' , r)

  reflect0 : ∀{Γ a} (x : Lvl Γ a) → V⟦ a ⟧ (ne x ε)
  reflect0 {a = a} x = reflect a x ε

  reify : ∀{Γ} a (v : Val Γ a) (〖v〗 : V⟦ a ⟧ v) → CanRead v
  reify ★       v 〖v〗 = 〖v〗
  reify {Γ} (b ⇒ c) f 〖f〗 =
    let
      〖u〗  = reflect0 (newLvl Γ)
      v , v⇓ , 〖v〗 = 〖f〗 (weak id) {var0} 〖u〗
      n , r = reify c v 〖v〗
    in lam n , λ {Δ} η → let
      f' = val≤ η f
      n' = nf≤ (lift' η) n
--      η' = lift' η
      have : readback (val≤ (lift' η) v) ⇓ n'
      have = r (lift' η)
      goal₃ : (readback =<< apply (val≤ (weak η) f) var0) ⇓ n'
      goal₃ =  {!r (lift' η)!}

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

