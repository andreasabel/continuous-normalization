-- Interface to standard library.

module Library where

open import Level public
  using (Level) renaming (zero to lzero; suc to lsuc)

open import Size public

open import Category.Monad public
  using (RawMonad; module RawMonad)

open import Data.Empty public
  using (⊥; ⊥-elim)

open import Data.List public
  using (List; []; _∷_; map)

open import Data.Maybe public
  using (Maybe; just; nothing) renaming (map to fmap)

open import Data.Nat public
  using (ℕ; zero; suc; _+_; _≟_)

open import Data.Product public
  using (∃; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Data.Sum public
  using (_⊎_; [_,_]′) renaming (inj₁ to inl; inj₂ to inr)

open import Data.Unit  public
  using (⊤)

open import Function public
  using (_∘_; case_of_)

open import Relation.Nullary public
  using (Dec; yes; no)

open import Relation.Binary public
  using (Setoid; module Setoid)

import Relation.Binary.PreorderReasoning
module Pre = Relation.Binary.PreorderReasoning

open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Relation.Binary.HeterogeneousEquality public
  using (_≅_; refl; ≡-to-≅; module ≅-Reasoning)
  renaming (sym to hsym; trans to htrans; cong to hcong; cong₂ to hcong₂; subst to hsubst)

hcong₃ : {A : Set}{B : A → Set}{C : ∀ a → B a → Set}{D : ∀ a b → C a b → Set}
         (f : ∀ a b c → D a b c)
         {a a' : A} → a ≅ a' →
         {b : B a}{b' : B a'} → b ≅ b' →
         {c : C a b}{c' : C a' b'} → c ≅ c' →
         f a b c ≅ f a' b' c'
hcong₃ f refl refl refl = refl

≅-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x ≡ y
≅-to-≡ refl = refl
