{-# OPTIONS --rewriting #-}
module DualContractive where

open import Data.Fin hiding (_+_)
open import Data.Maybe
open import Data.Nat

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Function

open import Direction

variable
  m n : ℕ

open import Agda.Builtin.Equality.Rewrite
----------------------------------------------------------------------
-- auxiliaries for automatic rewriting

n+1=suc-n : n + 1 ≡ suc n
n+1=suc-n {zero} = refl
n+1=suc-n {suc n} = cong suc (n+1=suc-n {n})

{-# REWRITE n+1=suc-n #-}

n+0=n : n + 0 ≡ n
n+0=n {zero} = refl
n+0=n {suc n} = cong suc (n+0=n {n})

{-# REWRITE n+0=n #-}

inject+0-x=x : {x : Fin m} → inject+ 0 x ≡ x
inject+0-x=x {x = zero} = refl
inject+0-x=x {x = suc x} = cong suc inject+0-x=x

{-# REWRITE inject+0-x=x #-}

----------------------------------------------------------------------

data TType (n : ℕ) : Set 
data SType (n : ℕ) : Set

data TType n where
  TInt : TType n
  TChn : (s : SType n) → TType n

data SType n where
  xmt : (d : Dir) (t : TType n) (s : SType n) → SType n
  rec : SType (suc n) → SType n
  var : Fin n → SType n

variable
  i : Fin n 
  t : TType n
  s s₀ : SType n

----------------------------------------------------------------------
-- weakening

weakenS : ∀ m → SType n → SType (n + m)
weakenT : ∀ m → TType n → TType (n + m)

weakenS m (xmt d t s) = xmt d (weakenT m t) (weakenS m s)
weakenS m (rec s) = rec (weakenS m s)
weakenS m (var x) = var (inject+ m x)

weakenT m TInt = TInt
weakenT m (TChn s) = TChn (weakenS m s)

weaken1S : SType n → SType (suc n)
weaken1S s = weakenS 1 s

----------------------------------------------------------------------
-- substitution

ssubst : SType (suc n) → Fin (suc n) → SType 0 → SType n
tsubst : TType (suc n) → Fin (suc n) → SType 0 → TType n

ssubst (xmt d t s) i s0 = xmt d (tsubst t i s0) (ssubst s i s0)
ssubst (rec s) i s0 = rec (ssubst s (suc i) s0)
ssubst {n} (var 0F) 0F s0 = weakenS n s0
ssubst {suc n} (var 0F) (suc i) s0 = var 0F
ssubst (var (suc x)) 0F s0 = var x
ssubst {suc n} (var (suc x)) (suc i) s0 = weaken1S (ssubst (var x) i s0)

tsubst TInt i s₀ = TInt
tsubst (TChn s) i s₀ = TChn (ssubst s i s₀)

----------------------------------------------------------------------
-- contractivity

open import Agda.Builtin.Size

data Contractive : { j : Size} → SType n → Set where
  con-xmt : { j : Size } → Contractive {j = ↑ j} (xmt d t s)
  con-rec : { j : Size } → Contractive {j = j} s → Contractive {j = ↑ j} (rec s)

con-subst : ∀ {n j}{i : Fin (suc n)} →
  ∀ s → Contractive{suc n} {j = j} s → Contractive{n} {j = j } (ssubst s i s₀)
con-subst (xmt d t s) con-xmt = con-xmt
con-subst {j = j} (rec s) (con-rec c) = con-rec (con-subst s c)
con-subst (var x) ()

unfold : ∀ {j} → (s : SType 0) (c : Contractive {j = j} s) → SType 0
unfold (xmt d t s) con-xmt = xmt d t s
unfold (rec s) (con-rec {j = j} c) = unfold (ssubst s 0F (rec s)) (con-subst s c)
unfold (var x) ()

unfold' : (s : SType n) (c : Contractive s) (σ : SType n → SType 0) → SType 0
unfold' (xmt d t s) con-xmt σ = σ (xmt d t s)
unfold' (rec s) (con-rec c) σ = unfold' s c λ s' → (σ ∘ ssubst s' 0F) (σ (rec s))
unfold' (var x) () σ

module CheckUnfold where
  s1 : SType 0
  s1 = rec (xmt SND TInt (var 0F))
  c1 : Contractive s1
  c1 = con-rec con-xmt
  s2 : SType 0
  s2 = xmt SND TInt s1

  u-s1=s2 : unfold' s1 c1 id ≡ s2
  u-s1=s2 = refl

  s3 : SType 0
  s3 = rec (rec (xmt SND TInt (var 0F)))
  c3 : Contractive s3
  c3 = con-rec (con-rec con-xmt)
  u-s3=s2 : unfold' s3 c3 id ≡ s2
  u-s3=s2 = refl

infer-contractive : (s : SType n) → Maybe (Contractive s)
infer-contractive (xmt d t s) = just con-xmt
infer-contractive (rec s) = map con-rec (infer-contractive s)
infer-contractive (var x) = nothing
