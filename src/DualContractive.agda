{-# OPTIONS --rewriting #-}
module DualContractive where

open import Data.Fin hiding (_+_)
open import Data.Maybe
open import Data.Nat hiding (_≤_)
open import Data.Sum hiding (map)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Function

open import Direction

open import Extensionality

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
  i j : Fin n 
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

data Contractive : Fin (suc n) → SType n → Set where
  con-rec : Contractive (suc i) s → Contractive i (rec s)
  con-xmt : Contractive 0F s → Contractive i (xmt d t s)
  con-var : i ≤ inject₁ j → Contractive i (var j)

module Examples where
  cn1 : ¬ Contractive {2} 1F (var 0F)
  cn1 (con-var ())

  cp1 : Contractive {2} 0F (var 1F)
  cp1 = con-var z≤n

  cp0 : Contractive {2} 0F (var 0F)
  cp0 = con-var z≤n

  sp2 : SType 0
  sp2 = (rec (xmt SND TInt (rec (var 1F))))

  cp2 : Contractive 0F sp2
  cp2 = con-rec (con-xmt (con-rec (con-var (s≤s z≤n))))

  sn2 : SType 0
  sn2 = (rec (xmt SND TInt (rec (var 0F))))

  cn2 : ¬ Contractive 0F sn2
  cn2 (con-rec (con-xmt (con-rec (con-var ()))))

unfold : (s : SType n) (c : Contractive i s) (σ : SType n → SType 0) → SType 0
unfold (xmt d t s) (con-xmt c) σ = σ (xmt d t s)
unfold (rec s) (con-rec c) σ = unfold s c (σ ∘ λ sn' → ssubst sn' 0F (σ (rec s))) 
unfold {i = 0F} (var x) (con-var z≤n) σ = σ (var x)
unfold {i = suc i} (var 0F) (con-var ()) σ
unfold {i = suc i} (var (suc x)) (con-var (s≤s x₁)) σ = unfold (var x) (con-var x₁) (σ ∘ weaken1S)

module CheckUnfold where
  s1 : SType 0
  s1 = rec (xmt SND TInt (var 0F))
  c1 : Contractive 0F s1
  c1 = con-rec (con-xmt (con-var z≤n))
  s2 : SType 0
  s2 = xmt SND TInt s1

  u-s1=s2 : unfold s1 c1 id ≡ s2
  u-s1=s2 = refl

  s3 : SType 0
  s3 = rec (rec (xmt SND TInt (var 0F)))
  c3 : Contractive 0F s3
  c3 = con-rec (con-rec (con-xmt (con-var z≤n)))
  u-s3=s2 : unfold s3 c3 id ≡ s2
  u-s3=s2 = refl

infer-contractive : (s : SType n) (i : Fin (suc n)) → Dec (Contractive i s)
infer-contractive (xmt d t s) i 
  with infer-contractive s 0F
infer-contractive (xmt d t s) i | yes p = yes (con-xmt p)
infer-contractive (xmt d t s) i | no ¬p = no (λ { (con-xmt c) → ¬p c })
infer-contractive (rec s) i
  with infer-contractive s (suc i)
infer-contractive (rec s) i | yes p = yes (con-rec p)
infer-contractive (rec s) i | no ¬p = no (λ { (con-rec c) → ¬p c })
infer-contractive (var x) 0F = yes (con-var z≤n)
infer-contractive (var 0F) (suc i) = no (λ { (con-var ()) })
infer-contractive (var (suc x)) (suc i)
  with infer-contractive (var x) i
infer-contractive (var (suc x)) (suc i) | yes (con-var x₁) = yes (con-var (s≤s x₁))
infer-contractive (var (suc x)) (suc i) | no ¬p = no (λ { (con-var (s≤s y)) → ¬p (con-var y) })

module ExamplesInference where
  open Examples
  
  infer-p2 : infer-contractive sp2 0F ≡ yes cp2
  infer-p2 = refl

  -- infer-n2 : infer-contractive sn2 0F ≡ no cn2
  -- how?


