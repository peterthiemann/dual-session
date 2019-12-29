{-# OPTIONS --rewriting #-}
module DualContractive where

open import Data.Fin
open import Data.Maybe
open import Data.Nat hiding (_≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Function

open import Direction

open import Extensionality

variable
  m n : ℕ
  i j : Fin n 

----------------------------------------------------------------------
-- lemmas for rewriting

n+1=suc-n : n +ℕ 1 ≡ suc n
n+1=suc-n {zero} = refl
n+1=suc-n {suc n} = cong suc (n+1=suc-n {n})

n+0=n : n +ℕ 0 ≡ n
n+0=n {zero} = refl
n+0=n {suc n} = cong suc (n+0=n {n})

n+sucm=sucn+m : ∀ n m → n +ℕ suc m ≡ suc (n +ℕ m)
n+sucm=sucn+m 0F m = refl
n+sucm=sucn+m (suc n) m = cong suc (n+sucm=sucn+m n m)

{-# REWRITE n+sucm=sucn+m #-}

open import Agda.Builtin.Equality.Rewrite


----------------------------------------------------------------------
module Experimental where

  data CSType (n : ℕ) (i : Fin (suc n)) : Set
  -- contractive session type with n free variables
  -- uses of variables greater than or equal to i are contractive
  -- uses of variables less than i are forbidden

  data CTType (n : ℕ) : Set where
    TInt : CTType n
    TChn : (s : CSType n 0F) → CTType n

  data CSType n i where
    xmt : (d : Dir) (t : CTType n) (s : CSType n 0F) → CSType n i
    end : CSType n i
    rec : (s : CSType (suc n) (suc i)) → CSType n i
    var : (x : Fin n) (i≤x : i ≤ inject₁ x) → CSType n i

  impossible : (x : Fin n) → ¬ fromℕ n ≤ inject₁ x
  impossible 0F ()
  impossible (suc x) (s≤s n≤x) = impossible x n≤x

  module Example where

    s13 : CSType 3 1F
    s13 = var 1F (s≤s z≤n)
    s12 : CSType 2 0F
    s12 = rec s13
    s11 : CSType 2 2F
    s11 = xmt SND TInt s12
    s10 : CSType 1 1F
    s10 = rec s11

    s1 : CSType 0 0F
    s1 = rec (xmt SND TInt (rec (var 1F (s≤s z≤n))))

    -- need s1 at type CSType 1 1F
    s1-u1 : CSType 0 0F
    s1-u1 = xmt SND TInt (rec (rec (xmt SND  TInt (rec (var 1F (s≤s z≤n))))))

  lemma-inject : ∀ x m → (i≤x : i ≤ inject₁ x) → inject+ m i ≤ inject₁ (inject+ m x)
  lemma-inject {i = 0F} 0F m z≤n = z≤n
  lemma-inject {i = 0F} (suc x) m z≤n = z≤n
  lemma-inject {i = suc i} 0F m ()
  lemma-inject {i = suc i} (suc x) m (s≤s i≤x) = s≤s (lemma-inject x m i≤x)

  sweaken0 : ∀ m → CSType n i → CSType (n +ℕ m) (inject+ m i)
  tweaken0 : ∀ m → CTType n → CTType (n +ℕ m)

  sweaken0 m (xmt d t s) = xmt d (tweaken0 m t) (sweaken0 m s)
  sweaken0 m (rec s) = rec (sweaken0 m s)
  sweaken0 m (var x i≤x) = var (inject+ m x) (lemma-inject x m i≤x)
  sweaken0 m end = end

  tweaken0 m TInt = TInt
  tweaken0 m (TChn s) = TChn (sweaken0 m s)

  tweaken' : ∀ m → CTType n → CTType (n +ℕ m)
  sweaken' : ∀ m → CSType n (fromℕ n) → CSType (n +ℕ m) (fromℕ (n +ℕ m))

  sweaken' m (xmt d t s) = xmt d (tweaken' m t) (sweaken0 m s)
  sweaken' m end = end
  sweaken' m (rec s) = rec (sweaken' m s)
  sweaken' m (var x i≤x) with impossible x i≤x
  sweaken' m (var x i≤x) | ()

  tweaken' m TInt = TInt
  tweaken' m (TChn s) = TChn (sweaken0 m s)

  module revisit-example where

    s1 : CSType 0 0F
    s1 = rec (xmt SND TInt (rec (var 1F (s≤s z≤n))))

    s1w : CSType 1 1F
    s1w = sweaken' 1 s1

    -- need s1 at type CSType 1 1F
    s1-u1 : CSType 0 0F
    s1-u1 = xmt SND TInt (rec (rec (xmt SND  TInt (rec (var 1F (s≤s z≤n))))))

    s1-u1w : CSType 0 0F
    s1-u1w = xmt SND TInt (rec s1w)

    u1=u1w : s1-u1 ≡ s1-u1w
    u1=u1w = refl

  tsubst1 : (j : Fin (suc n)) → CSType 0 0F → CTType (suc n) → CTType n
  ssubst1 : (j : Fin (suc n)) → CSType 0 0F → i ≤ j → CSType (suc n) (inject₁ i) → CSType n i

  ssubst1 j s0 i≤j (xmt d t s) = xmt d (tsubst1 j s0 t) (ssubst1 j s0 z≤n s)
  ssubst1 j s0 i≤j end = end
  ssubst1 j s0 i≤j (rec s) = rec (ssubst1 (suc j) s0 (s≤s i≤j) s)
  ssubst1 {0F} {0F} 0F s0 z≤n (var 0F z≤n) = s0
  ssubst1 {suc n} {0F} 0F s0 z≤n (var 0F z≤n) = sweaken0 (suc n) s0
  ssubst1 {suc n} {0F} 0F s0 z≤n (var (suc x) z≤n) = var x z≤n
  ssubst1 {suc n} {0F} (suc j) s0 z≤n (var 0F z≤n) = var 0F z≤n
  ssubst1 {suc n} {0F} (suc j) s0 z≤n (var (suc x) z≤n)
    with sweaken0 1 (ssubst1 {n} {0F} j s0 z≤n (var x z≤n))
  ... | ih rewrite n+0=n {n} = ih
  ssubst1 {suc n} {suc i} (suc j) s0 (s≤s i≤j) (var (suc x) (s≤s i≤x))
    with ssubst1 {n} {i} j s0 i≤j (var x i≤x)
  ... | ih = let sw1 = sweaken'{n} 1 in {!sweaken'!}

  tsubst1 j s0 t = {!!}

  tsubst0 : Fin (suc n) → CSType 0 0F → CTType (suc n) → CTType n
  ssubst0 : Fin (suc n) → CSType 0 0F → CSType (suc n) (inject₁ i) → CSType n i

  ssubst0 j s0 (xmt d t s) = xmt d (tsubst0 j s0 t) (ssubst0 j s0 s)
  ssubst0 j s0 end = end
  ssubst0 j s0 (rec s) = rec (ssubst0 (suc j) s0 s)
  ssubst0 {n} {0F} 0F s0 (var 0F z≤n) = sweaken0 n s0
  ssubst0 {suc n} {0F} (suc j) s0 (var 0F z≤n) = var 0F z≤n
  ssubst0 {n} {0F} 0F s0 (var (suc x) z≤n) = var x z≤n
  ssubst0 {suc n} {0F} (suc j) s0 (var (suc x) z≤n) 
    with sweaken0 1 (ssubst0 {n} {0F} j s0 (var x z≤n))
  ... | ih rewrite n+0=n {n} = ih
  ssubst0 {n} {suc i} j s0 (var 0F ())
  ssubst0 {suc n} {suc i} 0F s0 (var (suc x) (s≤s i≤x)) = {!!} -- var x {!!}
  ssubst0 {suc n} {suc i} (suc j) s0 (var (suc x) (s≤s i≤x)) = {!!}

  tsubst0 j s0 TInt = TInt
  tsubst0 j s0 (TChn s) = TChn (ssubst0 j s0 s)

  ssubst' : Fin (suc n) → CSType 0 0F → CSType (suc n) (fromℕ (suc n)) → CSType n (fromℕ n)

  ssubst' j s0 (xmt d t s) = xmt d (tsubst0 j s0 t) (ssubst0 j s0 s)
  ssubst' j s0 end = end
  ssubst' j s0 (rec s) = rec (ssubst' (suc j) s0 s)
  ssubst' j s0 (var x i≤x) with impossible x i≤x
  ssubst' j s0 (var x i≤x) | ()

  ----------------------------------------------------------------------

  sweaki : j ≤ i → CSType n i → CSType n j
  sweaki i≤j (xmt d t s) = xmt d t s
  sweaki i≤j (rec s) = rec (sweaki (s≤s i≤j) s)
  sweaki i≤j (var x i≤j₁) = var x (≤-trans i≤j i≤j₁)
  sweaki i≤j end = end

  -- _+𝔽_ : (i : Fin (suc n)) (m : ℕ) → Fin (suc (n +ℕ m))
  -- _+𝔽_ i 0F = i
  -- _+𝔽_ i (suc m) = suc (_+𝔽_ i m)

  -- liftadd-suc : (i : Fin (suc n)) (m : ℕ) → _+𝔽_ (suc i) m ≡ suc (_+𝔽_ i m)
  -- liftadd-suc i 0F = refl
  -- liftadd-suc i (suc m) = cong suc (liftadd-suc i m)

  -- -- weakening
  -- sweaken : ∀ m → CSType n i → CSType (n +ℕ m) (i +𝔽 m)
  -- tweaken : ∀ m → CTType n → CTType (n +ℕ m)

  -- sweaken m (xmt d t s) = xmt d (tweaken m t) (sweaki z≤n (sweaken m s))
  -- sweaken {i = i} m (rec s) with sweaken m s
  -- ... | sms rewrite liftadd-suc i m = rec sms
  -- sweaken m (var x i≤x) = var (inject+ m x) {!!}
  -- sweaken m end = end

  -- tweaken m TInt = TInt
  -- tweaken m (TChn s) = TChn (sweaki z≤n (sweaken m s))


  _+𝔾_ : (i : Fin (suc n)) (j : Fin (suc m)) → Fin (suc (n +ℕ m))
  _+𝔾_{n}{m} i 0F = inject+ m i
  _+𝔾_{n}{suc m} i (suc j) with i +𝔾 j
  ... | ij rewrite n+sucm=sucn+m n m = suc ij

  suc-i+Gj : (i : Fin (suc n)) (j : Fin (suc m)) → suc (i +𝔾 j) ≡ suc i +𝔾 j
  suc-i+Gj i 0F = refl
  suc-i+Gj{n}{suc m} i (suc j) with suc-i+Gj i j
  ... | sij rewrite n+sucm=sucn+m n m = cong suc sij

  ij≤injmx : ∀ m → (i : Fin (suc n)) (j : Fin (suc m)) (x : Fin n) (i≤x : i ≤ inject₁ x)
    → (i +𝔾 j) ≤ inject₁ (inject+ m x)
  ij≤injmx m 0F j 0F z≤n = {!!}
  ij≤injmx m 0F j (suc x) z≤n = {!!}
  ij≤injmx m (suc i) j 0F ()
  ij≤injmx m (suc i) j (suc x) (s≤s i≤x) 
    rewrite sym (suc-i+Gj i j) = s≤s (ij≤injmx m i j x i≤x)

  sweakeni : ∀ m (j : Fin (suc m)) → CSType n i → CSType (n +ℕ m) (i +𝔾 j)
  tweakeni : ∀ m → CTType n → CTType (n +ℕ m)

  sweakeni m j (xmt d t s) = xmt d (tweakeni m t) (sweakeni m 0F s)
  sweakeni m j end = end
  sweakeni{i = i} m j (rec s) with (sweakeni m j s)
  ... | swi rewrite sym (suc-i+Gj i j) = rec swi
  sweakeni m j (var x i≤x) = var (inject+ m x) (ij≤injmx m _ j x i≤x)

  tweakeni m TInt = TInt
  tweakeni m (TChn s) = TChn (sweakeni m 0F s)

  sweakenn : ∀ m (j : Fin (suc (n +ℕ m))) → CSType n (fromℕ n) → CSType (n +ℕ m) j
  sweakenn m j (xmt d t s) = xmt d {!!} (sweakenn m 0F {!!})
  sweakenn m j end = {!!}
  sweakenn m j (rec s) = {!!}
  sweakenn m j (var x i≤x) = {!!}

  ssubst : Fin (suc n) → CSType 0 0F → CSType (suc n) (inject₁ i) → CSType n i
  tsubst : Fin (suc n) → CSType 0 0F → CTType (suc n) → CTType n

  ssubst j s₀ (xmt d t s) = xmt d (tsubst j s₀ t) (ssubst j s₀ s)
  ssubst j s₀ end = end
  ssubst j s₀ (rec s) = rec (ssubst (suc j) s₀ s)
  ssubst {n} 0F s₀ (var 0F i≤x) = {!sweak!}
  ssubst {n} 0F s₀ (var (suc x) i≤x) = {!!}
  ssubst {n} (suc j) s₀ (var 0F i≤x) = {!!}
  ssubst {n} (suc j) s₀ (var (suc x) i≤x) = {!!}

  tsubst j s₀ TInt = TInt
  tsubst j s₀ (TChn s) = TChn (ssubst j s₀ s)


  unfold : (s : CSType n i) (σ : CSType n i → CSType 0 0F) → CSType 0 0F
  unfold (xmt d t s) σ = σ (xmt d t s)
  unfold (rec s) σ = unfold s (σ ∘ {!ssubst!})
  unfold {i = 0F} (var j z≤n) σ = σ (var j z≤n)
  unfold {i = suc i} (var 0F ()) σ
  unfold {i = suc i} (var (suc j) (s≤s i≤j)) σ = unfold (var j i≤j) {!!}
  unfold end σ = end

----------------------------------------------------------------------
-- auxiliaries for automatic rewriting

{- REWRITE n+1=suc-n #-}

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
  end : SType n

variable
  t : TType n
  s s₀ : SType n

----------------------------------------------------------------------
-- weakening

weakenS : ∀ m → SType n → SType (n +ℕ m)
weakenT : ∀ m → TType n → TType (n +ℕ m)

weakenS m (xmt d t s) = xmt d (weakenT m t) (weakenS m s)
weakenS m (rec s) = rec (weakenS m s)
weakenS m (var x) = var (inject+ m x)
weakenS m end = end

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
ssubst end i s0 = end

tsubst TInt i s₀ = TInt
tsubst (TChn s) i s₀ = TChn (ssubst s i s₀)

----------------------------------------------------------------------
-- contractivity

mutual
  data ContractiveT : TType n → Set where
    con-int : ContractiveT{n} TInt
    con-chn : Contractive 0F s → ContractiveT (TChn s)

  data Contractive : Fin (suc n) → SType n → Set where
    con-rec : Contractive (suc i) s → Contractive i (rec s)
    con-xmt : ContractiveT t → Contractive 0F s → Contractive i (xmt d t s)
    con-var : i ≤ inject₁ j → Contractive i (var j)
    con-end : Contractive i end

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
  cp2 = con-rec (con-xmt con-int (con-rec (con-var (s≤s z≤n))))

  sn2 : SType 0
  sn2 = (rec (xmt SND TInt (rec (var 0F))))

  cn2 : ¬ Contractive 0F sn2
  cn2 (con-rec (con-xmt con-int (con-rec (con-var ()))))

unfold : (s : SType n) (c : Contractive i s) (σ : SType n → SType 0) → SType 0
unfold (xmt d t s) (con-xmt ct c) σ = σ (xmt d t s)
unfold end con-end σ = end
unfold (rec s) (con-rec c) σ = unfold s c (σ ∘ λ sn' → ssubst sn' 0F (σ (rec s))) 
unfold {i = 0F} (var x) (con-var z≤n) σ = σ (var x)
unfold {i = suc i} (var 0F) (con-var ()) σ
unfold {i = suc i} (var (suc x)) (con-var (s≤s x₁)) σ = unfold (var x) (con-var x₁) (σ ∘ weaken1S)

module CheckUnfold where
  s1 : SType 0
  s1 = rec (xmt SND TInt (var 0F))
  c1 : Contractive 0F s1
  c1 = con-rec (con-xmt con-int (con-var z≤n))
  s2 : SType 0
  s2 = xmt SND TInt s1

  u-s1=s2 : unfold s1 c1 id ≡ s2
  u-s1=s2 = refl

  s3 : SType 0
  s3 = rec (rec (xmt SND TInt (var 0F)))
  c3 : Contractive 0F s3
  c3 = con-rec (con-rec (con-xmt con-int (con-var z≤n)))
  u-s3=s2 : unfold s3 c3 id ≡ s2
  u-s3=s2 = refl

infer-contractiveT : (t : TType n) → Dec (ContractiveT t)
infer-contractive : (s : SType n) (i : Fin (suc n)) → Dec (Contractive i s)

infer-contractive (xmt d t s) i 
  with infer-contractiveT t | infer-contractive s 0F
infer-contractive (xmt d t s) i | yes p | yes p₁ = yes (con-xmt p p₁)
infer-contractive (xmt d t s) i | yes p | no ¬p = no (λ { (con-xmt ct cs) → ¬p cs })
infer-contractive (xmt d t s) i | no ¬p | yes p = no (λ { (con-xmt ct cs) → ¬p ct })
infer-contractive (xmt d t s) i | no ¬p | no ¬p₁ = no (λ { (con-xmt ct cs) → ¬p₁ cs})
infer-contractive end i = yes con-end
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

infer-contractiveT TInt = yes con-int
infer-contractiveT (TChn s)
  with infer-contractive s 0F
infer-contractiveT (TChn s) | yes p = yes (con-chn p)
infer-contractiveT (TChn s) | no ¬p = no (λ { (con-chn cs) → ¬p cs })

module ExamplesInference where
  open Examples
  
  infer-p2 : infer-contractive sp2 0F ≡ yes cp2
  infer-p2 = refl

  -- infer-n2 : infer-contractive sn2 0F ≡ no cn2
  -- how?


SType' : ℕ → Set
SType' n = Σ (SType n) (λ s → ∃ λ i → Contractive i s)

unfold' : SType' n → (SType n → SType 0) → SType' 0
unfold' (xmt d t s , i , c) σ = σ (xmt d t s) , 0F , {!!}
unfold' (rec s , snd) σ
  with unfold' (s , {!!}) {!!}
... | usc = {!!}
unfold' (var x , snd) σ = (σ (var x)) , 0F , {!!}
unfold' (end , i , con-end) σ = end , 0F , con-end

----------------------------------------------------------------------
-- equivalence
variable
  t₁ t₂ t₁' t₂' : TType n
  s₁ s₂ : SType n

-- type equivalence
data EquivT (R : SType n → SType n → Set) : TType n → TType n → Set where
  eq-int  : EquivT R TInt TInt
  eq-chan : R s₁ s₂ → EquivT R (TChn s₁) (TChn s₂)

-- session type equivalence
data EquivS (R : SType n → SType n → Set) : SType n → SType n → Set where
  eq-xmt : (d : Dir) → EquivT R t₁ t₂ → R s₁ s₂ → EquivS R (xmt d t₁ s₁) (xmt d t₂ s₂)
  eq-end : EquivS R end end

-- record Equiv (s₁ s₂ : SType 0) : Set where
--   coinductive
--   field force : EquivS Equiv (unfold s₁) (unfold s₂)

-- open Equiv
