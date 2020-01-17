{-# OPTIONS --rewriting #-}
module DualContractive where

open import Data.Fin
open import Data.Maybe
open import Data.Nat hiding (_≤_ ; compare) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Function

open import Direction

open import Extensionality

open import Max hiding (n)

----------------------------------------------------------------------
-- see also https://github.com/zmthy/recursive-types/tree/ftfjp16
-- for encoding of recursive types

variable
  m n : ℕ
  i i' j : Fin n 

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
-- auxiliaries for automatic rewriting

{- REWRITE n+1=suc-n #-}

{-# REWRITE n+0=n #-}

-- inject+0-x=x : {x : Fin m} → inject+ 0 x ≡ x
-- inject+0-x=x {x = zero} = refl
-- inject+0-x=x {x = suc x} = cong suc inject+0-x=x

{- REWRITE inject+0-x=x #-}

----------------------------------------------------------------------
-- types and session types

data TType (n : ℕ) : Set 
data SType (n : ℕ) : Set

data TType n where
  TInt : TType n
  TChn : (S : SType n) → TType n

data SType n where
  xmt : (d : Dir) (T : TType n) (S : SType n) → SType n
  end : SType n
  rec : (S : SType (suc n)) → SType n
  var : (x : Fin n) → SType n

variable
  t T : TType n
  s s₀ S S₀ : SType n

----------------------------------------------------------------------
module Examples-Types where
  sint : SType n → SType n
  sint = xmt SND TInt

  -- μ X. !Int. X
  s1 : SType 0
  s1 = rec (sint (var 0F))

  -- μ X. μ Y. !Int. Y
  s2 : SType 0
  s2 = rec (rec (sint (var 0F)))

  -- μ X. μ Y. !Int. X
  s2a : SType 0
  s2a = rec (rec (sint (var 1F)))

  -- μ X. !Int. μ Y. X
  s3 : SType 0
  s3 = rec (sint (rec (var 1F)))

----------------------------------------------------------------------
-- weakening

increase : ∀ m → (x : Fin n) → Fin (n +ℕ m)
increase 0F x = x
increase (suc m) x = suc (increase m x)

increaseS : ∀ m → SType n → SType (n +ℕ m)
increaseT : ∀ m → TType n → TType (n +ℕ m)

increaseS m (xmt d t s) = xmt d (increaseT m t) (increaseS m s)
increaseS m (rec s) = rec (increaseS m s)
increaseS m (var x) = var (inject+ m x)
increaseS m end = end

increaseT m TInt = TInt
increaseT m (TChn s) = TChn (increaseS m s)

weakenS : ∀ m → SType n → SType (n +ℕ m)
weakenT : ∀ m → TType n → TType (n +ℕ m)

weakenS m (xmt d t s) = xmt d (weakenT m t) (weakenS m s)
weakenS m (rec s) = rec (weakenS m s)
weakenS m (var x) = var (increase m x)
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
ssubst {n} (var 0F) 0F s0 = increaseS n s0
ssubst {suc n} (var 0F) (suc i) s0 = var 0F
ssubst (var (suc x)) 0F s0 = var x
ssubst {suc n} (var (suc x)) (suc i) s0 = increaseS 1 (ssubst (var x) i s0)
ssubst end i s0 = end

tsubst TInt i s₀ = TInt
tsubst (TChn s) i s₀ = TChn (ssubst s i s₀)

----------------------------------------------------------------------
-- contractivity

mutual
  data ContractiveT : TType n → Set where
    con-int : ContractiveT{n} TInt
    con-chn : Contractive 0F S → ContractiveT (TChn S)

  data Contractive (i : Fin (suc n)) : SType n → Set where
    con-xmt : ContractiveT t → Contractive 0F s → Contractive i (xmt d t s)
    con-end : Contractive i end
    con-rec : Contractive (suc i) S → Contractive i (rec S)
    con-var : i ≤ inject₁ j → Contractive i (var j)

----------------------------------------------------------------------
module Examples-Contractivity where
  open Examples-Types
  
  cn1 : ¬ Contractive {2} 1F (var 0F)
  cn1 (con-var ())

  cp1 : Contractive {2} 0F (var 1F)
  cp1 = con-var z≤n

  cp0 : Contractive {2} 0F (var 0F)
  cp0 = con-var z≤n

  cs1 : Contractive 0F s1
  cs1 = con-rec (con-xmt con-int (con-var z≤n))

  cs2 : Contractive 0F s2
  cs2 = con-rec (con-rec (con-xmt con-int (con-var z≤n)))

  cs2a : Contractive 0F s2a
  cs2a = con-rec (con-rec (con-xmt con-int (con-var z≤n)))

  sp2 : SType 0
  sp2 = s3

  cp2 : Contractive 0F sp2
  cp2 = con-rec (con-xmt con-int (con-rec (con-var (s≤s z≤n))))

  sn2 : SType 0
  sn2 = (rec (xmt SND TInt (rec (var 0F))))

  cn2 : ¬ Contractive 0F sn2
  cn2 (con-rec (con-xmt con-int (con-rec (con-var ()))))

----------------------------------------------------------------------
-- unfolding to first non-rec constructor

unfold : (s : SType n) (c : Contractive i s) (σ : SType n → SType 0) → SType 0
unfold (xmt d t s) (con-xmt ct c) σ = σ (xmt d t s)
unfold end con-end σ = end
unfold (rec s) (con-rec c) σ = unfold s c (σ ∘ λ sn' → ssubst sn' 0F (σ (rec s))) 
unfold {i = 0F} (var x) (con-var z≤n) σ = σ (var x)
unfold {i = suc i} (var 0F) (con-var ()) σ
unfold {i = suc i} (var (suc x)) (con-var (s≤s x₁)) σ = unfold (var x) (con-var x₁) (σ ∘ increaseS 1)

unfold₀ : (S : SType 0) (c : Contractive 0F S) → SType 0
unfold₀ S c = unfold S c id

----------------------------------------------------------------------
module Examples-Unfold where
  open Examples-Types

  c1 : Contractive 0F s1
  c1 = con-rec (con-xmt con-int (con-var z≤n))
  s11 : SType 0
  s11 = xmt SND TInt s1

  u-s1=s11 : unfold s1 c1 id ≡ s11
  u-s1=s11 = refl

  c2 : Contractive 0F s2
  c2 = con-rec (con-rec (con-xmt con-int (con-var z≤n)))
  u-s2=s11 : unfold s2 c2 id ≡ s11
  u-s2=s11 = cong (xmt SND TInt) (cong rec (cong (xmt SND TInt) refl))
----------------------------------------------------------------------
-- contractivity is decidable

infer-contractiveT : (t : TType n) → Dec (ContractiveT t)
infer-contractive : (s : SType n) (i : Fin (suc n)) → Dec (Contractive i s)

infer-contractiveT TInt = yes con-int
infer-contractiveT (TChn s)
  with infer-contractive s 0F
infer-contractiveT (TChn s) | yes p = yes (con-chn p)
infer-contractiveT (TChn s) | no ¬p = no (λ { (con-chn cs) → ¬p cs })

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

----------------------------------------------------------------------
module Examples-Inference where
  open Examples-Contractivity
  
  infer-p2 : infer-contractive sp2 0F ≡ yes cp2
  infer-p2 = refl

  infer-n2 : infer-contractive sn2 0F ≡ no cn2
  infer-n2 = cong no (ext (λ { (con-rec (con-xmt con-int (con-rec (con-var ())))) }))

----------------------------------------------------------------------
-- RT: if a type is contractive at level i, then it is also contractive at any smaller level

c-weakenS : {S : SType n} (i' : Fin′ i) → Contractive i S → Contractive (inject i') S
c-weakenS i' (con-rec cis) = con-rec (c-weakenS (suc i') cis)
c-weakenS i' (con-xmt x cis) = con-xmt x cis
c-weakenS i' con-end = con-end
c-weakenS {i = suc i} i' (con-var {0F} ())
c-weakenS {i = suc i} 0F (con-var {suc n} (s≤s x)) = con-var z≤n
c-weakenS {i = suc i} (suc i') (con-var {suc n} (s≤s x)) = con-var (s≤s (trans-< x))

c-weakenS₁ : {S : SType n} → Contractive (suc i) S → Contractive (inject₁ i) S
c-weakenS₁ (con-rec cis) = con-rec (c-weakenS₁ cis)
c-weakenS₁ (con-xmt x cis) = con-xmt x cis
c-weakenS₁ con-end = con-end
c-weakenS₁ {0F} {()} (con-var x)
c-weakenS₁ {suc n} {0F} (con-var x) = con-var z≤n
c-weakenS₁ {suc n} {suc i} (con-var x) = con-var (pred-≤ x)

c-weakenS! : {S : SType n} → Contractive i S → Contractive 0F S
c-weakenS! {i = 0F} (con-rec cis) = con-rec cis
c-weakenS! {i = suc i} (con-rec cis) = con-rec (c-weakenS 1F cis)
c-weakenS! {n} {i} (con-xmt x cis) = con-xmt x cis
c-weakenS! {n} {i} con-end = con-end
c-weakenS! {n} {i} (con-var x) = con-var z≤n

----------------------------------------------------------------------
-- single substitution of j ↦ Sj

subst1T : (T : TType (suc n)) (j : Fin (suc n)) (Sj : SType n) → TType n
subst1S : (S : SType (suc n)) (j : Fin (suc n)) (Sj : SType n) → SType n

subst1T TInt j Sj = TInt
subst1T (TChn S) j Sj = TChn (subst1S S j Sj)

subst1S (xmt d T S) j Sj = xmt d (subst1T T j Sj) (subst1S S j Sj)
subst1S end j Sj = end
subst1S (rec S) j Sj = rec (subst1S S (suc j) (weaken1S Sj))
subst1S (var x) j Sj
  with compare x j
subst1S (var .(inject least)) j Sj | less .j least = var (inject! least)
subst1S (var x) .x Sj | equal .x = Sj
subst1S (var (suc x)) .(inject least) Sj | greater .(suc x) least = var x

{- the termination checker doesnt like this:
subst1S (var 0F) 0F Sj = Sj
subst1S {suc n} (var 0F) (suc j) Sj = var 0F 
subst1S (var (suc x)) 0F Sj = var x
subst1S (var (suc x)) (suc j) Sj = subst1S (var (inject₁ x)) (inject₁ j) Sj
-}

unfold1S : (S : SType 0) → SType 0
unfold1S (xmt d T S) = xmt d T S
unfold1S end = end
unfold1S (rec S) = subst1S S 0F (rec S)

unfoldSS : (S : SType n) → SType n
unfoldSS (xmt d T S) = xmt d T S
unfoldSS end = end
unfoldSS (rec S)
  with unfoldSS S
... | ih = subst1S ih 0F (rec ih)
unfoldSS (var x) = var x

----------------------------------------------------------------------
-- max index substitution

subst-maxT : (Sm : SType n) (T : TType (suc n)) → TType n
subst-maxS : (Sm : SType n) (S : SType (suc n)) → SType n

subst-maxT Sm TInt = TInt
subst-maxT Sm (TChn S) = TChn (subst-maxS Sm S)

subst-maxS Sm (xmt d T S) = xmt d (subst-maxT Sm T) (subst-maxS Sm S)
subst-maxS Sm end = end
subst-maxS Sm (rec S) = rec (subst-maxS (weaken1S Sm) S)
subst-maxS Sm (var x)
  with max? x
subst-maxS Sm (var x) | yes p = Sm
subst-maxS Sm (var x) | no ¬p = var (reduce ¬p)


unfoldmS : (S : SType 0) → SType 0
unfoldmS (xmt d T S) = xmt d T S
unfoldmS end = end
unfoldmS (rec S) = subst-maxS (rec S) S

----------------------------------------------------------------------
-- max substitution preserves contractivity

contr-weakenT : ContractiveT T → ContractiveT (weakenT 1 T)
contr-weakenS : Contractive i S → Contractive (suc i) (weaken1S S)

contr-weakenT con-int = con-int
contr-weakenT (con-chn x) = con-chn (c-weakenS! (contr-weakenS x))

contr-weakenS (con-xmt x cs) = con-xmt (contr-weakenT x) (c-weakenS! (contr-weakenS cs))
contr-weakenS con-end = con-end
contr-weakenS (con-rec cs) = con-rec (contr-weakenS cs)
contr-weakenS {n}{i} {S = var j} (con-var x) = con-var (s≤s x)


subst-contr-mT : 
  {T : TType (suc n)} (c : ContractiveT T)
  {S' : SType n} (c' : Contractive i S')
    → ContractiveT (subst-maxT S' T)

subst-contr-mS :
  -- {i : Fin (suc (suc n))}
  {S : SType (suc n)} (c : Contractive (inject₁ i) S)
  {S' : SType n} (c' : Contractive i S')
    → Contractive i (subst-maxS S' S)

subst-contr-mT con-int csm = con-int
subst-contr-mT (con-chn x) csm = con-chn (c-weakenS! (subst-contr-mS x (c-weakenS! csm)))

subst-contr-mS (con-xmt x cs) csm = con-xmt (subst-contr-mT x csm) (subst-contr-mS cs (c-weakenS! csm))
subst-contr-mS con-end csm = con-end
subst-contr-mS (con-rec cs) csm = con-rec (subst-contr-mS cs (contr-weakenS csm))
subst-contr-mS {S = var j} (con-var x) csm
  with max? j
subst-contr-mS {i = _} {var j} (con-var x) csm | yes p = csm
subst-contr-mS {i = _} {var j} (con-var x) csm | no ¬p = con-var (lemma-reduce x ¬p)

-- one step unfolding preserves contractivity

unfold-contr : Contractive i S → Contractive i (unfoldmS S)
unfold-contr (con-xmt x c) = con-xmt x c
unfold-contr con-end = con-end
unfold-contr (con-rec c) = subst-contr-mS (c-weakenS₁ c) (con-rec c)

-- multiple unfolding 

unfold! : (S : SType n) (σ : SType n → SType 0) → SType 0
unfold! (xmt d T S) σ = σ (xmt d T S)
unfold! end σ = end
unfold! (rec S) σ = unfold! S (σ ∘ subst-maxS (rec S))
unfold! (var x) σ = σ (var x)

unfold!-contr : Contractive i S → Contractive i (unfold! S id)
unfold!-contr (con-xmt x cs) = con-xmt x cs
unfold!-contr con-end = con-end
unfold!-contr (con-rec cs) = {!!}

-- multiple unfolding preserves contractivity

SCType : (n : ℕ) → Fin (suc n) → Set
SCType n i = Σ (SType n) (Contractive i)

unfold!! : (SC : SCType n i) → (SCType n i → SCType 0 0F) → SCType 0 0F
unfold!! SC@(xmt d T S , con-xmt x cs) σ = σ SC
unfold!! (end , con-end) σ = end , con-end
unfold!! (rec S , con-rec cs) σ =
  unfold!! (S , cs) (σ ∘ λ{ (S' , c') → (subst-maxS (rec S) S') , (subst-contr-mS (c-weakenS₁ c') (con-rec cs)) })
unfold!! SC@(var x , con-var x₁) σ = σ SC

----------------------------------------------------------------------
-- equivalence requires multiple unfolding

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
