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

open import Types.Direction

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
n+sucm=sucn+m zero m = refl
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
  s1 = rec (sint (var zero))

  -- μ X. μ Y. !Int. Y
  s2 : SType 0
  s2 = rec (rec (sint (var zero)))

  -- μ X. μ Y. !Int. X
  s2a : SType 0
  s2a = rec (rec (sint (var (suc zero))))

  -- μ X. !Int. μ Y. X
  s3 : SType 0
  s3 = rec (sint (rec (var (suc zero))))

module Alternative-Substitution where

  -- analogous to https://plfa.github.io/DeBruijn/

  -- extending a map by an identity segment

  extV : (Fin m → Fin n) → (Fin (suc m) → Fin (suc n))
  extV ρ zero = zero
  extV ρ (suc i) = suc (ρ i)

  -- renaming / can be used for weakening one binding as @rename suc@

  renameT : (Fin m → Fin n) → TType m → TType n
  renameS : (Fin m → Fin n) → SType m → SType n

  renameT ρ TInt = TInt
  renameT ρ (TChn S) = TChn (renameS ρ S)
  
  renameS ρ (xmt d T S) = xmt d (renameT ρ T) (renameS ρ S)
  renameS ρ end = end
  renameS ρ (rec S) = rec (renameS (extV ρ) S)
  renameS ρ (var x) = var (ρ x)

  -- extending a map from variables to terms

  extS : (Fin m → SType n) → (Fin (suc m) → SType (suc n))
  extS σ zero = var zero
  extS σ (suc i) = renameS suc (σ i)

  -- simultaneous substitution

  substT : (Fin m → SType n) → TType m → TType n
  substS : (Fin m → SType n) → SType m → SType n

  substT σ TInt = TInt
  substT σ (TChn S) = TChn (substS σ S)

  substS σ (xmt d T S) = xmt d (substT σ T) (substS σ S)
  substS σ end = end
  substS σ (rec S) = rec (substS (extS σ) S)
  substS σ (var x) = σ x

  -- single substitution

  mk-σ : SType n → Fin (suc n) → SType n
  mk-σ S' zero = S'
  mk-σ S' (suc x) = var x

  substT1 : SType n → TType (suc n) → TType n
  substT1 S' T = substT (mk-σ S') T

  substS1 : SType n → SType (suc n) → SType n
  substS1 S' S = substS (mk-σ S') S

----------------------------------------------------------------------
-- weakening

increase : ∀ m → (x : Fin n) → Fin (n +ℕ m)
increase zero x = x
increase (suc m) x = suc (increase m x)

increaseS : ∀ m → SType n → SType (n +ℕ m)
increaseT : ∀ m → TType n → TType (n +ℕ m)

increaseS m (xmt d t s) = xmt d (increaseT m t) (increaseS m s)
increaseS m (rec s) = rec (increaseS m s)
increaseS m (var x) = var (inject+ m x) -- should say increase here
increaseS m end = end

increaseT m TInt = TInt
increaseT m (TChn s) = TChn (increaseS m s)

-- weaken m is used to push a (closed) term under m new binders
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

-- this one behaves correctly
weaken'S : ∀ m → Fin (suc n) → SType n → SType (n +ℕ m)
weaken'T : ∀ m → Fin (suc n) → TType n → TType (n +ℕ m)

weaken'S m i (xmt d T S) = xmt d (weaken'T m i T) (weaken'S m i S)
weaken'S m i end = end
weaken'S m i (rec S) = rec (weaken'S m (suc i) S)
weaken'S {suc n} m zero (var x) = var (increase m x)
weaken'S {suc n} m (suc i) (var x)
  with compare i x
weaken'S {suc n} m (suc .(inject least)) (var x) | less .x least = var (increase m x)
weaken'S {suc n} m (suc i) (var .i) | equal .i = var (inject+ m i)
weaken'S {suc n} m (suc i) (var .(inject least)) | greater .i least = var (inject+ m (inject least))


weaken'T m i TInt = TInt
weaken'T m i (TChn S) = TChn (weaken'S m i S)

weaken'S0 : ∀ m → SType n → SType (n +ℕ m)
weaken'S0 m S = weaken'S m (fromℕ _) S

----------------------------------------------------------------------
-- examples

module Examples-Weakening where

  sv0 sv1 : SType 1
  sv0 = rec (var zero)
  sv1 = rec (var (suc zero))

  sv0-w : SType 2
  sv0-w = weaken'S 1 zero sv0

  step0 : weaken'S{2} 1 zero (var zero) ≡ var (suc zero)
        × weaken'S{2} 1 zero (var (suc zero)) ≡ var (suc (suc zero))
  step0 = refl , refl

  step1 : weaken'S{2} 1 (suc zero) (var zero) ≡ var zero
        × weaken'S{2} 1 (suc zero) (var (suc zero)) ≡ var (suc (suc zero))
  step1 = refl , refl

  stepr1 : weaken'S 1 zero sv0 ≡ rec (var zero)
         × weaken'S 1 zero sv1 ≡ rec (var (suc (suc zero)))
  stepr1 = refl , refl

  stepr2 : weaken'S{3} 1 zero (rec (rec (var zero))) ≡ rec (rec (var zero))
         × weaken'S{3} 1 zero (rec (rec (var (suc zero)))) ≡ rec (rec (var (suc zero)))
         × weaken'S{3} 1 zero (rec (rec (var (suc (suc zero))))) ≡ rec (rec (var (suc (suc (suc zero)))))
  stepr2 = refl , refl , refl

  sx1 : SType 0
  sx1 = rec (xmt SND TInt (var zero))

  sx1-w : SType 1
  sx1-w = rec (xmt SND TInt (var zero))

  sx1=sx1-w : sx1-w ≡ weaken'S 1 zero sx1
  sx1=sx1-w = refl

  sx2 : SType 1
  sx2 = xmt SND TInt (var zero)

  sx2-w1 : SType 2
  sx2-w1 = xmt SND TInt (var (suc zero))

  sx2-w0 : SType 2
  sx2-w0 = xmt SND TInt (var zero)

  sx2=w : sx2-w1 ≡ weaken'S 1 zero sx2
        × sx2-w0 ≡ weaken'S 1 (suc zero) sx2
  sx2=w = refl , refl

  open Alternative-Substitution 

  step0-r : renameS suc sv0 ≡ rec (var zero)
          × renameS suc sv1 ≡ rec (var (suc (suc zero)))
  step0-r = refl , refl

  step1-r : renameS{1} suc (rec (rec (var zero))) ≡ (rec (rec (var zero)))
          × renameS{1} suc (rec (rec (var (suc zero)))) ≡ (rec (rec (var (suc zero))))
          × renameS{1} suc (rec (rec (var (suc (suc zero))))) ≡ (rec (rec (var (suc (suc (suc zero))))))
  step1-r = refl , refl , refl

----------------------------------------------------------------------
-- contractivity

mutual
  data ContractiveT {n} : TType n → Set where
    con-int : ContractiveT TInt
    con-chn : Contractive zero S → ContractiveT (TChn S)

  data Contractive (i : Fin (suc n)) : SType n → Set where
    con-xmt : ContractiveT t → Contractive zero s → Contractive i (xmt d t s)
    con-end : Contractive i end
    con-rec : Contractive (suc i) S → Contractive i (rec S)
    con-var : i ≤ inject₁ j → Contractive i (var j)

----------------------------------------------------------------------
module Examples-Contractivity where
  open Examples-Types
  
  cn1 : ¬ Contractive {2} (suc zero) (var zero)
  cn1 (con-var ())

  cp1 : Contractive {2} zero (var (suc zero))
  cp1 = con-var z≤n

  cp0 : Contractive {2} zero (var zero)
  cp0 = con-var z≤n

  cs1 : Contractive zero s1
  cs1 = con-rec (con-xmt con-int (con-var z≤n))

  cs2 : Contractive zero s2
  cs2 = con-rec (con-rec (con-xmt con-int (con-var z≤n)))

  cs2a : Contractive zero s2a
  cs2a = con-rec (con-rec (con-xmt con-int (con-var z≤n)))

  sp2 : SType 0
  sp2 = s3

  cp2 : Contractive zero sp2
  cp2 = con-rec (con-xmt con-int (con-rec (con-var (s≤s z≤n))))

  sn2 : SType 0
  sn2 = (rec (xmt SND TInt (rec (var zero))))

  cn2 : ¬ Contractive zero sn2
  cn2 (con-rec (con-xmt con-int (con-rec (con-var ()))))

module Alternative-Unfolding where
  open Alternative-Substitution

  -- one top-level unfolding if possible

  unfold₁ : SType n → SType n
  unfold₁ (rec S) = substS1 (rec S) S
  unfold₁ S@(xmt d T x) = S
  unfold₁ S@end = S
  unfold₁ S@(var x) = S

  -- unfold all the way

  unfold : (S : SType n) (σ : SType n → SType m) → SType m
  unfold S@(xmt d T S') σ = σ S
  unfold end σ = end
  unfold (rec S) σ = unfold S (σ ∘ substS1 (rec S))
  unfold S@(var x) σ = σ S

  unfold₀ : SType n → SType n
  unfold₀ S = unfold S id

  

----------------------------------------------------------------------
-- substitution

ssubst : SType (suc n) → Fin (suc n) → SType 0 → SType n
tsubst : TType (suc n) → Fin (suc n) → SType 0 → TType n

ssubst (xmt d t s) i s0 = xmt d (tsubst t i s0) (ssubst s i s0)
ssubst (rec s) i s0 = rec (ssubst s (suc i) s0)
ssubst {n} (var zero) zero s0 = increaseS n s0
ssubst {suc n} (var zero) (suc i) s0 = var zero
ssubst (var (suc x)) zero s0 = var x
ssubst {suc n} (var (suc x)) (suc i) s0 = increaseS 1 (ssubst (var x) i s0)
ssubst end i s0 = end

tsubst TInt i s₀ = TInt
tsubst (TChn s) i s₀ = TChn (ssubst s i s₀)


----------------------------------------------------------------------
-- unfolding to first non-rec constructor

unfold : (s : SType n) (c : Contractive i s) (σ : SType n → SType 0) → SType 0
unfold (xmt d t s) (con-xmt ct c) σ = σ (xmt d t s)
unfold end con-end σ = end
unfold (rec s) (con-rec c) σ = unfold s c (σ ∘ λ sn' → ssubst sn' zero (σ (rec s))) 
unfold {i = zero} (var x) (con-var z≤n) σ = σ (var x)
unfold {i = suc i} (var zero) (con-var ()) σ
unfold {i = suc i} (var (suc x)) (con-var (s≤s x₁)) σ = unfold (var x) (con-var x₁) (σ ∘ increaseS 1)

unfold₀ : (S : SType 0) (c : Contractive zero S) → SType 0
unfold₀ S c = unfold S c id

----------------------------------------------------------------------
module Examples-Unfold where
  open Examples-Types

  c1 : Contractive zero s1
  c1 = con-rec (con-xmt con-int (con-var z≤n))
  s11 : SType 0
  s11 = xmt SND TInt s1

  u-s1=s11 : unfold s1 c1 id ≡ s11
  u-s1=s11 = refl

  c2 : Contractive zero s2
  c2 = con-rec (con-rec (con-xmt con-int (con-var z≤n)))
  u-s2=s11 : unfold s2 c2 id ≡ s11
  u-s2=s11 = cong (xmt SND TInt) (cong rec (cong (xmt SND TInt) refl))
----------------------------------------------------------------------
-- contractivity is decidable

infer-contractiveT : (t : TType n) → Dec (ContractiveT t)
infer-contractive : (s : SType n) (i : Fin (suc n)) → Dec (Contractive i s)

infer-contractiveT TInt = yes con-int
infer-contractiveT (TChn s)
  with infer-contractive s zero
infer-contractiveT (TChn s) | yes p = yes (con-chn p)
infer-contractiveT (TChn s) | no ¬p = no (λ { (con-chn cs) → ¬p cs })

infer-contractive (xmt d t s) i 
  with infer-contractiveT t | infer-contractive s zero
infer-contractive (xmt d t s) i | yes p | yes p₁ = yes (con-xmt p p₁)
infer-contractive (xmt d t s) i | yes p | no ¬p = no (λ { (con-xmt ct cs) → ¬p cs })
infer-contractive (xmt d t s) i | no ¬p | yes p = no (λ { (con-xmt ct cs) → ¬p ct })
infer-contractive (xmt d t s) i | no ¬p | no ¬p₁ = no (λ { (con-xmt ct cs) → ¬p₁ cs})
infer-contractive end i = yes con-end
infer-contractive (rec s) i
  with infer-contractive s (suc i)
infer-contractive (rec s) i | yes p = yes (con-rec p)
infer-contractive (rec s) i | no ¬p = no (λ { (con-rec c) → ¬p c })
infer-contractive (var x) zero = yes (con-var z≤n)
infer-contractive (var zero) (suc i) = no (λ { (con-var ()) })
infer-contractive (var (suc x)) (suc i)
  with infer-contractive (var x) i
infer-contractive (var (suc x)) (suc i) | yes (con-var x₁) = yes (con-var (s≤s x₁))
infer-contractive (var (suc x)) (suc i) | no ¬p = no (λ { (con-var (s≤s y)) → ¬p (con-var y) })

----------------------------------------------------------------------
module Examples-Inference where
  open Examples-Contractivity
  
  infer-p2 : infer-contractive sp2 zero ≡ yes cp2
  infer-p2 = refl

  infer-n2 : infer-contractive sn2 zero ≡ no cn2
  infer-n2 = cong no (ext (λ { (con-rec (con-xmt con-int (con-rec (con-var ())))) }))

----------------------------------------------------------------------
-- RT: if a type is contractive at level i, then it is also contractive at any smaller level

c-weakenS : {S : SType n} (i' : Fin′ i) → Contractive i S → Contractive (inject i') S
c-weakenS i' (con-rec cis) = con-rec (c-weakenS (suc i') cis)
c-weakenS i' (con-xmt x cis) = con-xmt x cis
c-weakenS i' con-end = con-end
c-weakenS {i = suc i} i' (con-var {zero} ())
c-weakenS {i = suc i} zero (con-var {suc n} (s≤s x)) = con-var z≤n
c-weakenS {i = suc i} (suc i') (con-var {suc n} (s≤s x)) = con-var (s≤s (trans-< x))

c-weakenS₁ : {S : SType n} → Contractive (suc i) S → Contractive (inject₁ i) S
c-weakenS₁ (con-rec cis) = con-rec (c-weakenS₁ cis)
c-weakenS₁ (con-xmt x cis) = con-xmt x cis
c-weakenS₁ con-end = con-end
c-weakenS₁ {zero} {()} (con-var x)
c-weakenS₁ {suc n} {zero} (con-var x) = con-var z≤n
c-weakenS₁ {suc n} {suc i} (con-var x) = con-var (pred-≤ x)

c-weakenS! : {S : SType n} → Contractive i S → Contractive zero S
c-weakenS! {i = zero} (con-rec cis) = con-rec cis
c-weakenS! {i = suc i} (con-rec cis) = con-rec (c-weakenS (suc zero) cis)
c-weakenS! {n} {i} (con-xmt x cis) = con-xmt x cis
c-weakenS! {n} {i} con-end = con-end
c-weakenS! {n} {i} (con-var x) = con-var z≤n



ct-weaken+ : {T : TType n} → ContractiveT T → ContractiveT (weaken'T 1 zero T)
c-weaken+ : {S : SType n} → Contractive i S → Contractive (suc i) (weaken'S 1 zero S)

ct-weaken+ con-int = con-int
ct-weaken+ (con-chn x) = con-chn (c-weakenS! (c-weaken+ x))

c-weaken+ (con-xmt x cis) = con-xmt (ct-weaken+ x) (c-weakenS! (c-weaken+ cis))
c-weaken+ con-end = con-end
c-weaken+ (con-rec cis) = con-rec {!!} -- gives a problem: (c-weaken+ {!cis!})
c-weaken+ {suc n} {i} {var j} (con-var i≤j) = con-var (s≤s i≤j)

module Alternative-Multiple-Substitution-Preserves where

  open Alternative-Substitution

  subst-contr-T :
    {T : TType m}
    (σ : Fin m → SType n)
    (γ : (j : Fin m) → Contractive i (σ j))
    (ct : ContractiveT T)
    → ContractiveT (substT σ T)

  subst-contr-S : ∀ {k} →
    (σ : Fin m → SType n)
    (γ : (j : Fin m) → Contractive k (σ j))
    (c : Contractive zero S)
    → Contractive k (substS σ S)

  subst-contr-T σ γ con-int = con-int
  subst-contr-T σ γ (con-chn cs) = con-chn (subst-contr-S σ (c-weakenS! ∘ γ) cs)

  subst-contr-S σ γ (con-xmt ct cs) =
    con-xmt (subst-contr-T σ γ ct) (subst-contr-S σ (c-weakenS! ∘ γ) cs)
  subst-contr-S σ γ con-end = con-end
  subst-contr-S σ γ (con-rec cs) = con-rec (subst-contr-S (extS σ) {!extS!} (c-weakenS₁ cs))
  subst-contr-S σ γ (con-var{j} x) = γ j

module Alternative-Substitution-Preserves where

  open Alternative-Substitution

  subst-contr-T : 
    {S' : SType n} (c' : Contractive i S')
    {T : TType (suc n)} (c : ContractiveT T)
      → ContractiveT (substT1 S' T)
  subst-contr-S :
    {S' : SType n} (c' : Contractive i S')
    {S : SType (suc n)} (c : Contractive (inject₁ i) S)
      → Contractive i (substS1 S' S)

  subst-contr-T c' con-int = con-int
  subst-contr-T c' (con-chn x) = con-chn (subst-contr-S (c-weakenS! c') x)

  subst-contr-S c' (con-xmt ct cs) =
    con-xmt (subst-contr-T c' ct) (subst-contr-S (c-weakenS! c') cs)
  subst-contr-S c' con-end = con-end
  subst-contr-S c' (con-rec c) = con-rec {!!} -- (subst-contr-S {!!} {!c!})
  subst-contr-S c' (con-var x) = {!!}

module Alternative-SingleSubstitution where
  ----------------------------------------------------------------------
  -- single substitution of j ↦ Sj

  subst1T : (T : TType (suc n)) (j : Fin (suc n)) (Sj : SType n) → TType n
  subst1S : (S : SType (suc n)) (j : Fin (suc n)) (Sj : SType n) → SType n

  subst1T TInt j Sj = TInt
  subst1T (TChn S) j Sj = TChn (subst1S S j Sj)

  subst1S (xmt d T S) j Sj = xmt d (subst1T T j Sj) (subst1S S j Sj)
  subst1S end j Sj = end
  subst1S (rec S) j Sj = rec (subst1S S (suc j) (weaken'S 1 zero Sj))
  subst1S (var x) j Sj
    with compare x j
  subst1S (var .(inject least)) j Sj | less .j least = var (inject! least)
  subst1S (var x) .x Sj | equal .x = Sj
  subst1S (var (suc x)) .(inject least) Sj | greater .(suc x) least = var x

  {- the termination checker doesnt like this:
  subst1S (var zero) zero Sj = Sj
  subst1S {suc n} (var zero) (suc j) Sj = var zero 
  subst1S (var (suc x)) zero Sj = var x
  subst1S (var (suc x)) (suc j) Sj = subst1S (var (inject₁ x)) (inject₁ j) Sj
  -}

  unfold1S : (S : SType 0) → SType 0
  unfold1S (xmt d T S) = xmt d T S
  unfold1S end = end
  unfold1S (rec S) = subst1S S zero (rec S)

  unfoldSS : (S : SType n) → SType n
  unfoldSS (xmt d T S) = xmt d T S
  unfoldSS end = end
  unfoldSS (rec S)
    with unfoldSS S
  ... | ih = subst1S ih zero (rec ih)
  unfoldSS (var x) = var x

----------------------------------------------------------------------
-- max index substitution

subst-maxT : (Sm : SType n) (T : TType (suc n)) → TType n
subst-maxS : (Sm : SType n) (S : SType (suc n)) → SType n

subst-maxT Sm TInt = TInt
subst-maxT Sm (TChn S) = TChn (subst-maxS Sm S)

subst-maxS Sm (xmt d T S) = xmt d (subst-maxT Sm T) (subst-maxS Sm S)
subst-maxS Sm end = end
subst-maxS Sm (rec S) = rec (subst-maxS (weaken'S 1 zero Sm) S)
subst-maxS Sm (var x)
  with max? x
subst-maxS Sm (var x) | yes p = Sm
subst-maxS Sm (var x) | no ¬p = var (reduce ¬p)


unfoldmS : (S : SType n) → SType n
unfoldmS (xmt d T S) = xmt d T S
unfoldmS end = end
unfoldmS (rec S) = subst-maxS (rec S) S
unfoldmS {suc n} (var x) = var x

----------------------------------------------------------------------
-- max substitution preserves contractivity

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
subst-contr-mS (con-rec cs) csm = con-rec (subst-contr-mS cs (c-weaken+ csm))
subst-contr-mS {S = var j} (con-var x) csm
  with max? j
subst-contr-mS {i = _} {var j} (con-var x) csm | yes p = csm
subst-contr-mS {i = _} {var j} (con-var x) csm | no ¬p = con-var (lemma-reduce x ¬p)

-- one step unfolding preserves contractivity

unfold-contr : Contractive i S → Contractive i (unfoldmS S)
unfold-contr (con-xmt x c) = con-xmt x c
unfold-contr con-end = con-end
unfold-contr (con-rec c) = subst-contr-mS (c-weakenS₁ c) (con-rec c)
unfold-contr (con-var x) = {!!}

-- multiple unfolding 
-- terminates even for non-contractive types because it delays the substitution

unfold! : (S : SType n) (σ : SType n → SType 0) → SType 0
unfold! (xmt d T S) σ = σ (xmt d T S)
unfold! end σ = end
unfold! (rec S) σ = unfold! S (σ ∘ subst-maxS (rec S))
unfold! (var x) σ = σ (var x)

-- unclear how this could be completed
-- unfold!-contr : Contractive i S → Contractive i (unfold! S id)
-- unfold!-contr (con-xmt x cs) = con-xmt x cs
-- unfold!-contr con-end = con-end
-- unfold!-contr (con-rec cs) = {!!}

-- multiple unfolding preserves contractivity

TCType : (n : ℕ) → Set
TCType n = Σ (TType n) ContractiveT

SCType : (n : ℕ) → Fin (suc n) → Set
SCType n i = Σ (SType n) (Contractive i)

unfold!! : (SC : SCType n i) → (SCType n i → SCType 0 zero) → SCType 0 zero
unfold!! SC@(xmt d T S , con-xmt x cs) σ = σ SC
unfold!! (end , con-end) σ = end , con-end
unfold!! (rec S , con-rec cs) σ =
  unfold!! (S , cs) (σ ∘ λ{ (S' , c') → (subst-maxS (rec S) S') , (subst-contr-mS (c-weakenS₁ c') (con-rec cs)) })
unfold!! SC@(var x , con-var x₁) σ = σ SC

{-# TERMINATING #-}
unfold!!! : ∀ {m n : ℕ} → SCType (n +ℕ m) zero → (SCType (n +ℕ m) zero → SCType m zero) → SCType m zero
unfold!!! SC@(xmt d T S , con-xmt x cs) σ = σ SC
unfold!!! (end , con-end) σ = end , con-end
unfold!!! (rec S , con-rec cs) σ =
  unfold!!! (S , c-weakenS₁ cs) (σ ∘ λ SC → (subst-maxS (rec S) (proj₁ SC)) , (subst-contr-mS (proj₂ SC) (con-rec cs)))
unfold!!! SC@(var x , con-var x₁) σ = σ SC

----------------------------------------------------------------------
-- equivalence requires multiple unfolding

variable
  T₁ T₂ : TCType n
  S₁ S₂ : SCType n i

data EquivT (R : SCType n zero → SCType n zero → Set) : TCType n → TCType n → Set where
  eq-int : EquivT R (TInt , con-int) (TInt , con-int)
  eq-chn : R S₁ S₂ →
    EquivT R (TChn (proj₁ S₁) , con-chn (proj₂ S₁))
             (TChn (proj₁ S₂) , con-chn (proj₂ S₂))

data EquivS (R : SCType n zero → SCType n zero → Set) :
     (S₁ S₂ : SCType n zero) → Set where
  eq-end :
    EquivS R (end , con-end) (end , con-end)
  eq-xmt : (d : Dir) →
    EquivT R T₁ T₂ →
    R S₁ S₂ →
    EquivS R (xmt d (proj₁ T₁) (proj₁ S₁) , con-xmt (proj₂ T₁) (proj₂ S₁))
             (xmt d (proj₁ T₂) (proj₁ S₂) , con-xmt (proj₂ T₂) (proj₂ S₂))
  eq-rec-l : 
    let S = proj₁ S₁ in
    let cs = proj₂ S₁ in
    EquivS R (subst-maxS (rec S) S , subst-contr-mS (c-weakenS₁ cs) (con-rec cs)) S₂ →
    EquivS R (rec S , con-rec cs) S₂
  eq-rec-r : 
    let S = proj₁ S₂ in
    let cs = proj₂ S₂ in
    EquivS R S₁ (subst-maxS (rec S) S , subst-contr-mS (c-weakenS₁ cs) (con-rec cs)) →
    EquivS R S₁ (rec S , con-rec cs)

record Equiv (S₁ S₂ : SCType 0 zero) : Set where
  coinductive
  field force : EquivS Equiv (unfold!! S₁ id) (unfold!! S₂ id)

record Equiv' (S₁ S₂ : SCType n zero) : Set where
  coinductive
  field force : EquivS Equiv' (unfold!!!{n = 0} S₁ id) (unfold!!!{n = 0} S₂ id)

{-# TERMINATING #-}
equivt-refl : ∀ T → EquivT Equiv T T
equivs-refl : ∀ S → EquivS Equiv S S
equiv-refl : ∀ S → Equiv S S

equivt-refl (TInt , con-int) = eq-int
equivt-refl (TChn S , con-chn x) = eq-chn (equiv-refl (S , x))

equivs-refl (xmt d t s , con-xmt ct cs) = eq-xmt d (equivt-refl (t , ct)) (equiv-refl (s , cs))
equivs-refl (end , con-end) = eq-end
equivs-refl (rec s , con-rec cs) = eq-rec-l (eq-rec-r (equivs-refl ((subst-maxS (rec s) s) , (subst-contr-mS (c-weakenS₁ cs) (con-rec cs)))))

Equiv.force (equiv-refl S) = equivs-refl (unfold!! S id)


----------------------------------------------------------------------
-- prove equivalence of one-level unrolling
-- μX S ≈ S [μX S / X] 

module μ-unrolling where

  unfold-≡ : ∀ S cs →
    unfold!! (S , cs) (λ { (S' , c') → (subst-maxS (rec S) S') , (subst-contr-mS (c-weakenS₁ c') (con-rec cs)) })
    ≡
      (unfold!!
       (subst-maxS (rec S) S ,
        subst-contr-mS (c-weakenS₁ cs) (con-rec cs))
       id)

  unfold-≡ (xmt d T S) (con-xmt x cs) = refl
  unfold-≡ end con-end = refl
  unfold-≡ (rec S) (con-rec cs) = {!!}
  unfold-≡ (var x) (con-var x₁)
    with max? x
  unfold-≡ (var x) (con-var x₁) | yes p = {!!}
  unfold-≡ (var x) (con-var x₁) | no ¬p = refl


  unroll : SCType n i → SCType n i
  unroll SC@(xmt d T S , con-xmt x cs) = SC
  unroll SC@(end , con-end) = SC
  unroll (rec S , cs@(con-rec cs')) = (subst-maxS (rec S) S) , (subst-contr-mS (c-weakenS₁ cs') cs)
  unroll SC@(var x , con-var x₁) = SC

  unroll-equiv : (SC : SCType 0 zero) → Equiv SC (unroll SC)
  Equiv.force (unroll-equiv SC@(xmt d T S , con-xmt x cs))
    with unroll SC
  ... | SC' = equivs-refl SC'
  Equiv.force (unroll-equiv (end , con-end)) = eq-end
  Equiv.force (unroll-equiv (rec S , con-rec cs))
    rewrite unfold-≡ S cs =
    let S₁ = unfold!! (S , cs) (λ { (S' , c') → (subst-maxS (rec S) S') , (subst-contr-mS (c-weakenS₁ c') (con-rec cs)) }) in
    let eqx = equivs-refl S₁ in
    {!S₁!}

----------------------------------------------------------------------
-- prove the folk theorem
-- μX μY S = μY [Y/X]S

module μ-examples where

  r1 : SType 0
  r1 = rec (rec (xmt SND (TChn (var zero)) (var (suc zero))))

  r2 : SType n
  r2 = rec (xmt SND (TChn (var zero)) (var zero))

  r2a : SType 0
  r2a = rec r2

  r2b : SType n
  r2b = rec (rec (xmt SND (TChn (var zero)) (var (suc zero))))

  r2-unfolded : SType 0
  r2-unfolded = xmt SND (TChn r2) r2

  r2-unf : SType 0
  r2-unf = rec (xmt SND (TChn (var zero)) r2b)

  rc2-unf : SCType 0 zero
  rc2-unf = r2-unf , (con-rec (con-xmt (con-chn (con-var z≤n)) (con-rec (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n))))))

  rc1 : SCType 0 zero
  rc1 = r1 , (con-rec (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n))))

  rc2 : SCType n zero
  rc2 = r2 , (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n)))

  rc2a : SCType 0 zero
  rc2a = r2a , con-rec (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n)))

  rc2b : SCType n zero
  rc2b = r2b , con-rec (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n)))

  rc2-unfolded : SCType 0 zero
  rc2-unfolded = r2-unfolded , (con-xmt (con-chn (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n)))) (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n))))

  rc2=rc2 : Equiv rc2 rc2
  Equiv.force rc2=rc2 = eq-xmt SND (eq-chn rc2=rc2) rc2=rc2

  rc2=rc2-unfolded : Equiv rc2 rc2-unfolded
  Equiv.force rc2=rc2-unfolded = eq-xmt SND (eq-chn rc2=rc2) rc2=rc2

  weak-r2 : SType 0
  weak-r2 = rec (weaken'S 1 zero r2)

  weak-rc2 : SCType 0 zero
  weak-rc2 = weak-r2 , (con-rec (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n))))

  r2-weak : SType n
  r2-weak = rec (xmt SND ((TChn (weaken'S 1 zero (rec (rec (xmt SND (TChn (var (suc zero))) (var (suc zero)))))))) ((weaken'S 1 zero (rec (rec (xmt SND (TChn (var (suc zero))) (var (suc zero))))))))

  rc2-weak : SCType 0 zero
  rc2-weak = r2-weak , con-rec (con-xmt (con-chn (con-rec (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n))))) (con-rec (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n)))))

  rc2=rc2a : Equiv rc2 rc2a
  Equiv.force rc2=rc2a = eq-xmt SND (eq-chn rc2=rc2a) rc2=rc2a

  rc2=xxxrc2b : Equiv' rc2 rc2-unf
  rc2=rc2b : Equiv' rc2 rc2b

  Equiv'.force rc2=xxxrc2b = eq-xmt SND (eq-chn rc2=xxxrc2b) rc2=rc2b
  Equiv'.force rc2=rc2b = eq-xmt SND (eq-chn rc2=rc2b) rc2=xxxrc2b

  rc2=rc2-weak : Equiv' rc2 rc2-weak
  Equiv'.force rc2=rc2-weak = eq-xmt SND (eq-chn {!rc2=rc2b!}) {!!}

  rc2=weak-rc2 : Equiv rc2 weak-rc2
  Equiv.force rc2=weak-rc2 = eq-xmt SND (eq-chn rc2=rc2a) rc2=rc2a

  r3 : SType 0
  r3 = rec (xmt SND (TChn (var zero)) (weaken'S 1 zero r1))

  rc3 : SCType 0 zero
  rc3 = r3 , con-rec (con-xmt (con-chn (con-var z≤n)) (con-rec (con-rec (con-xmt (con-chn (con-var z≤n)) (con-var z≤n)))))

  rc1=rc2 : Equiv rc1 rc2
  rc3=rc2 : Equiv rc3 rc2

  Equiv.force rc1=rc2 = eq-xmt SND (eq-chn rc1=rc2) rc3=rc2
  Equiv.force rc3=rc2 = eq-xmt SND (eq-chn rc3=rc2) rc1=rc2

-- end examples
----------------------------------------------------------------------

recrec : SType 2 → SType 0 × SType 0
recrec S = rec (rec S) , rec (subst-maxS (var zero) S)

recrec2 : SType 2 → SType 1
recrec2 S = rec S

conrr1 : {S : SType 2} → Contractive (suc (suc zero)) S → Contractive zero (rec (rec S))
conrr1 cs = con-rec (con-rec cs)

conrr2 : {S : SType 2} → Contractive (suc (suc zero)) S → Contractive (suc zero) (subst-maxS (var zero) S)
conrr2 cs = subst-contr-mS {!subst-contr-mS!} (con-var (s≤s z≤n))

sc-rec : SCType (suc n) (suc i) → SCType n i
sc-rec (S , cs) = (rec S , con-rec cs)

¬fromN≤x : (x : Fin n) → ¬ (fromℕ n ≤ inject₁ x)
¬fromN≤x {suc n} zero ()
¬fromN≤x {suc n} (suc x) (s≤s n≤x) = ¬fromN≤x x n≤x

μμ-lem-gen : {n : ℕ}
  → (S : SType (suc (suc n)))
  → Contractive (suc (suc (fromℕ n))) S
  → Contractive (suc (fromℕ n)) (subst-maxS (var (fromℕ n)) S)
μμ-lem-gen (xmt d T S) (con-xmt x cs) = con-xmt (subst-contr-mT x (con-var z≤n)) (subst-contr-mS cs (con-var z≤n))
μμ-lem-gen end con-end = con-end
μμ-lem-gen (rec S) (con-rec cs) = con-rec (μμ-lem-gen S cs)
μμ-lem-gen (var zero) (con-var ())
μμ-lem-gen (var (suc zero)) (con-var (s≤s ()))
μμ-lem-gen (var (suc (suc x))) (con-var (s≤s (s≤s x₁)))
  with ¬fromN≤x x x₁
μμ-lem-gen (var (suc (suc x))) (con-var (s≤s (s≤s x₁))) | ()

μμ-lemma : (S : SType 2) → Contractive (suc (suc zero)) S → Contractive (suc zero) (subst-maxS (var zero) S)
μμ-lemma S cs = μμ-lem-gen S cs

μμ-gen : (S : SType (suc (suc n))) (cs : Contractive (suc (suc (fromℕ n))) S) →
  Equiv' (sc-rec (sc-rec (S , {!!}))) 
         (sc-rec ((subst-maxS (var zero) S) , {!!}))
μμ-gen S cs = {!!}

μμ1 : (S : SType 2) (cs : Contractive (suc (suc zero)) S) →
  Equiv (sc-rec (sc-rec (S , cs)))
        (sc-rec ((subst-maxS (var zero) S) , μμ-lemma S cs))
Equiv.force (μμ1 (xmt d T S) (con-xmt x cs)) = {!!}
Equiv.force (μμ1 end con-end) = eq-end
Equiv.force (μμ1 (rec S) (con-rec cs)) = {!!}
Equiv.force (μμ1 (var x) (con-var x₁)) = {!!}


-- or μX μY S = μX [X/Y]S

μμ2 : (S : SType 2) (cs : Contractive (suc (suc zero)) S) →
  Equiv (sc-rec (sc-rec (S , cs)))
        let xxx = subst-maxS {!sc-rec!} (rec S) in (sc-rec ((subst-maxS (var zero) S) , (subst-contr-mS (c-weakenS₁ cs) (con-var {!!}))))
μμ2 S cs = {!!}
