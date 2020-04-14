module Types.IND where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Types.Direction
open import Auxiliary.Extensionality

open import Auxiliary.RewriteLemmas

private
  variable
    m n : ℕ

----------------------------------------------------------------------
-- session type inductively with explicit rec

data Polarity : Set where
  POS NEG : Polarity

mutual
  data Type n : Set where
    TUnit TInt : Type n
    TPair : (T₁ : Type n) (T₂ : Type n) → Type n
    TChan : (S : SType n) → Type n
  
  data SType n : Set where
    gdd : (G : GType n) → SType n
    rec : (G : GType (suc n) ) → SType n
    var : (p : Polarity) → (x : Fin n) → SType n

  data GType n : Set where
    transmit : (d : Dir) (T : Type n) (S : SType n) → GType n
    choice : (d : Dir) (m : ℕ) (alt : Fin m → SType n) → GType n
    end : GType n
  
TType = Type

-- weakening

weakenS : (n : ℕ) → SType m → SType (m + n)
weakenG : (n : ℕ) → GType m → GType (m + n)
weakenT : (n : ℕ) → TType m → TType (m + n)

weakenS n (gdd gst) = gdd (weakenG n gst)
weakenS n (rec gst) = rec (weakenG n gst)
weakenS n (var p x) = var p (inject+ n x)

weakenG n (transmit d t s) = transmit d (weakenT n t) (weakenS n s)
weakenG n (choice d m alt) = choice d m (weakenS n ∘ alt)
weakenG n end = end

weakenT n TUnit = TUnit
weakenT n TInt = TInt
weakenT n (TPair ty ty₁) = TPair (weakenT n ty) (weakenT n ty₁)
weakenT n (TChan x) = TChan (weakenS n x)

weaken1 : SType m → SType (suc m)
weaken1{m} stm with weakenS 1 stm
... | r rewrite n+1=suc-n {m} = r

module CheckWeaken where
  s0 : SType 0
  s0 = rec (transmit SND TUnit (var POS zero))
  s1 : SType 1
  s1 = rec (transmit SND TUnit (var POS zero))
  s2 : SType 2
  s2 = rec (transmit SND TUnit (var POS zero))

  check-weakenS1 : weakenS 1 s0 ≡ s1
  check-weakenS1 = cong rec (cong (transmit SND TUnit) refl)

  check-weakenS2 : weakenS 2 s0 ≡ s2
  check-weakenS2 = cong rec (cong (transmit SND TUnit) refl)

weaken1'N : Fin (suc n) → Fin n → Fin (suc n)
weaken1'N zero x = suc x
weaken1'N (suc i) zero = zero
weaken1'N (suc i) (suc x) = suc (weaken1'N i x)

weaken1'S : Fin (suc n) → SType n → SType (suc n)
weaken1'G : Fin (suc n) → GType n → GType (suc n)
weaken1'T : Fin (suc n) → TType n → TType (suc n)

weaken1'S i (gdd gst) = gdd (weaken1'G i gst)
weaken1'S i (rec gst) = rec (weaken1'G (suc i) gst)
weaken1'S i (var p x) = var p (weaken1'N i x)

weaken1'G i (transmit d t s) = transmit d (weaken1'T i t) (weaken1'S i s)
weaken1'G i (choice d m alt) = choice d m (weaken1'S i ∘ alt)
weaken1'G i end = end

weaken1'T i TUnit = TUnit
weaken1'T i TInt = TInt
weaken1'T i (TPair t₁ t₂) = TPair (weaken1'T i t₁) (weaken1'T i t₂)
weaken1'T i (TChan x) = TChan (weaken1'S i x)

weaken1S : SType n → SType (suc n)
weaken1G : GType n → GType (suc n)
weaken1T : Type n → Type (suc n)

weaken1S = weaken1'S zero
weaken1G = weaken1'G zero
weaken1T = weaken1'T zero

module CheckWeaken1' where
  sxy : ∀ n → Fin (suc n) → SType n
  sxy n x = rec (transmit SND TUnit (var POS x))

  s00 : SType 0
  s00 = sxy 0 zero
  s10 : SType 1
  s10 = sxy 1 zero
  s11 : SType 1
  s11 = sxy 1 (suc zero)
  s22 : SType 2
  s22 = sxy 2 (suc (suc zero))

  check-weaken-s01 : weaken1'S zero s00 ≡ s10
  check-weaken-s01 = refl

  check-weaken-s1-s2 : weaken1'S zero s11 ≡ s22
  check-weaken-s1-s2 = refl

  check-weaken-s21 : weaken1'S (suc zero) (sxy 2 (suc zero)) ≡ sxy 3 (suc zero)
  check-weaken-s21 = refl
--------------------------------------------------------------------

dual-pol : Polarity → Polarity
dual-pol POS = NEG
dual-pol NEG = POS

dual-pol-inv : ∀ p → dual-pol (dual-pol p) ≡ p
dual-pol-inv POS = refl
dual-pol-inv NEG = refl

swap-polS : (i : Fin (suc n)) → SType (suc n) → SType (suc n)
swap-polG : (i : Fin (suc n)) → GType (suc n) → GType (suc n)
swap-polT : (i : Fin (suc n)) → Type (suc n) → Type (suc n)

swap-polG i (transmit d t st) = transmit d (swap-polT i t) (swap-polS i st)
swap-polG i (choice d m alt) = choice d m (swap-polS i ∘ alt)
swap-polG i end = end

swap-polS i (gdd gst) = gdd (swap-polG i gst)
swap-polS i (rec st) = rec (swap-polG (suc i) st)
swap-polS zero (var p zero) = var (dual-pol p) zero
swap-polS (suc i) (var p zero) = var p zero
swap-polS zero (var p (suc x)) = var p (suc x)
swap-polS {suc n} (suc i) (var p (suc x)) = weaken1S (swap-polS i (var p x))

swap-polT i TUnit = TUnit
swap-polT i TInt = TInt
swap-polT i (TPair t₁ t₂) = TPair (swap-polT i t₁) (swap-polT i t₂)
swap-polT i (TChan x) = TChan (swap-polS i x)

--------------------------------------------------------------------

weak-weakN : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (x : Fin n)
  → weaken1'N (suc i) (weaken1'N j x) ≡ weaken1'N (inject₁ j) (weaken1'N i x)
weak-weakG : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (g : GType n)
  → weaken1'G (suc i) (weaken1'G j g) ≡ weaken1'G (inject₁ j) (weaken1'G i g)
weak-weakS : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (s : SType n)
  → weaken1'S (suc i) (weaken1'S j s) ≡ weaken1'S (inject₁ j) (weaken1'S i s)
weak-weakT : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (t : Type n)
  → weaken1'T (suc i) (weaken1'T j t) ≡ weaken1'T (inject₁ j) (weaken1'T i t)

weak-weakN zero zero le x                              = refl
weak-weakN (suc i) zero le x                         = refl
weak-weakN (suc i) (suc j) (s≤s le) zero           = refl
weak-weakN{suc n} (suc i) (suc j) (s≤s le) (suc x) = cong suc (weak-weakN i j le x) 

weak-weakG i j le (transmit d t s) = cong₂ (transmit d) (weak-weakT i j le t) (weak-weakS i j le s)
weak-weakG i j le (choice d m alt) = cong (choice d m) (ext (weak-weakS i j le ∘ alt))
weak-weakG i j le end              = refl

weak-weakS i j le (gdd gst) = cong gdd (weak-weakG i j le gst)
weak-weakS i j le (rec gst) = cong rec (weak-weakG (suc i) (suc j) (s≤s le) gst)
weak-weakS i j le (var p x) = cong (var p) (weak-weakN i j le x)

weak-weakT i j le TUnit        = refl
weak-weakT i j le TInt         = refl
weak-weakT i j le (TPair t t₁) = cong₂ TPair (weak-weakT i j le t) (weak-weakT i j le t₁)
weak-weakT i j le (TChan s)    = cong TChan (weak-weakS i j le s)


weaken1-weakenN : (m : ℕ) (j : Fin (suc n)) (x : Fin n)
  → inject+ m (weaken1'N j x) ≡ weaken1'N (inject+ m j) (inject+ m x)
weaken1-weakenN m zero zero           = refl
weaken1-weakenN m zero (suc x)      = refl
weaken1-weakenN m (suc j) zero      = refl
weaken1-weakenN m (suc j) (suc x) = cong suc (weaken1-weakenN m j x)

weaken1-weakenS : (m : ℕ) (j : Fin (suc n)) (s : SType n)
  → weakenS m (weaken1'S j s) ≡ weaken1'S (inject+ m j) (weakenS m s) 
weaken1-weakenG : (m : ℕ) (j : Fin (suc n)) (g : GType n)
  → weakenG m (weaken1'G j g) ≡ weaken1'G (inject+ m j) (weakenG m g)
weaken1-weakenT : (m : ℕ) (j : Fin (suc n)) (t : Type n)
  → weakenT m (weaken1'T j t) ≡ weaken1'T (inject+ m j) (weakenT m t)
weaken1-weakenS m j (gdd gst) = cong gdd (weaken1-weakenG m j gst)
weaken1-weakenS m j (rec gst) = cong rec (weaken1-weakenG m (suc j) gst)
weaken1-weakenS m zero (var p zero)      = refl
weaken1-weakenS m zero (var p (suc x)) = refl
weaken1-weakenS {suc n} m (suc j) (var p zero)      = refl
weaken1-weakenS {suc n} m (suc j) (var p (suc x)) = cong (var p) (cong suc (weaken1-weakenN m j x))

weaken1-weakenG m j (transmit d t s)  = cong₂ (transmit d) (weaken1-weakenT m j t) (weaken1-weakenS m j s)
weaken1-weakenG m j (choice d m₁ alt) = cong (choice d m₁) (ext (weaken1-weakenS m j ∘ alt))
weaken1-weakenG m j end = refl

weaken1-weakenT m j TUnit = refl
weaken1-weakenT m j TInt = refl
weaken1-weakenT m j (TPair t t₁) = cong₂ TPair (weaken1-weakenT m j t) (weaken1-weakenT m j t₁)
weaken1-weakenT m j (TChan x) = cong TChan (weaken1-weakenS m j x)

--------------------------------------------------------------------

-- weakening of later index
{-# TERMINATING #-}
swap-weaken1'G : (i : Fin (suc (suc n))) (j : Fin′ i) (gst : GType (suc n)) →
  swap-polG (inject j) (weaken1'G i gst) ≡ weaken1'G i (swap-polG (inject! j) gst)
swap-weaken1'S : (i : Fin (suc (suc n))) (j : Fin′ i) (sst : SType (suc n)) →
  swap-polS (inject j) (weaken1'S i sst) ≡ weaken1'S i (swap-polS (inject! j) sst)
swap-weaken1'T : (i : Fin (suc (suc n))) (j : Fin′ i) (t : Type (suc n)) →
  swap-polT (inject j) (weaken1'T i t) ≡ weaken1'T i (swap-polT (inject! j) t)

swap-weaken1'G i j (transmit d t s) = cong₂ (transmit d) (swap-weaken1'T i j t) (swap-weaken1'S i j s)
swap-weaken1'G i j (choice d m alt) = cong (choice d m) (ext (swap-weaken1'S i j ∘ alt))
swap-weaken1'G i j end = refl

swap-weaken1'S i j (gdd gst) = cong gdd (swap-weaken1'G i j gst)
swap-weaken1'S i j (rec gst) = cong rec (swap-weaken1'G (suc i) (suc j) gst)
swap-weaken1'S zero () (var p x)
swap-weaken1'S (suc i) zero (var p zero) = refl
swap-weaken1'S (suc i) zero (var p (suc x)) = refl
swap-weaken1'S (suc i) (suc j) (var p zero) = refl
swap-weaken1'S{suc n} (suc i) (suc j) (var p (suc x)) rewrite (weak-weakS i zero z≤n (swap-polS (inject! j) (var p x))) = 
  let sws = swap-weaken1'S{n} i j (var p x) in cong (weaken1'S zero) sws

swap-weaken1'T i j TUnit         = refl
swap-weaken1'T i j TInt          = refl
swap-weaken1'T i j (TPair t₁ t₂) = cong₂ TPair (swap-weaken1'T i j t₁) (swap-weaken1'T i j t₂)
swap-weaken1'T i j (TChan s)     = cong TChan (swap-weaken1'S i j s)

--------------------------------------------------------------------

-- weakening of earlier index
{-# TERMINATING #-}
swap-weaken1'S< : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) → (s : SType (suc n)) →
  swap-polS (suc i) (weaken1'S (inject₁ j) s) ≡ weaken1'S (inject₁ j) (swap-polS i s)
swap-weaken1'G< : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) → (g : GType (suc n)) →
  swap-polG (suc i) (weaken1'G (inject₁ j) g) ≡ weaken1'G (inject₁ j) (swap-polG i g)
swap-weaken1'T< : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) → (t : Type (suc n)) →
  swap-polT (suc i) (weaken1'T (inject₁ j) t) ≡ weaken1'T (inject₁ j) (swap-polT i t)

swap-weaken1'S< i j le (gdd gst)       = cong gdd (swap-weaken1'G< i j le gst)
swap-weaken1'S< i j le (rec gst)       = cong rec (swap-weaken1'G< (suc i) (suc j) (s≤s le) gst)
swap-weaken1'S< zero zero le (var p x)     = refl
swap-weaken1'S< (suc i) zero le (var p x) = refl
swap-weaken1'S<{suc n} (suc i) (suc j) le (var p zero) = refl
swap-weaken1'S<{suc n} (suc i) (suc j) (s≤s le) (var p (suc x)) rewrite (weak-weakS (inject₁ j) zero z≤n (swap-polS i (var p x))) =
  let sws = swap-weaken1'S<{n} i j le (var p x) in cong (weaken1'S zero) sws

swap-weaken1'G< i j le (transmit d t s) = cong₂ (transmit d) (swap-weaken1'T< i j le t) (swap-weaken1'S< i j le s)
swap-weaken1'G< i j le (choice d m alt) = cong (choice d m) (ext ((swap-weaken1'S< i j le) ∘ alt))
swap-weaken1'G< i j le end = refl

swap-weaken1'T< i j le TUnit = refl
swap-weaken1'T< i j le TInt = refl
swap-weaken1'T< i j le (TPair t t₁) = cong₂ (TPair) (swap-weaken1'T< i j le t) (swap-weaken1'T< i j le t₁)
swap-weaken1'T< i j le (TChan s) = cong (TChan) (swap-weaken1'S< i j le s)


swap-weakenS : (i : Fin (suc n)) → (s : SType (suc n)) →
  swap-polS (suc i) (weaken1S s) ≡ weaken1S (swap-polS i s)
swap-weakenG : (i : Fin (suc n)) → (g : GType (suc n)) →
  swap-polG (suc i) (weaken1G g) ≡ weaken1G (swap-polG i g)
swap-weakenT : (i : Fin (suc n)) → (t : Type (suc n)) →
  swap-polT (suc i) (weaken1T t) ≡ weaken1T (swap-polT i t)

swap-weakenS i s = swap-weaken1'S< i zero z≤n s
swap-weakenG i g = swap-weaken1'G< i zero z≤n g
swap-weakenT i t = swap-weaken1'T< i zero z≤n t

--------------------------------------------------------------------

-- swapping of general weakening
{-# TERMINATING #-}
swap-weakenG' : (m : ℕ) (j : Fin (suc n)) (gst : GType (suc n))
  → swap-polG (inject+ m j) (weakenG m gst) ≡ weakenG m (swap-polG j gst)
swap-weakenS' : (m : ℕ) (j : Fin (suc n)) (s : SType (suc n))
  → swap-polS (inject+ m j) (weakenS m s) ≡ weakenS m (swap-polS j s)
swap-weakenT' : (m : ℕ) (j : Fin (suc n)) (t : Type (suc n))
  → swap-polT (inject+ m j) (weakenT m t) ≡ weakenT m (swap-polT j t)

swap-weakenG' m j (transmit d t s) = cong₂ (transmit d) (swap-weakenT' m j t) (swap-weakenS' m j s)
swap-weakenG' m j (choice d m₁ alt) = cong (choice d m₁) (ext (swap-weakenS' m j ∘ alt))
swap-weakenG' m j end = refl

swap-weakenS' m j (gdd gst) = cong gdd (swap-weakenG' m j gst)
swap-weakenS' m j (rec gst) = cong rec (swap-weakenG' m (suc j) gst)
swap-weakenS' m zero (var p zero)      = refl
swap-weakenS' m (suc j) (var p zero) = refl
swap-weakenS' m zero (var p (suc zero))      = refl
swap-weakenS' m zero (var p (suc (suc x))) = refl
swap-weakenS' {suc n} m (suc j) (var p (suc x)) rewrite (weaken1-weakenS m zero (swap-polS j (var p x))) =
   let rst = swap-weakenS'{n} m j (var p x) in cong weaken1S rst

swap-weakenT' m j TUnit = refl
swap-weakenT' m j TInt = refl
swap-weakenT' m j (TPair t t₁) = cong₂ TPair (swap-weakenT' m j t) (swap-weakenT' m j t₁)
swap-weakenT' m j (TChan x) = cong TChan (swap-weakenS' m j x)

--------------------------------------------------------------------

{-# TERMINATING #-}
swap-pol-invS : (i : Fin (suc n)) → (st : SType (suc n)) →
  swap-polS i (swap-polS i st) ≡ st
swap-pol-invG : (i : Fin (suc n)) → (st : GType (suc n)) →
  swap-polG i (swap-polG i st) ≡ st
swap-pol-invT : (i : Fin (suc n)) → (ty : Type (suc n)) →
  swap-polT i (swap-polT i ty) ≡ ty

swap-pol-invS i (gdd gst) = cong gdd (swap-pol-invG i gst)
swap-pol-invS i (rec gst) = cong rec (swap-pol-invG (suc i) gst)
swap-pol-invS zero (var p zero) rewrite dual-pol-inv p = refl
swap-pol-invS (suc i) (var p zero) = refl
swap-pol-invS zero (var p (suc x)) rewrite dual-pol-inv p = refl
swap-pol-invS {suc n} (suc i) (var p (suc x))
  rewrite swap-weakenS i (swap-polS i (var p x)) | swap-pol-invS i (var p x) = refl

-- extensionality needed
swap-pol-invG i (transmit d t s) = cong₂ (transmit d) (swap-pol-invT i t) (swap-pol-invS i s)
swap-pol-invG i (choice d m alt) = cong (choice d m) (ext R)
  where R : ∀ x → swap-polS i (swap-polS i (alt x)) ≡ alt x
        R x rewrite swap-pol-invS i (alt x) = refl
swap-pol-invG i end = refl

swap-pol-invT i TUnit = refl
swap-pol-invT i TInt = refl
swap-pol-invT i (TPair ty ty₁) = cong₂ TPair (swap-pol-invT i ty) (swap-pol-invT i ty₁)
swap-pol-invT i (TChan x) = cong TChan (swap-pol-invS i x)

--------------------------------------------------------------------
-- LM duality
dualS : SType n → SType n
dualG : GType n → GType n

dualG (transmit d t st) = transmit (dual-dir d) t (dualS st)
dualG (choice d m alt) = choice (dual-dir d) m (dualS ∘ alt)
dualG end = end

dualS (gdd gst) = gdd (dualG gst)
dualS (rec gst) = rec (swap-polG zero (dualG gst))
dualS (var p x) = var (dual-pol p) x

--------------------------------------------------------------------

dual-weakenS : (i : Fin (suc n)) (s : SType n) → dualS (weaken1'S i s) ≡ weaken1'S i (dualS s)
dual-weakenG : (i : Fin (suc n)) (g : GType n) → dualG (weaken1'G i g) ≡ weaken1'G i (dualG g)

dual-weakenS i (gdd gst) = cong gdd (dual-weakenG i gst)
dual-weakenS i (rec gst) rewrite (sym (swap-weaken1'G (suc i) zero (dualG gst))) = cong rec (cong (swap-polG zero) (dual-weakenG (suc i) gst))
dual-weakenS i (var p x) = refl

dual-weakenG i (transmit d t s) = cong₂ (transmit (dual-dir d)) refl (dual-weakenS i s)
dual-weakenG i (choice d m alt) = cong (choice (dual-dir d) m) (ext (dual-weakenS i ∘ alt))
dual-weakenG i end = refl

dual-weakenS' : (m : ℕ) (s : SType n) → dualS (weakenS m s) ≡ weakenS m (dualS s)
dual-weakenG' : (m : ℕ) (g : GType n) → dualG (weakenG m g) ≡ weakenG m (dualG g)

dual-weakenS' n (gdd gst) = cong gdd (dual-weakenG' n gst)
dual-weakenS' n (rec gst) rewrite (sym (swap-weakenG' n zero (dualG gst))) = cong rec (cong (swap-polG zero) (dual-weakenG' n gst))
dual-weakenS' n (var p x) = refl

dual-weakenG' n (transmit d t s) = cong₂ (transmit (dual-dir d)) refl (dual-weakenS' n s)
dual-weakenG' n (choice d m alt) = cong (choice (dual-dir d) m) (ext (dual-weakenS' n ∘ alt))
dual-weakenG' n end = refl 

--------------------------------------------------------------------

aux : (i : Fin n) (x : Fin n) (p' : Polarity) →
  var p' (suc (suc x)) ≡ weaken1S (var p' (suc x))
aux i x p = refl

var-suc : (i : Fin n) (x : Fin n) (p : Polarity) → 
  ∃ λ p' → swap-polS (suc i) (var p (suc x)) ≡ var p' (suc x)
var-suc zero zero p = dual-pol p , refl
var-suc (suc i) zero p = p , refl
var-suc zero (suc x) p = p , refl
var-suc (suc i) (suc x) p 
  with var-suc i x p
... | p' , snd 
  rewrite sym (aux i x p') = p' , cong weaken1S snd

--------------------------------------------------------------------

{-# TERMINATING #-}
swap-swapG : (gst : GType (suc n)) → (i : Fin (suc n)) (j : Fin′ i) → 
  swap-polG i (swap-polG (inject j) gst) ≡ swap-polG (inject j) (swap-polG i gst)
swap-swapT : (t : Type (suc n)) → (i : Fin (suc n)) (j : Fin′ i) →
  swap-polT i (swap-polT (inject j) t) ≡ swap-polT (inject j) (swap-polT i t)
swap-swapS : (st : SType (suc n)) → (i : Fin (suc n)) (j : Fin′ i) →
  swap-polS i (swap-polS (inject j) st) ≡ swap-polS (inject j) (swap-polS i st)

swap-swapG (transmit d t s) i j = cong₂ (transmit d) (swap-swapT t i j) (swap-swapS s i j)
swap-swapG (choice d m alt) i j = cong (choice d m) (ext (λ x → swap-swapS (alt x) i j))
swap-swapG end i j = refl

swap-swapT TUnit i j = refl
swap-swapT TInt i j = refl
swap-swapT (TPair t t₁) i j = cong₂ TPair (swap-swapT t i j) (swap-swapT t₁ i j)
swap-swapT (TChan x) i j = cong TChan (swap-swapS x i j)

swap-swapS (gdd gst) i j = cong gdd (swap-swapG gst i j)
swap-swapS (rec gst) i j = cong rec (swap-swapG gst (suc i) (suc j))
swap-swapS (var p zero) zero ()
swap-swapS (var p zero) (suc i) zero = refl
swap-swapS (var p zero) (suc i) (suc j) = refl
swap-swapS (var p (suc x)) zero ()
swap-swapS (var p (suc x)) (suc i) zero
  with var-suc i x p
... | p' , snd rewrite snd = refl
swap-swapS {suc n} (var p (suc x)) (suc i) (suc j) 
  rewrite swap-weakenS i (swap-polS (inject j) (var p x))
  with swap-swapS (var p x) i j
... | pxij rewrite swap-weakenS (inject j) (swap-polS i (var p x))
  = cong weaken1S pxij

{-# TERMINATING #-}
swap-pol-dualG : (i : Fin (suc n)) (gst : GType (suc n)) → 
  swap-polG i (dualG gst) ≡ dualG (swap-polG i gst)
swap-pol-dualS : (i : Fin (suc n)) (st : SType (suc n)) →
  swap-polS i (dualS st) ≡ dualS (swap-polS i st)

swap-pol-dualG i (transmit d t s) = cong (transmit _ (swap-polT i t)) (swap-pol-dualS i s)
swap-pol-dualG i (choice d m alt) = cong (choice _ _) (ext (swap-pol-dualS i ∘ alt))
swap-pol-dualG i end = refl

swap-pol-dualS i (gdd gst) = cong gdd (swap-pol-dualG i gst)
swap-pol-dualS i (rec gst) rewrite sym (swap-pol-dualG (suc i) gst) = 
  cong rec (swap-swapG (dualG gst) (suc i) zero)
swap-pol-dualS zero (var p zero) = refl
swap-pol-dualS (suc i) (var p zero) = refl
swap-pol-dualS zero (var p (suc x)) = refl
swap-pol-dualS {suc n} (suc i) (var p (suc x))
   rewrite (dual-weakenS zero (swap-polS i (var p x))) =  cong weaken1S (swap-pol-dualS i (var p x)) 

--------------------------------------------------------------------

dual-invS : (st : SType n) → st ≡ dualS (dualS st)
dual-invG : (gst : GType n) → gst ≡ dualG (dualG gst)

dual-invS (gdd gst) = cong gdd (dual-invG gst)
dual-invS (rec gst) rewrite sym (swap-pol-dualG zero (dualG gst)) | swap-pol-invG zero (dualG (dualG gst)) = cong rec (dual-invG gst)
dual-invS (var p x) rewrite dual-pol-inv p = refl

dual-invG (transmit d t s) rewrite dual-dir-inv d = cong₂ (transmit d) refl (dual-invS s)
dual-invG (choice d m alt) rewrite dual-dir-inv d = cong (choice d m) (ext R)
  where R : (x : Fin m) → alt x ≡ dualS (dualS (alt x))
        R x rewrite sym (dual-invS (alt x)) = refl
dual-invG end = refl

dual-if : Polarity → SType n → SType n
dual-if POS s = s
dual-if NEG s = dualS s

dual-if-dual : (p : Polarity) (ist : SType 0) → dual-if p ist ≡ dual-if (dual-pol p) (dualS ist)
dual-if-dual POS ist = (dual-invS ist)
dual-if-dual NEG ist = refl 

--------------------------------------------------------------------
-- substitution

st-substS : SType (suc n) → Fin (suc n) → SType 0 → SType n
st-substG : GType (suc n) → Fin (suc n) → SType 0 → GType n
st-substT : Type (suc n) → Fin (suc n) → SType 0 → Type n

st-substS (gdd gst) i st0 = gdd (st-substG gst i st0)
st-substS (rec gst) i st0 = rec (st-substG gst (suc i) st0)
st-substS {n} (var p zero) zero st0 = weakenS n (dual-if p st0)
st-substS {suc n} (var p zero) (suc i) st0 = var p zero
st-substS {suc n} (var p (suc x)) zero st0 = var p x
st-substS {suc n} (var p (suc x)) (suc i) st0 = weaken1S (st-substS (var p x) i st0)

st-substG (transmit d t s) i st0 = transmit d (st-substT t i st0) (st-substS s i st0)
st-substG (choice d m alt) i st0 = choice d m (λ j → st-substS (alt j) i st0)
st-substG end i st0 = end

st-substT TUnit i st0 = TUnit
st-substT TInt i st0 = TInt
st-substT (TPair ty ty₁) i st0 = TPair (st-substT ty i st0) (st-substT ty₁ i st0)
st-substT (TChan st) i st0 = TChan (st-substS st i st0)

--------------------------------------------------------------------

trivial-subst-var : (p : Polarity) (x : Fin n) (ist₁ ist₂ : SType 0)
  → st-substS (var p (suc x)) zero ist₁ ≡ st-substS (var p (suc x)) zero ist₂
trivial-subst-var p zero ist1 ist2 = refl
trivial-subst-var p (suc x) ist1 ist2 = refl

trivial-subst-var' : (p : Polarity) (i : Fin n) (ist₁ ist₂ : SType 0)
  → st-substS (var p zero) (suc i) ist₁ ≡ st-substS (var p zero) (suc i) ist₂
trivial-subst-var' p zero ist1 ist2 = refl
trivial-subst-var' p (suc x) ist1 ist2 = refl

--------------------------------------------------------------------
-- equivalence
variable
  t t₁ t₂ t₁' t₂' : Type n
  s s₁ s₂ : SType n
  g g₁ g₂ : GType n

unfold : SType 0 → GType 0
unfold (gdd gst) = gst
unfold (rec gst) = st-substG gst zero (rec gst)

-- type equivalence
data EquivT (R : SType n → SType n → Set) : Type n → Type n → Set where
  eq-unit : EquivT R TUnit TUnit
  eq-int  : EquivT R TInt TInt
  eq-pair : EquivT R t₁ t₁' → EquivT R t₂ t₂' → EquivT R (TPair t₁ t₂) (TPair t₁' t₂')
  eq-chan : R s₁ s₂ → EquivT R (TChan s₁) (TChan s₂)

-- session type equivalence
data EquivG (R : SType n → SType n → Set) : GType n → GType n → Set where
  eq-transmit : (d : Dir) → EquivT R t₁ t₂ → R s₁ s₂ → EquivG R (transmit d t₁ s₁) (transmit d t₂ s₂)
  eq-choice : ∀ {alt alt'} → (d : Dir) → ((i : Fin m) → R (alt i) (alt' i)) → EquivG R (choice d m alt) (choice d m alt')
  eq-end : EquivG R end end

record Equiv (s₁ s₂ : SType 0) : Set where
  coinductive
  field force : EquivG Equiv (unfold s₁) (unfold s₂)

open Equiv

_≈_ = Equiv
_≈'_ = EquivG Equiv
_≈ᵗ_ = EquivT Equiv

-- reflexive

≈-refl : s ≈ s
≈'-refl : g ≈' g
≈ᵗ-refl : t ≈ᵗ t

force (≈-refl {s}) = ≈'-refl

≈'-refl {transmit d t s} = eq-transmit d ≈ᵗ-refl ≈-refl
≈'-refl {choice d m alt} = eq-choice d (λ i → ≈-refl)
≈'-refl {end} = eq-end

≈ᵗ-refl {TUnit} = eq-unit
≈ᵗ-refl {TInt} = eq-int
≈ᵗ-refl {TPair t t₁} = eq-pair ≈ᵗ-refl ≈ᵗ-refl
≈ᵗ-refl {TChan x} = eq-chan ≈-refl

-- symmetric

≈-symm : s₁ ≈ s₂ → s₂ ≈ s₁
≈'-symm : g₁ ≈' g₂ → g₂ ≈' g₁
≈ᵗ-symm : t₁ ≈ᵗ t₂ → t₂ ≈ᵗ t₁

force (≈-symm s₁≈s₂) = ≈'-symm (force s₁≈s₂)

≈'-symm (eq-transmit d x x₁) = eq-transmit d (≈ᵗ-symm x) (≈-symm x₁)
≈'-symm (eq-choice d x) = eq-choice d (≈-symm ∘ x)
≈'-symm eq-end = eq-end

≈ᵗ-symm eq-unit = eq-unit
≈ᵗ-symm eq-int = eq-int
≈ᵗ-symm (eq-pair t₁≈ᵗt₂ t₁≈ᵗt₃) = eq-pair (≈ᵗ-symm t₁≈ᵗt₂) (≈ᵗ-symm t₁≈ᵗt₃)
≈ᵗ-symm (eq-chan x) = eq-chan (≈-symm x)

