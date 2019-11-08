{-# OPTIONS --rewriting #-}
module Duality where

open import Data.Bool

open import Data.Nat hiding (compare)
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Agda.Builtin.Equality.Rewrite

-- variables

variable
  n m : ℕ

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
-- extensionality

postulate
  ext : {A : Set}{B : A → Set}{f : (x : A) → B x} {g : (x : A) → B x} →
    (∀ x → f x ≡ g x) → f ≡ g

----------------------------------------------------------------------
-- direction

data Dir : Set where
  SND RCV : Dir

-- dual
dual-dir : Dir → Dir
dual-dir SND = RCV
dual-dir RCV = SND

dual-dir-inv : (d : Dir) → dual-dir (dual-dir d) ≡ d
dual-dir-inv SND = refl
dual-dir-inv RCV = refl

----------------------------------------------------------------------
-- session types coinductively

module COI where

  mutual
    data Type : Set where
      TUnit TInt : Type
      TPair : Type → Type → Type
      TChan : SType → Type
    
    data STypeF (S : Set) : Set where
      transmit : (d : Dir) (t : Type) (s : S) → STypeF S
      choice : (d : Dir) (m : ℕ) (alt : Fin m → S) → STypeF S
      end : STypeF S

    record SType : Set where
      coinductive 
      constructor delay
      field force : STypeF SType

  open SType

  variable
    t t₁ t₂ t₁' t₂' : Type
    s s₁ s₂ : SType
    s' : STypeF SType

  -- type equivalence
  data EquivT (R : SType → SType → Set) : Type → Type → Set where
    eq-unit : EquivT R TUnit TUnit
    eq-int  : EquivT R TInt TInt
    eq-pair : EquivT R t₁ t₁' → EquivT R t₂ t₂' → EquivT R (TPair t₁ t₂) (TPair t₁' t₂')
    eq-chan : R s₁ s₂ → EquivT R (TChan s₁) (TChan s₂)

  -- session type equivalence
  data EquivF (R : SType → SType → Set) : STypeF SType → STypeF SType → Set where
    eq-transmit : (d : Dir) → EquivT R t₁ t₂ → R s₁ s₂ → EquivF R (transmit d t₁ s₁) (transmit d t₂ s₂)
    eq-choice : ∀ {alt alt'} → (d : Dir) → ((i : Fin m) → R (alt i) (alt' i)) → EquivF R (choice d m alt) (choice d m alt')
    eq-end : EquivF R end end

  record Equiv (s₁ : SType) (s₂ : SType) : Set where
    coinductive
    field force : EquivF Equiv (force s₁) (force s₂)

  open Equiv

  _≈_ = Equiv
  _≈'_ = EquivF Equiv
  _≈ᵗ_ = EquivT Equiv

  ≈ᵗ-refl : t ≈ᵗ t
  ≈-refl : s ≈ s
  ≈'-refl : s' ≈' s'

  force (≈-refl {s}) = ≈'-refl

  ≈'-refl {transmit d t s} = eq-transmit d ≈ᵗ-refl ≈-refl
  ≈'-refl {choice d m alt} = eq-choice d λ i → ≈-refl
  ≈'-refl {end} = eq-end

  ≈ᵗ-refl {TUnit} = eq-unit
  ≈ᵗ-refl {TInt} = eq-int
  ≈ᵗ-refl {TPair t t₁} = eq-pair ≈ᵗ-refl ≈ᵗ-refl
  ≈ᵗ-refl {TChan x} = eq-chan ≈-refl

  ----------------------------------------------------------------------
  -- duality
  dual : SType → SType
  dualF : STypeF SType → STypeF SType

  force (dual s) = dualF (force s)

  dualF (transmit d t s) = transmit (dual-dir d) t (dual s)
  dualF (choice d m alt) = choice (dual-dir d) m (dual ∘ alt)
  dualF end = end

  -- properties

  dual-involution : ∀ s → s ≈ dual (dual s)
  dual-involutionF : ∀ s' → s' ≈' dualF (dualF s')

  force (dual-involution s) = dual-involutionF (force s)

  dual-involutionF (transmit d t s)
    rewrite dual-dir-inv d = eq-transmit d ≈ᵗ-refl (dual-involution s)
  dual-involutionF (choice d m alt)
    rewrite dual-dir-inv d = eq-choice d (dual-involution ∘ alt)
  dual-involutionF end = eq-end

-- coinductive examples ----------------------------------------

module COIExample where
  open COI

  s1 : SType
  s2 : SType
  SType.force s1 = transmit SND TInt s2
  SType.force s2 = transmit SND (TChan s1) s1

  sd1 : SType
  sd2 : SType
  SType.force sd1 = transmit RCV TInt sd2
  SType.force sd2 = transmit RCV (TChan s1) sd1

  s1-dual-sd1 : dual s1 ≈ sd1
  s2-dual-sd2 : dual s2 ≈ sd2
  Equiv.force s1-dual-sd1 = eq-transmit RCV eq-int s2-dual-sd2
  Equiv.force s2-dual-sd2 = eq-transmit RCV ≈ᵗ-refl s1-dual-sd1

  -- minimal example: S0 = !S0.S0
  s0 : SType
  SType.force s0 = transmit SND (TChan s0) s0

  sd0 : SType
  SType.force sd0 = transmit RCV (TChan s0) sd0

  s0-dual-sd0 : dual s0 ≈ sd0
  Equiv.force s0-dual-sd0 = eq-transmit RCV ≈ᵗ-refl s0-dual-sd0

----------------------------------------------------------------------
-- session type inductively with explicit rec

module IND where

  data Polarity : Set where
    POS NEG : Polarity

  mutual
    data Type (n : ℕ) : Set where
      TUnit TInt : Type n
      TPair : Type n → Type n → Type n
      TChan : SType n → Type n
    
    data SType (n : ℕ) : Set where
      gdd : (gst : GType n) → SType n
      rec : (gst : GType (suc n) ) → SType n
      var : (p : Polarity) → (x : Fin n) → SType n

    data GType (n : ℕ) : Set where
      transmit : (d : Dir) (t : Type n) (s : SType n) → GType n
      choice : (d : Dir) (m : ℕ) (alt : Fin m → SType n) → GType n
      end : GType n
    
  TType = Type

  weakenS : (n : ℕ) → SType m → SType (m + n)
  weakenG : (n : ℕ) → GType m → GType (m + n)
  weakenT : (n : ℕ) → Type m → Type (m + n)
  
  weakenS n (gdd gst) = gdd (weakenG n gst)
  weakenS n (rec gst) = rec (weakenG n gst)
  weakenS n (var p x) = var p (inject+ n x)

  weakenG n (transmit d t s) = transmit d (weakenT n t) (weakenS n s)
  weakenG n (choice d m alt) = choice d m (λ i → weakenS n (alt i))
  weakenG n end = end

  weakenT n TUnit = TUnit
  weakenT n TInt = TInt
  weakenT n (TPair ty ty₁) = TPair (weakenT n ty) (weakenT n ty₁)
  weakenT n (TChan x) = TChan (weakenS n x)

  weaken1 : SType m → SType (suc m)
  weaken1{m} stm with weakenS 1 stm
  ... | r rewrite n+1=suc-n {m} = r

  weaken1'N : Fin (suc n) → Fin n → Fin (suc n)
  weaken1'N zero x = suc x
  weaken1'N (suc i) zero = zero
  weaken1'N (suc i) (suc x) = suc (weaken1'N i x)

  weaken1'S : Fin (suc n) → SType n → SType (suc n)
  weaken1'G : Fin (suc n) → GType n → GType (suc n)
  weaken1'T : Fin (suc n) → Type n → Type (suc n)

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

----------------------------------------------------------------------
  module sanity-check-weaken1 where
    w1S : SType n → SType (suc n)
    w1S s = weaken1'S zero s

    s0 : SType 0
    s0 = rec (transmit SND TUnit (var POS zero))

    s1 : SType 1
    s1 = rec (transmit SND TUnit (var POS zero))

    s1=weaken1-s0 : s1 ≡ w1S s0
    s1=weaken1-s0 = cong rec (cong (transmit SND TUnit) refl)

    s2 : SType 1
    s2 = rec (transmit SND (TChan (var POS (suc zero))) (var POS zero))

    s3 : SType 2
    s3 = rec (transmit SND (TChan (var POS (suc (suc zero)))) (var POS zero))

    s3=weaken1-s2 : s3 ≡ w1S s2
    s3=weaken1-s2 = cong rec (cong₂ (transmit SND) refl refl)

----------------------------------------------------------------------

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

----------------------------------------------------------------------

  swap-weakenS : (i : Fin (suc n)) → (s : SType (suc n)) →
    swap-polS (suc i) (weaken1S s) ≡ weaken1S (swap-polS i s)
  swap-weakenG : (i : Fin (suc n)) → (g : GType (suc n)) →
    swap-polG (suc i) (weaken1G g) ≡ weaken1G (swap-polG i g)
  swap-weakenT : (i : Fin (suc n)) → (t : Type (suc n)) →
    swap-polT (suc i) (weaken1T t) ≡ weaken1T (swap-polT i t)

  swap-weakenS i (gdd gst) = cong gdd (swap-weakenG i gst)
  swap-weakenS i (rec gst) = cong rec {!!}
  swap-weakenS zero (var p zero) = refl
  swap-weakenS (suc i) (var p zero) = refl
  swap-weakenS zero (var p (suc x)) = refl
  swap-weakenS (suc i) (var p (suc x)) = refl

  swap-weakenG i (transmit d t s) = cong₂ (transmit d) (swap-weakenT i t) (swap-weakenS i s)
  swap-weakenG i (choice d m alt) = cong (choice d m) (ext (λ x → swap-weakenS i (alt x)))
  swap-weakenG i end = refl

  swap-weakenT i TUnit = refl
  swap-weakenT i TInt = refl
  swap-weakenT i (TPair t₁ t₂) = cong₂ TPair (swap-weakenT i t₁) (swap-weakenT i t₂)
  swap-weakenT i (TChan x) = cong TChan (swap-weakenS i x)

----------------------------------------------------------------------

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

  dualS : SType n → SType n
  dualG : GType n → GType n

  dualG (transmit d t st) = transmit (dual-dir d) t (dualS st)
  dualG (choice d m alt) = choice (dual-dir d) m (dualS ∘ alt)
  dualG end = end

  dualS (gdd gst) = gdd (dualG gst)
  dualS (rec gst) = rec (swap-polG zero (dualG gst))
  dualS (var p x) = var (dual-pol p) x

----------------------------------------------------------------------

  dual-weakenS : (i : Fin n) (s : SType n) → dualS (weaken1'S (suc i) s) ≡ weaken1'S (suc i) (dualS s)
  dual-weakenG : (i : Fin n) (g : GType n) → dualG (weaken1'G (suc i) g) ≡ weaken1'G (suc i) (dualG g)

  dual-weakenS i (gdd gst) = cong gdd (dual-weakenG i gst)
  dual-weakenS i (rec gst) = cong rec {!!}
  dual-weakenS i (var p x) = refl

  dual-weakenG i (transmit d t s) = cong₂ (transmit (dual-dir d)) refl (dual-weakenS i s)
  dual-weakenG i (choice d m alt) = cong (choice (dual-dir d) m) (ext (dual-weakenS i ∘ alt))
  dual-weakenG i end = refl

----------------------------------------------------------------------
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
----------------------------------------------------------------------

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
    with var-suc i x (dual-pol p)
  ... | p' , snd rewrite snd = {!!}
  swap-swapS {suc n} (var p (suc x)) (suc i) (suc j) 
    rewrite swap-weakenS i (swap-polS (inject j) (var p x))
    with swap-swapS (var p x) i j
  ... | pxij rewrite swap-weakenS (inject j) (swap-polS i (var p x))
    = cong weaken1S pxij

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
    rewrite dual-weakenS i (swap-polS i (var p x)) = {!!} -- cong weaken1S (swap-pol-dualS i (var p x))

----------------------------------------------------------------------

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

----------------------------------------------------------------------

  trivial-weakenS : ∀ {m} → (ist : SType m) → weakenS 0 ist ≡ ist
  trivial-weakenG : ∀ {m} → (ist : GType m) → weakenG 0 ist ≡ ist
  trivial-weakenT : ∀ {m} → (ty : Type m) → weakenT 0 ty ≡ ty

  trivial-weakenS (gdd gst) = cong gdd (trivial-weakenG gst)
  trivial-weakenS (rec gst) = cong rec (trivial-weakenG gst)
  trivial-weakenS (var p x) = refl

  trivial-weakenG (transmit d t s) = cong₂ (transmit d) (trivial-weakenT t) (trivial-weakenS s)
  trivial-weakenG (choice d m alt) = cong (choice d m) (ext (trivial-weakenS ∘ alt))
  trivial-weakenG end = refl

  trivial-weakenT TUnit = refl
  trivial-weakenT TInt = refl
  trivial-weakenT (TPair ty ty₁) = cong₂ TPair (trivial-weakenT ty) (trivial-weakenT ty₁)
  trivial-weakenT (TChan x) = cong TChan (trivial-weakenS x)

----------------------------------------------------------------------
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

----------------------------------------------------------------------

module INDExample where
  open IND

  s1 : SType 0
  s2 : SType 1
  s1 = rec (transmit SND TInt s2)
  s2 = gdd (transmit SND (TChan (var POS zero)) (var POS zero))

  sd1 sd1' : SType 0
  sd2 sd2' : SType 1
  sd1 = rec (transmit RCV TInt sd2)
  sd2 = gdd (transmit RCV (TChan (var NEG zero)) (var POS zero))
  sd1' = rec (transmit RCV TInt sd2)
  sd2' = gdd (transmit RCV (TChan (weaken1 s1)) (var POS zero))

  sd1=dual-s1 : sd1 ≡ dualS s1
  sd1=dual-s1 = cong rec (cong (transmit RCV TInt) (cong gdd (cong₂ (transmit RCV) refl refl)))

  -- minimal example

  s0 : SType 0
  s0 = rec (transmit SND (TChan (var POS zero)) (var POS zero))

  sd0 sd0' : SType 0
  sd0 = rec (transmit RCV (TChan (var NEG zero)) (var POS zero))
  sd0' = rec (transmit RCV (TChan (weaken1 s0)) (var POS zero))

  sd0=dual-s0 : sd0 ≡ dualS s0
  sd0=dual-s0 = refl

----------------------------------------------------------------------
-- provide an embedding of IND to COI

open COI
open IND

ind2coiT : IND.Type 0 → COI.Type
ind2coiS : IND.SType 0 → COI.SType
ind2coiG : IND.GType 0 → COI.STypeF COI.SType

ind2coiT TUnit = TUnit
ind2coiT TInt = TInt
ind2coiT (TPair it it₁) = TPair (ind2coiT it) (ind2coiT it₁)
ind2coiT (TChan st) = TChan (ind2coiS st)

ind2coiG (transmit d t ist) = transmit d (ind2coiT t) (ind2coiS ist)
ind2coiG (choice d m alt) = choice d m (ind2coiS ∘ alt)
ind2coiG end = end

SType.force (ind2coiS (gdd gst)) = ind2coiG gst
SType.force (ind2coiS (rec gst)) = ind2coiG (st-substG gst zero (rec gst))

module Experimental where
  subst-weakenS : (s : IND.SType (suc n)) (i : Fin (suc n)) (s0 : IND.SType 0)
    → st-substS (weaken1S s) (suc i) s0 ≡ weaken1S (st-substS s i s0)
  subst-weakenS s i s0 = {!!}

  subst-swap-dualT : ∀ {ist} → (t : IND.Type (suc n)) (i : Fin (suc n)) →
    st-substT t i ist ≡ st-substT (swap-polT i t) i (IND.dualS ist)
  subst-swap-dualS : ∀ {ist} → (st : IND.SType (suc n)) (i : Fin (suc n)) →
    st-substS st i ist ≡ st-substS (swap-polS i st) i (IND.dualS ist)
  subst-swap-dualG : ∀ {ist} → (gst : IND.GType (suc n)) (i : Fin (suc n)) → 
    st-substG gst i ist ≡ st-substG (swap-polG i gst) i (IND.dualS ist)

  subst-swap-dualT TUnit i = refl
  subst-swap-dualT TInt i = refl
  subst-swap-dualT (TPair ty ty₁) i = cong₂ TPair (subst-swap-dualT ty i) (subst-swap-dualT ty₁ i)
  subst-swap-dualT (TChan x) i = cong TChan (subst-swap-dualS x i)

  subst-swap-dualS (gdd gst) i = cong gdd (subst-swap-dualG gst i)
  subst-swap-dualS (rec gst) i = cong rec (subst-swap-dualG gst (suc i))
  subst-swap-dualS (var p zero) zero = {!!}
  subst-swap-dualS {suc n} (var p zero) (suc i) = refl
  subst-swap-dualS {suc n} (var p (suc x)) zero = {!!}
  subst-swap-dualS {suc n}{ist} (var p (suc x)) (suc i)
    rewrite subst-weakenS (swap-polS i (var p x)) i (dualS ist) 
    = {!!}

  subst-swap-dualG (transmit d t s) i = cong₂ (transmit d) (subst-swap-dualT t i) (subst-swap-dualS s i)
  subst-swap-dualG (choice d m alt) i = cong (choice d m) (ext (λ x → subst-swap-dualS (alt x) i))
  subst-swap-dualG end i = refl


module NotSufficientlyGeneral where
  subst-swap-dualT : ∀ {ist} → (t : IND.Type (suc n)) →
    st-substT t zero ist ≡ st-substT (swap-polT zero t) zero (IND.dualS ist)
  subst-swap-dualS : ∀ {ist} → (st : IND.SType (suc n)) → st-substS st zero ist ≡ st-substS (swap-polS zero st) zero (IND.dualS ist)
  subst-swap-dualG : ∀ {ist} → (gst : IND.GType (suc n)) → 
    st-substG gst zero ist ≡ st-substG (swap-polG zero gst) zero (IND.dualS ist)

  subst-swap-dualT TUnit = refl
  subst-swap-dualT TInt = refl
  subst-swap-dualT (TPair t t₁) = cong₂ TPair (subst-swap-dualT t) (subst-swap-dualT t₁)
  subst-swap-dualT (TChan st) = cong TChan (subst-swap-dualS st)

  subst-swap-dualS (gdd gst) = cong gdd (subst-swap-dualG gst)
  subst-swap-dualS{n} (rec gst) = cong rec {!subst-swap-dualG!}
  subst-swap-dualS {ist = ist} (var POS zero) rewrite sym (IND.dual-invS ist) = refl
  subst-swap-dualS {ist = ist} (var NEG zero) = refl
  subst-swap-dualS {suc n} {ist = ist} (var p (suc i)) = {!st-substS (var p (suc i)) zero ist!}

  subst-swap-dualG (transmit d t s) = cong₂ (transmit d) (subst-swap-dualT t) (subst-swap-dualS s)
  subst-swap-dualG (choice d m alt) = cong (choice d m) (ext (subst-swap-dualS ∘ alt))
  subst-swap-dualG end = refl

open Experimental

----------------------------------------------------------------------

swap-i-weakenS : (i : Fin (suc n)) (s : IND.SType n) → swap-polS i (weaken1'S i s) ≡ weaken1'S i s
swap-i-weakenG : (i : Fin (suc n)) (g : IND.GType n) → swap-polG i (weaken1'G i g) ≡ weaken1'G i g
swap-i-weakenT : (i : Fin (suc n)) (t : IND.TType n) → swap-polT i (weaken1'T i t) ≡ weaken1'T i t

swap-i-weakenS i (gdd gst) = cong gdd (swap-i-weakenG i gst)
swap-i-weakenS i (rec gst) = cong rec (swap-i-weakenG (suc i) gst)
swap-i-weakenS zero (var p zero) = refl
swap-i-weakenS (suc i) (var p zero) = refl
swap-i-weakenS zero (var p (suc x)) = refl
swap-i-weakenS (suc i) (var p (suc x)) = cong weaken1S (swap-i-weakenS i (var p x))

swap-i-weakenG i (transmit d t s) = cong₂ (transmit d) (swap-i-weakenT i t) (swap-i-weakenS i s)
swap-i-weakenG i (choice d m alt) = cong (choice d m) (ext (swap-i-weakenS i ∘ alt))
swap-i-weakenG i end = refl

swap-i-weakenT i TUnit = refl
swap-i-weakenT i TInt = refl
swap-i-weakenT i (TPair t₁ t₂) = cong₂ TPair (swap-i-weakenT i t₁) (swap-i-weakenT i t₂)
swap-i-weakenT i (TChan x) = cong TChan (swap-i-weakenS i x)

subst-swapG : (ist : IND.SType 0) (i : Fin (suc (suc n))) (j : Fin′ i) (g : GType (suc (suc n))) →
  st-substG (swap-polG (inject j) g) i ist ≡ swap-polG (inject! j) (st-substG g i ist)
subst-swapS : (ist : IND.SType 0) (i : Fin (suc (suc n))) (j : Fin′ i) (s : IND.SType (suc (suc n))) →
  st-substS (swap-polS (inject j) s) i ist ≡ swap-polS (inject! j) (st-substS s i ist)
subst-swapT : (ist : IND.SType 0) (i : Fin (suc (suc n))) (j : Fin′ i) (g : IND.Type (suc (suc n))) →
  st-substT (swap-polT (inject j) g) i ist ≡ swap-polT (inject! j) (st-substT g i ist)

subst-swapG ist i j (transmit d t s) = cong₂ (transmit d) (subst-swapT ist i j t) (subst-swapS ist i j s)
subst-swapG ist i j (choice d m alt) = cong (choice d m) (ext (λ x → subst-swapS ist i j (alt x)))
subst-swapG ist i j end = refl

subst-swapS ist i j (gdd gst) = cong gdd (subst-swapG ist i j gst)
subst-swapS ist i j (rec gst) = cong rec (subst-swapG ist (suc i) (suc j) gst)
subst-swapS{zero} ist zero () (var p zero)
subst-swapS {zero} ist (suc zero) zero (var p zero) = refl
subst-swapS {zero} ist (suc zero) zero (var p (suc x))
  rewrite swap-i-weakenS zero (st-substS (var p x) zero ist) = refl
subst-swapS{suc n} ist (suc i) zero (var p zero) = refl
subst-swapS{suc n} ist (suc i) (suc j) (var p zero) = refl
subst-swapS{suc n} ist zero () (var p (suc x))
subst-swapS{suc n} ist (suc i) zero (var p (suc x))
  rewrite swap-i-weakenS zero (st-substS (var p x) i ist) = refl
subst-swapS{suc n} ist (suc i) (suc j) (var p (suc x)) 
  rewrite subst-weakenS (swap-polS (inject j) (var p x)) i ist
  | swap-weakenS (inject! j) (st-substS (var p x) i ist)
  = cong weaken1S (subst-swapS ist i j (var p x))

subst-swapT ist i j TUnit = refl
subst-swapT ist i j TInt = refl
subst-swapT ist i j (TPair t t₁) = cong₂ TPair (subst-swapT ist i j t) (subst-swapT ist i j t₁)
subst-swapT ist i j (TChan x) = cong TChan (subst-swapS ist i j x)

-- show that the dualS function is compatible with unfolding
-- that is
-- COI.dual ∘ ind2coi ≈ ind2coi ∘ IND.dual

dual-compatibleS : (ist : IND.SType 0) →
  COI.dual (ind2coiS ist) ≈ ind2coiS (IND.dualS ist)
dual-compatibleG : (gst : IND.GType 0) →
  COI.dualF (ind2coiG gst) ≈' ind2coiG (IND.dualG gst)
dual-compatibleG-subst : (gst : IND.GType 1) (ist : IND.SType 0) →
  (dualF (ind2coiG (st-substG gst zero ist))) ≈'
  (ind2coiG (st-substG (swap-polG zero (dualG gst)) zero (IND.dualS ist)))
dual-compatibleS-subst : (gst : IND.SType 1) (ist : IND.SType 0) →
  (COI.dual (ind2coiS (st-substS gst zero ist))) ≈
  (ind2coiS (st-substS (swap-polS zero (IND.dualS gst)) zero (IND.dualS ist)))

{-
dual-comp-substG : (gst : GType 1) (ist : IND.SType 0) →
  (dualF (ind2coiG (st-substG gst zero ist))) ≈'
  (ind2coiG (st-substG (swap-polG zero (dualG gst)) zero (dualS ist)))

dual-comp-substG (transmit d t s) ist = {!!}
dual-comp-substG (choice d m alt) ist = {!!}
dual-comp-substG end ist = {!!}
-}

Equiv.force (dual-compatibleS (gdd gst)) = dual-compatibleG gst
Equiv.force (dual-compatibleS (rec gst)) = dual-compatibleG-subst gst (rec gst)

dual-compatibleG (transmit d t s) = eq-transmit (dual-dir d) ≈ᵗ-refl (dual-compatibleS s)
dual-compatibleG (choice d m alt) = eq-choice (dual-dir d) (dual-compatibleS ∘ alt)
dual-compatibleG end = eq-end

dual-compatibleG-subst (transmit d t s) ist
  rewrite (subst-swap-dualT{ist = ist} t zero) =
  eq-transmit (dual-dir d) ≈ᵗ-refl (dual-compatibleS-subst s ist)
dual-compatibleG-subst (choice d m alt) ist =
  eq-choice (dual-dir d) λ i → dual-compatibleS-subst (alt i) ist
dual-compatibleG-subst end ist = eq-end

Equiv.force (dual-compatibleS-subst (gdd gst) ist) =
  dual-compatibleG-subst gst ist
Equiv.force (dual-compatibleS-subst (rec gst) ist)
  -- rewrite swap-swapG (dualG gst) (suc zero) zero
  -- | swap-pol-dualG (suc zero) gst
  rewrite (subst-swap-dualG {ist = dualS ist} (swap-polG (suc zero) (swap-polG zero (dualG gst))) (suc zero))
  | sym (IND.dual-invS ist)
  | swap-pol-invG (suc zero) (swap-polG zero (dualG gst))
  | subst-swapG ist (suc zero) zero (dualG gst)
  =
  let gst' = (st-substG gst (suc zero) ist) in
  let ist' = (rec gst') in
  let ppp' = dual-compatibleG-subst gst' ist' in
-- ppp' : dualF
-- (ind2coiG
--  (st-substG (st-substG gst (suc zero) ist) zero
--   (rec (st-substG gst (suc zero) ist))))
-- ≈'
-- ind2coiG
-- (st-substG (swap-polG zero (dualG (st-substG gst (suc zero) ist)))
--  zero (rec (swap-polG zero (dualG (st-substG gst (suc zero) ist)))))
  {!!}
  -- rewrite swap-pol-invG {!!} (dualG gst) = {!!}
dual-compatibleS-subst (var POS zero) ist rewrite trivial-weakenS ist | trivial-weakenS (IND.dualS ist) = dual-compatibleS ist
dual-compatibleS-subst (var NEG zero) ist rewrite trivial-weakenS (IND.dualS ist) | trivial-weakenS (IND.dualS (IND.dualS ist)) = dual-compatibleS (IND.dualS ist)



--         (st-substG (swap-polG i gst) i (dualS ist)) ≡
--         (st-substG gst i ist)
