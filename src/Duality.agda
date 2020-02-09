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

open import Extensionality

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

open import Direction

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
    t t₁ t₂ t₃ t₁' t₂' t₃' : Type
    s s₁ s₂ s₃ : SType
    s' s₁' s₂' s₃' : STypeF SType

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

  -- reflexivity
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

  -- symmetry
  ≈-symm : s₁ ≈ s₂ → s₂ ≈ s₁
  ≈'-symm : s₁' ≈' s₂' → s₂' ≈' s₁'
  ≈ᵗ-symm : t₁ ≈ᵗ t₂ → t₂ ≈ᵗ t₁

  force (≈-symm s₁≈s₂) = ≈'-symm (force s₁≈s₂)

  ≈'-symm (eq-transmit d x x₁) = eq-transmit d (≈ᵗ-symm x) (≈-symm x₁)
  ≈'-symm (eq-choice d x) = eq-choice d (λ i → ≈-symm (x i))
  ≈'-symm eq-end = eq-end

  ≈ᵗ-symm eq-unit = eq-unit
  ≈ᵗ-symm eq-int = eq-int
  ≈ᵗ-symm (eq-pair t₁≈t₂ t₁≈t₃) = eq-pair (≈ᵗ-symm t₁≈t₂) (≈ᵗ-symm t₁≈t₃)
  ≈ᵗ-symm (eq-chan x) = eq-chan (≈-symm x)
  
  -- transitivity
  ≈-trans : s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
  ≈'-trans : s₁' ≈' s₂' → s₂' ≈' s₃' → s₁' ≈' s₃'
  ≈ᵗ-trans : t₁ ≈ᵗ t₂ → t₂ ≈ᵗ t₃ → t₁ ≈ᵗ t₃

  force (≈-trans s₁≈s₂ s₂≈s₃) = ≈'-trans (force s₁≈s₂) (force s₂≈s₃)
  
  ≈'-trans (eq-transmit d tt₁ ss₁) (eq-transmit .d tt₂ ss₂) = eq-transmit d (≈ᵗ-trans tt₁ tt₂) (≈-trans ss₁ ss₂)
  ≈'-trans (eq-choice d x) (eq-choice .d x₁) = eq-choice d (λ i → ≈-trans (x i) (x₁ i))
  ≈'-trans eq-end eq-end = eq-end
  
  ≈ᵗ-trans eq-unit eq-unit = eq-unit
  ≈ᵗ-trans eq-int eq-int = eq-int
  ≈ᵗ-trans (eq-pair t₁≈ᵗt₂ t₁≈ᵗt₃) (eq-pair t₂≈ᵗt₃ t₂≈ᵗt₄) = eq-pair (≈ᵗ-trans t₁≈ᵗt₂ t₂≈ᵗt₃) (≈ᵗ-trans t₁≈ᵗt₃ t₂≈ᵗt₄)
  ≈ᵗ-trans (eq-chan ss₁) (eq-chan ss₂) = eq-chan (≈-trans ss₁ ss₂)

  ----------------------------------------------------------------------
  -- relational duality
  data DualD : Dir → Dir → Set where
    dual-sr : DualD SND RCV
    dual-rs : DualD RCV SND

  -- session type duality
  data DualF (R : SType → SType → Set) : STypeF SType → STypeF SType → Set where
    dual-transmit : DualD d₁ d₂ → t₁ ≈ᵗ t₂ → R s₁ s₂ → DualF R (transmit d₁ t₁ s₁) (transmit d₂ t₂ s₂)
    dual-choice : ∀ {alt alt'} → DualD d₁ d₂ → ((i : Fin m) → R (alt i) (alt' i)) → DualF R (choice d₁ m alt) (choice d₂ m alt')
    dual-end : DualF R end end

  record Dual (s₁ : SType) (s₂ : SType) : Set where
    coinductive
    field force : DualF Dual (force s₁) (force s₂)

  -- open Dual

  _⊥_ = Dual
  _⊥'_ = DualF Dual
  -- _≈ᵗ_ = EquivT Equiv

  -- symmetric

  DualD-symm : DualD d₁ d₂ → DualD d₂ d₁
  DualD-symm dual-sr = dual-rs
  DualD-symm dual-rs = dual-sr

  ⊥-symm : s₁ ⊥ s₂ → s₂ ⊥ s₁
  ⊥'-symm : s₁' ⊥' s₂' → s₂' ⊥' s₁'

  Dual.force (⊥-symm s₁⊥s₂) = ⊥'-symm (Dual.force s₁⊥s₂)

  ⊥'-symm (dual-transmit x x₁ x₂) = dual-transmit (DualD-symm x) (≈ᵗ-symm x₁) (⊥-symm x₂)
  ⊥'-symm (dual-choice x x₁) = dual-choice (DualD-symm x) (⊥-symm ∘ x₁)
  ⊥'-symm dual-end = dual-end

  -- involutory
  DualD-inv : DualD d₁ d₂ → DualD d₂ d₃ → d₁ ≡ d₃
  DualD-inv dual-sr dual-rs = refl
  DualD-inv dual-rs dual-sr = refl

  ⊥-inv : s₁ ⊥ s₂ → s₂ ⊥ s₃ → s₁ ≈ s₃
  ⊥'-inv : s₁' ⊥' s₂' → s₂' ⊥' s₃' → s₁' ≈' s₃'

  force (⊥-inv s₁⊥s₂ s₂⊥s₃) = ⊥'-inv (Dual.force s₁⊥s₂) (Dual.force s₂⊥s₃)

  ⊥'-inv (dual-transmit dd₁ tt₁ ss₁) (dual-transmit dd₂ tt₂ ss₂) rewrite DualD-inv dd₁ dd₂ = eq-transmit _ (≈ᵗ-trans tt₁ tt₂) (⊥-inv ss₁ ss₂)
  ⊥'-inv (dual-choice dd₁ ss₁) (dual-choice dd₂ ss₂) rewrite DualD-inv dd₁ dd₂ = eq-choice _ (λ i → ⊥-inv (ss₁ i) (ss₂ i))
  ⊥'-inv dual-end dual-end = eq-end

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

  -----------------------------------------------------------------------
  -- relational duality vs functional duality

  -- soundness

  dual-soundD : DualD d (dual-dir d)
  dual-soundD {SND} = dual-sr
  dual-soundD {RCV} = dual-rs

  dual-soundS : s ⊥ dual s
  dual-soundF : s' ⊥' dualF s'
  
  Dual.force dual-soundS = dual-soundF

  dual-soundF {transmit d t s} = dual-transmit dual-soundD ≈ᵗ-refl dual-soundS
  dual-soundF {choice d m alt} = dual-choice dual-soundD (λ i → dual-soundS)
  dual-soundF {end} = dual-end

  -- completeness

  dual-completeD : DualD d₁ d₂ → d₁ ≡ dual-dir d₂
  dual-completeD dual-sr = refl
  dual-completeD dual-rs = refl

  dual-completeS : s₁ ⊥ s₂ → s₁ ≈ dual s₂
  dual-completeF : s₁' ⊥' s₂' → s₁' ≈' dualF s₂'
  
  force (dual-completeS s₁⊥s₂) = dual-completeF (Dual.force s₁⊥s₂)
  
  dual-completeF (dual-transmit dd tt ss) rewrite dual-completeD dd = eq-transmit _ tt (dual-completeS ss)
  dual-completeF (dual-choice dd x₁) rewrite dual-completeD dd = eq-choice _ (λ i → dual-completeS (x₁ i))
  dual-completeF dual-end = eq-end

----------------------------------------------------------------------
-- session type inductively with explicit rec

module IND where

  data Polarity : Set where
    POS NEG : Polarity

  mutual
    data Type (n : ℕ) : Set where
      TUnit TInt : Type n
      TPair : (T₁ : Type n) (T₂ : Type n) → Type n
      TChan : (S : SType n) → Type n
    
    data SType (n : ℕ) : Set where
      gdd : (G : GType n) → SType n
      rec : (G : GType (suc n) ) → SType n
      var : (p : Polarity) → (x : Fin n) → SType n

    data GType (n : ℕ) : Set where
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
    s00 = sxy 0 0F
    s10 : SType 1
    s10 = sxy 1 0F
    s11 : SType 1
    s11 = sxy 1 1F
    s22 : SType 2
    s22 = sxy 2 2F
  
    check-weaken-s01 : weaken1'S 0F s00 ≡ s10
    check-weaken-s01 = refl

    check-weaken-s1-s2 : weaken1'S 0F s11 ≡ s22
    check-weaken-s1-s2 = refl

    check-weaken-s21 : weaken1'S 1F (sxy 2 1F) ≡ sxy 3 1F
    check-weaken-s21 = refl
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

  weak-weakN : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (x : Fin n)
    → weaken1'N (suc i) (weaken1'N j x) ≡ weaken1'N (inject₁ j) (weaken1'N i x)
  weak-weakG : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (g : GType n)
    → weaken1'G (suc i) (weaken1'G j g) ≡ weaken1'G (inject₁ j) (weaken1'G i g)
  weak-weakS : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (s : SType n)
    → weaken1'S (suc i) (weaken1'S j s) ≡ weaken1'S (inject₁ j) (weaken1'S i s)
  weak-weakT : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (t : Type n)
    → weaken1'T (suc i) (weaken1'T j t) ≡ weaken1'T (inject₁ j) (weaken1'T i t)

  weak-weakN 0F 0F le x                              = refl
  weak-weakN (suc i) 0F le x                         = refl
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
  weaken1-weakenN m 0F 0F           = refl
  weaken1-weakenN m 0F (suc x)      = refl
  weaken1-weakenN m (suc j) 0F      = refl
  weaken1-weakenN m (suc j) (suc x) = cong suc (weaken1-weakenN m j x)
 
  weaken1-weakenS : (m : ℕ) (j : Fin (suc n)) (s : SType n)
    → weakenS m (weaken1'S j s) ≡ weaken1'S (inject+ m j) (weakenS m s) 
  weaken1-weakenG : (m : ℕ) (j : Fin (suc n)) (g : GType n)
    → weakenG m (weaken1'G j g) ≡ weaken1'G (inject+ m j) (weakenG m g)
  weaken1-weakenT : (m : ℕ) (j : Fin (suc n)) (t : Type n)
    → weakenT m (weaken1'T j t) ≡ weaken1'T (inject+ m j) (weakenT m t)
  weaken1-weakenS m j (gdd gst) = cong gdd (weaken1-weakenG m j gst)
  weaken1-weakenS m j (rec gst) = cong rec (weaken1-weakenG m (suc j) gst)
  weaken1-weakenS m 0F (var p 0F)      = refl
  weaken1-weakenS m 0F (var p (suc x)) = refl
  weaken1-weakenS {suc n} m (suc j) (var p 0F)      = refl
  weaken1-weakenS {suc n} m (suc j) (var p (suc x)) = cong (var p) (cong suc (weaken1-weakenN m j x))

  weaken1-weakenG m j (transmit d t s)  = cong₂ (transmit d) (weaken1-weakenT m j t) (weaken1-weakenS m j s)
  weaken1-weakenG m j (choice d m₁ alt) = cong (choice d m₁) (ext (weaken1-weakenS m j ∘ alt))
  weaken1-weakenG m j end = refl

  weaken1-weakenT m j TUnit = refl
  weaken1-weakenT m j TInt = refl
  weaken1-weakenT m j (TPair t t₁) = cong₂ TPair (weaken1-weakenT m j t) (weaken1-weakenT m j t₁)
  weaken1-weakenT m j (TChan x) = cong TChan (weaken1-weakenS m j x)

----------------------------------------------------------------------

  -- weakening of later index
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
  swap-weaken1'S{suc n} (suc i) (suc j) (var p (suc x)) rewrite (weak-weakS i 0F z≤n (swap-polS (inject! j) (var p x))) = 
    let sws = swap-weaken1'S{n} i j (var p x) in cong (weaken1'S 0F) sws

  swap-weaken1'T i j TUnit         = refl
  swap-weaken1'T i j TInt          = refl
  swap-weaken1'T i j (TPair t₁ t₂) = cong₂ TPair (swap-weaken1'T i j t₁) (swap-weaken1'T i j t₂)
  swap-weaken1'T i j (TChan s)     = cong TChan (swap-weaken1'S i j s)

----------------------------------------------------------------------

  -- weakening of earlier index
  swap-weaken1'S< : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) → (s : SType (suc n)) →
    swap-polS (suc i) (weaken1'S (inject₁ j) s) ≡ weaken1'S (inject₁ j) (swap-polS i s)
  swap-weaken1'G< : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) → (g : GType (suc n)) →
    swap-polG (suc i) (weaken1'G (inject₁ j) g) ≡ weaken1'G (inject₁ j) (swap-polG i g)
  swap-weaken1'T< : (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) → (t : Type (suc n)) →
    swap-polT (suc i) (weaken1'T (inject₁ j) t) ≡ weaken1'T (inject₁ j) (swap-polT i t)

  swap-weaken1'S< i j le (gdd gst)       = cong gdd (swap-weaken1'G< i j le gst)
  swap-weaken1'S< i j le (rec gst)       = cong rec (swap-weaken1'G< (suc i) (suc j) (s≤s le) gst)
  swap-weaken1'S< 0F 0F le (var p x)     = refl
  swap-weaken1'S< (suc i) 0F le (var p x) = refl
  swap-weaken1'S<{suc n} (suc i) (suc j) le (var p zero) = refl
  swap-weaken1'S<{suc n} (suc i) (suc j) (s≤s le) (var p (suc x)) rewrite (weak-weakS (inject₁ j) 0F z≤n (swap-polS i (var p x))) =
    let sws = swap-weaken1'S<{n} i j le (var p x) in cong (weaken1'S 0F) sws

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

  swap-weakenS i s = swap-weaken1'S< i 0F z≤n s
  swap-weakenG i g = swap-weaken1'G< i 0F z≤n g
  swap-weakenT i t = swap-weaken1'T< i 0F z≤n t

----------------------------------------------------------------------

  -- swapping of general weakening
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
  swap-weakenS' m 0F (var p 0F)      = refl
  swap-weakenS' m (suc j) (var p 0F) = refl
  swap-weakenS' m 0F (var p 1F)      = refl
  swap-weakenS' m 0F (var p (suc (suc x))) = refl
  swap-weakenS' {suc n} m (suc j) (var p (suc x)) rewrite (weaken1-weakenS m 0F (swap-polS j (var p x))) =
     let rst = swap-weakenS'{n} m j (var p x) in cong weaken1S rst

  swap-weakenT' m j TUnit = refl
  swap-weakenT' m j TInt = refl
  swap-weakenT' m j (TPair t t₁) = cong₂ TPair (swap-weakenT' m j t) (swap-weakenT' m j t₁)
  swap-weakenT' m j (TChan x) = cong TChan (swap-weakenS' m j x)

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

  dual-weakenS : (i : Fin (suc n)) (s : SType n) → dualS (weaken1'S i s) ≡ weaken1'S i (dualS s)
  dual-weakenG : (i : Fin (suc n)) (g : GType n) → dualG (weaken1'G i g) ≡ weaken1'G i (dualG g)

  dual-weakenS i (gdd gst) = cong gdd (dual-weakenG i gst)
  dual-weakenS i (rec gst) rewrite (sym (swap-weaken1'G (suc i) 0F (dualG gst))) = cong rec (cong (swap-polG 0F) (dual-weakenG (suc i) gst))
  dual-weakenS i (var p x) = refl

  dual-weakenG i (transmit d t s) = cong₂ (transmit (dual-dir d)) refl (dual-weakenS i s)
  dual-weakenG i (choice d m alt) = cong (choice (dual-dir d) m) (ext (dual-weakenS i ∘ alt))
  dual-weakenG i end = refl

  dual-weakenS' : (m : ℕ) (s : SType n) → dualS (weakenS m s) ≡ weakenS m (dualS s)
  dual-weakenG' : (m : ℕ) (g : GType n) → dualG (weakenG m g) ≡ weakenG m (dualG g)

  dual-weakenS' n (gdd gst) = cong gdd (dual-weakenG' n gst)
  dual-weakenS' n (rec gst) rewrite (sym (swap-weakenG' n 0F (dualG gst))) = cong rec (cong (swap-polG 0F) (dual-weakenG' n gst))
  dual-weakenS' n (var p x) = refl
 
  dual-weakenG' n (transmit d t s) = cong₂ (transmit (dual-dir d)) refl (dual-weakenS' n s)
  dual-weakenG' n (choice d m alt) = cong (choice (dual-dir d) m) (ext (dual-weakenS' n ∘ alt))
  dual-weakenG' n end = refl 

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
    with var-suc i x p
  ... | p' , snd rewrite snd = refl
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
     rewrite (dual-weakenS 0F (swap-polS i (var p x))) =  cong weaken1S (swap-pol-dualS i (var p x)) 

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

  dual-if-dual : (p : Polarity) (ist : SType 0) → dual-if p ist ≡ dual-if (dual-pol p) (dualS ist)
  dual-if-dual POS ist = (dual-invS ist)
  dual-if-dual NEG ist = refl 

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

  trivial-subst-var : (p : Polarity) (x : Fin n) (ist₁ ist₂ : SType 0)
    → st-substS (var p (suc x)) 0F ist₁ ≡ st-substS (var p (suc x)) 0F ist₂
  trivial-subst-var p 0F ist1 ist2 = refl
  trivial-subst-var p (suc x) ist1 ist2 = refl

  trivial-subst-var' : (p : Polarity) (i : Fin n) (ist₁ ist₂ : SType 0)
    → st-substS (var p 0F) (suc i) ist₁ ≡ st-substS (var p 0F) (suc i) ist₂
  trivial-subst-var' p 0F ist1 ist2 = refl
  trivial-subst-var' p (suc x) ist1 ist2 = refl

----------------------------------------------------------------------
  -- equivalence
  variable
    t t₁ t₂ t₁' t₂' : Type n
    s s₁ s₂ : SType n
    g g₁ g₂ : GType n

  unfold : SType 0 → GType 0
  unfold (gdd gst) = gst
  unfold (rec gst) = st-substG gst 0F (rec gst)

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


----------------------------------------------------------------------
-- provide an embedding of IND to COI

open COI
open IND hiding (_≈_ ; _≈'_ ; ≈-refl ; ≈'-refl ; ≈ᵗ-refl)

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

----------------------------------------------------------------------

subst-weakenS : (s : IND.SType (suc n)) (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (s0 : IND.SType 0)
  → st-substS (weaken1'S (inject₁ j) s) (suc i) s0 ≡ weaken1'S j (st-substS s i s0)
subst-weakenG : (g : IND.GType (suc n)) (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (s0 : IND.SType 0)
  → st-substG (weaken1'G (inject₁ j) g) (suc i) s0 ≡ weaken1'G j (st-substG g i s0)
subst-weakenT : (t : IND.Type (suc n)) (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (s0 : IND.SType 0)
  → st-substT (weaken1'T (inject₁ j) t) (suc i) s0 ≡ weaken1'T j (st-substT t i s0)

subst-weakenS (gdd gst) i j le s0 = cong gdd (subst-weakenG gst i j le s0)
subst-weakenS (rec gst) i j le s0 = cong rec (subst-weakenG gst (suc i) (suc j) (s≤s le) s0)
subst-weakenS (var p x) 0F 0F le s0 = refl
subst-weakenS {suc n} (var p x) (suc i) 0F le s0 = refl
subst-weakenS {suc n} (var p 0F) (suc i) (suc j) le s0 = refl
subst-weakenS {suc n} (var p (suc x)) (suc i) (suc j) (s≤s le) s0 rewrite (weak-weakS j 0F z≤n (st-substS (var p x) i s0))
  = cong (weaken1'S 0F) (subst-weakenS (var p x) i j le s0)

subst-weakenG (transmit d t s) i j le s0 = cong₂ (transmit d) (subst-weakenT t i j le s0) (subst-weakenS s i j le s0)
subst-weakenG (choice d m alt) i j le s0 = cong (choice d m) (ext (λ m' → subst-weakenS (alt m') i j le s0 ))
subst-weakenG end i j le s0 = refl

subst-weakenT TUnit i j le s0 = refl
subst-weakenT TInt i j le s0 = refl
subst-weakenT (TPair t t₁) i j le s0 = cong₂ TPair (subst-weakenT t i j le s0) (subst-weakenT t₁ i j le s0)
subst-weakenT (TChan s) i j le s0 = cong TChan (subst-weakenS s i j le s0)


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
subst-swap-dualS {n} {ist} (var p zero) zero = cong (weakenS n) (dual-if-dual p ist)
subst-swap-dualS {suc n} (var p zero) (suc i) = refl
subst-swap-dualS {suc n} (var p (suc x)) zero = refl
subst-swap-dualS {suc n}{ist} (var p (suc x)) (suc i)      
  rewrite subst-weakenS (swap-polS i (var p x)) i 0F z≤n (dualS ist) 
  = cong (weaken1'S 0F) (subst-swap-dualS ((var p x)) i)

subst-swap-dualG (transmit d t s) i = cong₂ (transmit d) (subst-swap-dualT t i) (subst-swap-dualS s i)
subst-swap-dualG (choice d m alt) i = cong (choice d m) (ext (λ x → subst-swap-dualS (alt x) i))
subst-swap-dualG end i = refl

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
  rewrite subst-weakenS (swap-polS (inject j) (var p x)) i 0F z≤n ist
  | swap-weakenS (inject! j) (st-substS (var p x) i ist)
  = cong weaken1S (subst-swapS ist i j (var p x))

subst-swapT ist i j TUnit = refl
subst-swapT ist i j TInt = refl
subst-swapT ist i j (TPair t t₁) = cong₂ TPair (subst-swapT ist i j t) (subst-swapT ist i j t₁)
subst-swapT ist i j (TChan x) = cong TChan (subst-swapS ist i j x)

----------------------------------------------------------------------

dual-recT' : (t : TType (suc n)) (i : Fin (suc n)) (ist : IND.SType 0)
  → st-substT (swap-polT i t) i (dualS ist) ≡ st-substT t i ist
dual-recG' : (g : GType (suc n)) (i : Fin (suc n)) (ist : IND.SType 0)
  → st-substG (swap-polG i g) i (dualS ist) ≡ st-substG g i ist
dual-recS' : (s : IND.SType (suc n)) (i : Fin (suc n)) (ist : IND.SType 0)
  → st-substS (swap-polS i s) i (dualS ist) ≡ st-substS s i ist

dual-recT' TUnit i ist = refl
dual-recT' TInt i ist = refl
dual-recT' (TPair t t₁) i ist = cong₂ TPair (dual-recT' t i ist) (dual-recT' t₁ i ist)
dual-recT' (TChan s) i ist = cong TChan (dual-recS' s i ist)

dual-recG' (transmit d t s) i ist = cong₂ (transmit d) (dual-recT' t i ist) (dual-recS' s i ist)
dual-recG' (choice d m alt) i ist = cong (choice d m) (ext (λ m' → dual-recS' (alt m') i ist))
dual-recG' end i ist = refl

dual-recS' (gdd gst) i ist = cong gdd (dual-recG' gst i ist)
dual-recS' (rec gst) i ist = cong rec (dual-recG' gst (suc i) ist)
dual-recS' (var p 0F) 0F ist rewrite (dual-if-dual p ist) = refl
dual-recS' (var p (suc x)) 0F ist = trivial-subst-var p x (dualS ist) (ist)
dual-recS' (var p 0F) (suc i) ist = trivial-subst-var' p i (dualS ist) (ist) 
dual-recS' (var p (suc x)) (suc i) ist rewrite (subst-swap-dualS{ist = ist} (var p (suc x)) (suc i))
  = refl

----------------------------------------------------------------------

-- show that the dualS function is compatible with unfolding
-- that is
-- COI.dual ∘ ind2coi ≈ ind2coi ∘ IND.dual

dual-lemmaS : (s : IND.SType (suc n)) (j : Fin (suc n)) (s0 : IND.SType 0)
  → st-substS (dualS s) j s0 ≡ dualS (st-substS s j s0)
dual-lemmaG : (g : IND.GType (suc n)) (j : Fin (suc n)) (s0 : IND.SType 0)
  → st-substG (dualG g) j s0 ≡ dualG (st-substG g j s0)

dual-lemmaS (gdd gst) j s0 = cong gdd (dual-lemmaG gst j s0)
dual-lemmaS (rec gst) j s0 rewrite (subst-swapG s0 (suc j) 0F (dualG gst)) =
  let rst = dual-lemmaG gst (suc j) s0 in cong rec (cong (swap-polG 0F) rst)
dual-lemmaS {n} (var POS 0F) 0F s0          = sym (dual-weakenS' n s0)
dual-lemmaS {n} (var NEG 0F) 0F s0 rewrite (sym (dual-weakenS' n s0)) | (sym (dual-invS (weakenS n s0))) = refl
dual-lemmaS {suc n} (var POS 0F) (suc j) s0 = refl
dual-lemmaS {suc n} (var NEG 0F) (suc j) s0 = refl
dual-lemmaS {suc n} (var POS (suc x)) 0F s0 = refl
dual-lemmaS {suc n} (var NEG (suc x)) 0F s0 = refl
dual-lemmaS {suc n} (var POS (suc x)) (suc j) s0 rewrite (dual-weakenS 0F (st-substS (var POS x) j s0)) = cong (weaken1'S 0F) (dual-lemmaS (var POS x) j s0)
dual-lemmaS {suc n} (var NEG (suc x)) (suc j) s0 rewrite (dual-weakenS 0F (st-substS (var NEG x) j s0)) = cong (weaken1'S 0F) (dual-lemmaS (var NEG x) j s0)

dual-lemmaG (transmit d t s) j s0 = cong₂ (transmit (dual-dir d)) refl (dual-lemmaS s j s0)
dual-lemmaG (choice d m alt) j s0 = cong (choice (dual-dir d) m) (ext (λ m' → dual-lemmaS (alt m') j s0))
dual-lemmaG end j s0 = refl


dual-compatibleS : (ist : IND.SType 0) →
  COI.dual (ind2coiS ist) ≈ ind2coiS (IND.dualS ist)
dual-compatibleG : (gst : IND.GType 0) →
  COI.dualF (ind2coiG gst) ≈' ind2coiG (IND.dualG gst)

Equiv.force (dual-compatibleS (gdd gst)) = dual-compatibleG gst
Equiv.force (dual-compatibleS (rec gst))
  rewrite (dual-recG' (dualG gst) 0F (rec gst))  | dual-lemmaG gst 0F (rec gst) = dual-compatibleG (st-substG gst zero (rec gst)) 

dual-compatibleG (transmit d t s) = eq-transmit (dual-dir d) ≈ᵗ-refl (dual-compatibleS s)
dual-compatibleG (choice d m alt) = eq-choice (dual-dir d) (dual-compatibleS ∘ alt)
dual-compatibleG end = eq-end

