module Types.COI where

open import Data.Nat
open import Data.Fin

open import Function

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Types.Direction

variable
  m n : ℕ

--------------------------------------------------------------------
-- session types coinductively

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

-------------------------------------------------------------------
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
