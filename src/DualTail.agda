module DualTail where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec

open import Function

open import Duality

-- session types restricted to tail recursion

data Type : Set
data SType (n : ℕ) : Set
data GType (n : ℕ) : Set

data Type where
  TUnit TInt : Type
  TPair : (t₁ t₂ : Type) → Type
  TChan : (s : SType 0) → Type

data SType n where
  gdd : (g : GType n) → SType n
  rec : (g : GType (suc n)) → SType n
  var : (x : Fin n) → SType n

data GType n where
  transmit : (d : Dir) (t : Type) (s : SType n) → GType n
  choice : (d : Dir) (m : ℕ) (alt : Fin m → SType n) → GType n
  end : GType n

-- naive definition of duality for tail recursive session types

dualS : SType n → SType n
dualG : GType n → GType n

dualS (gdd g) = gdd (dualG g)
dualS (rec g) = rec (dualG g)
dualS (var x) = var x

dualG (transmit d t s) = transmit (dual-dir d) t (dualS s)
dualG (choice d m alt) = choice (dual-dir d) m (dualS ∘ alt)
dualG end = end

-- weakening

weakenS : (n : ℕ) → SType m → SType (m + n)
weakenG : (n : ℕ) → GType m → GType (m + n)

weakenS n (gdd g) = gdd (weakenG n g)
weakenS n (rec g) = rec (weakenG n g)
weakenS n (var x) = var (inject+ n x)

weakenG n (transmit d t s) = transmit d t (weakenS n s)
weakenG n (choice d m alt) = choice d m (weakenS n ∘ alt)
weakenG n end = end

weaken1'S : Fin (suc n) → SType n → SType (suc n)
weaken1'G : Fin (suc n) → GType n → GType (suc n)

weaken1'S i (gdd g) = gdd (weaken1'G i g )
weaken1'S i (rec g) = rec (weaken1'G (suc i) g)
weaken1'S i (var x) = var (IND.weaken1'N i x)

weaken1'G i (transmit d t s) = transmit d t (weaken1'S i s)
weaken1'G i (choice d m alt) = choice d m (weaken1'S i ∘ alt)
weaken1'G i end = end

-- substitution

st-substS : SType (suc n) → Fin (suc n) → SType 0 → SType n
st-substG : GType (suc n) → Fin (suc n) → SType 0 → GType n
-- st-substT : Type (suc n) → Fin (suc n) → SType 0 → Type n

st-substS (gdd g) i s0 = gdd (st-substG g i s0)
st-substS (rec g) i s0 = rec (st-substG g (suc i) s0)
st-substS {n} (var 0F) 0F s0 = weakenS n s0
st-substS {suc n} (var 0F) (suc i) s0 = var 0F
st-substS (var (suc x)) 0F s0 = var x
st-substS {suc n} (var (suc x)) (suc i) s0 = weaken1'S 0F (st-substS {n} (var x) i s0)

st-substG (transmit d t s) i s0 = transmit d t (st-substS s i s0)
st-substG (choice d m alt) i s0 = choice d m λ j → st-substS (alt j) i s0
st-substG end i s0 = end

-- injecting tail recursive session types into coinductive session types

tail2coiT : Type → COI.Type
tail2coiS : SType 0 → COI.SType
tail2coiG : GType 0 → COI.STypeF COI.SType

tail2coiT TUnit = COI.TUnit
tail2coiT TInt = COI.TInt
tail2coiT (TPair t t₁) = COI.TPair (tail2coiT t) (tail2coiT t₁)
tail2coiT (TChan s) = COI.TChan (tail2coiS s)

COI.SType.force (tail2coiS (gdd g)) = tail2coiG g
COI.SType.force (tail2coiS (rec g)) = tail2coiG (st-substG g 0F (rec g))

tail2coiG (transmit d t s) = COI.transmit d (tail2coiT t) (tail2coiS s)
tail2coiG (choice d m alt) = COI.choice d m (tail2coiS ∘ alt)
tail2coiG end = COI.end

-- compatibility

_≈_ = COI._≈_
_≈'_ = COI._≈'_

dual-tailS : (s : SType 0) →
  COI.dual (tail2coiS s) ≈ tail2coiS (dualS s)
dual-tailG : (g : GType 0) →
  COI.dualF (tail2coiG g) ≈' tail2coiG (dualG g)

COI.Equiv.force (dual-tailS (gdd g)) = dual-tailG g
COI.Equiv.force (dual-tailS (rec g)) = {!!}

dual-tailG (transmit d t s) = COI.eq-transmit (dual-dir d) COI.≈ᵗ-refl (dual-tailS s)
dual-tailG (choice d m alt) = COI.eq-choice (dual-dir d) (dual-tailS ∘ alt)
dual-tailG end = COI.eq-end
