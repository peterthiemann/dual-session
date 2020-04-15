module DualTail1 where

open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Product

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Duality using (ind2coiS)
open import Types.Direction

import Types.IND as IND
import Types.COI as COI
open import Types.Tail1

private
  variable
    n : ℕ

-- instead of unrolling and substituting, we maintain a stack of bodies of recursive types

data Stack : ℕ → Set where
  ε : Stack 0
  ⟪_,_⟫ : Stack n → GType (suc n) → Stack (suc n)

-- the dual of a stack

dual-stack : Stack n → Stack n
dual-stack ε = ε
dual-stack ⟪ σ , g ⟫ = ⟪ dual-stack σ , dualG g ⟫

-- obtain an entry from the stack
-- technically m = n - i, but we don't need to know

get : (i : Fin n) → Stack n → Σ ℕ λ m → Stack m × GType (suc m)
get zero ⟪ σ , x ⟫ = _ , (σ , x)
get (suc i) ⟪ σ , x ⟫ = get i σ

-- relate a stack entry to the corresponding entry on the dual stack

get-dual-stack : (x : Fin n) (σ : Stack n) →
  get x (dual-stack σ) ≡ map id (map dual-stack dualG) (get x σ)
get-dual-stack zero ⟪ σ , x ⟫ = refl
get-dual-stack (suc x) ⟪ σ , x₁ ⟫ = get-dual-stack x σ

-- mapping tail recursive session types to coinductive session types
-- relies on a stack to unfold variables on the fly

tail2coiT : Type → COI.Type
tail2coiS : Stack n → SType n → COI.SType
tail2coiG : Stack n → GType n → COI.STypeF COI.SType

tail2coiT TUnit = COI.TUnit
tail2coiT TInt = COI.TInt
tail2coiT (TPair t t₁) = COI.TPair (tail2coiT t) (tail2coiT t₁)
tail2coiT (TChan s) = COI.TChan (ind2coiS s)

COI.SType.force (tail2coiS σ (gdd g)) = tail2coiG σ g
COI.SType.force (tail2coiS σ (rec g)) = tail2coiG ⟪ σ , g ⟫ g
COI.SType.force (tail2coiS σ (var x))
  with get x σ
... | m , σ' , gxs = tail2coiG ⟪ σ' , gxs ⟫ gxs

tail2coiG σ (transmit d t s) = COI.transmit d (tail2coiT t) (tail2coiS σ s)
tail2coiG σ (choice d m alt) = COI.choice d m (tail2coiS σ ∘ alt)
tail2coiG σ end = COI.end

-- get coinductive bisimulation in scope

_≈_ = COI._≈_
_≈'_ = COI._≈'_

-- main proposition

dual-tailS : (σ : Stack n) (s : SType n) →
  COI.dual (tail2coiS σ s) ≈ tail2coiS (dual-stack σ) (dualS s)
dual-tailG : (σ : Stack n) (g : GType n) →
  COI.dualF (tail2coiG σ g) ≈' tail2coiG (dual-stack σ) (dualG g)

COI.Equiv.force (dual-tailS σ (gdd g)) = dual-tailG σ g
COI.Equiv.force (dual-tailS σ (rec g)) = dual-tailG ⟪ σ , g ⟫ g
COI.Equiv.force (dual-tailS σ (var x))
  rewrite get-dual-stack x σ
  with get x σ
... | m , σ' , g = dual-tailG ⟪ σ' , g ⟫ g

dual-tailG σ (transmit d t s) = COI.eq-transmit (dual-dir d) COI.≈ᵗ-refl (dual-tailS σ s)
dual-tailG σ (choice d m alt) = COI.eq-choice (dual-dir d) (dual-tailS σ ∘ alt)
dual-tailG σ end = COI.eq-end

-- corrolary for SType 0

dual-tail : ∀ s → COI.dual (tail2coiS ε s) ≈ tail2coiS ε (dualS s)
dual-tail = dual-tailS ε
