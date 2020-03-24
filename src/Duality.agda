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

open import Direction

open import Auxiliary hiding (m ; n)

----------------------------------------------------------------------
-- session types coinductively

import Types.COI as COI hiding (m ; n)

----------------------------------------------------------------------
-- session type inductively with explicit rec

import Types.IND as IND

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

{-# TERMINATING #-}
subst-weakenS : (s : IND.SType (suc n)) (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (s0 : IND.SType 0)
  → st-substS (weaken1'S (inject₁ j) s) (suc i) s0 ≡ weaken1'S j (st-substS s i s0)
subst-weakenG : (g : IND.GType (suc n)) (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (s0 : IND.SType 0)
  → st-substG (weaken1'G (inject₁ j) g) (suc i) s0 ≡ weaken1'G j (st-substG g i s0)
subst-weakenT : (t : IND.Type (suc n)) (i : Fin (suc n)) (j : Fin (suc n)) (le : Data.Fin._≤_ j i) (s0 : IND.SType 0)
  → st-substT (weaken1'T (inject₁ j) t) (suc i) s0 ≡ weaken1'T j (st-substT t i s0)

subst-weakenS (gdd gst) i j le s0 = cong gdd (subst-weakenG gst i j le s0)
subst-weakenS (rec gst) i j le s0 = cong rec (subst-weakenG gst (suc i) (suc j) (s≤s le) s0)
subst-weakenS (var p x) zero zero le s0 = refl
subst-weakenS {suc n} (var p x) (suc i) zero le s0 = refl
subst-weakenS {suc n} (var p zero) (suc i) (suc j) le s0 = refl
subst-weakenS {suc n} (var p (suc x)) (suc i) (suc j) (s≤s le) s0 rewrite (weak-weakS j zero z≤n (st-substS (var p x) i s0))
  = cong (weaken1'S zero) (subst-weakenS (var p x) i j le s0)

subst-weakenG (transmit d t s) i j le s0 = cong₂ (transmit d) (subst-weakenT t i j le s0) (subst-weakenS s i j le s0)
subst-weakenG (choice d m alt) i j le s0 = cong (choice d m) (ext (λ m' → subst-weakenS (alt m') i j le s0 ))
subst-weakenG end i j le s0 = refl

subst-weakenT TUnit i j le s0 = refl
subst-weakenT TInt i j le s0 = refl
subst-weakenT (TPair t t₁) i j le s0 = cong₂ TPair (subst-weakenT t i j le s0) (subst-weakenT t₁ i j le s0)
subst-weakenT (TChan s) i j le s0 = cong TChan (subst-weakenS s i j le s0)

{-# TERMINATING #-}
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
  rewrite subst-weakenS (swap-polS i (var p x)) i zero z≤n (dualS ist) 
  = cong (weaken1'S zero) (subst-swap-dualS ((var p x)) i)

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

{-# TERMINATING #-}
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
  rewrite subst-weakenS (swap-polS (inject j) (var p x)) i zero z≤n ist
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
dual-recS' (var p zero) zero ist rewrite (dual-if-dual p ist) = refl
dual-recS' (var p (suc x)) zero ist = trivial-subst-var p x (dualS ist) (ist)
dual-recS' (var p zero) (suc i) ist = trivial-subst-var' p i (dualS ist) (ist) 
dual-recS' (var p (suc x)) (suc i) ist rewrite (subst-swap-dualS{ist = ist} (var p (suc x)) (suc i))
  = refl

----------------------------------------------------------------------

-- show that the dualS function is compatible with unfolding
-- that is
-- COI.dual ∘ ind2coi ≈ ind2coi ∘ IND.dual

{-# TERMINATING #-}
dual-lemmaS : (s : IND.SType (suc n)) (j : Fin (suc n)) (s0 : IND.SType 0)
  → st-substS (dualS s) j s0 ≡ dualS (st-substS s j s0)
dual-lemmaG : (g : IND.GType (suc n)) (j : Fin (suc n)) (s0 : IND.SType 0)
  → st-substG (dualG g) j s0 ≡ dualG (st-substG g j s0)

dual-lemmaS (gdd gst) j s0 = cong gdd (dual-lemmaG gst j s0)
dual-lemmaS (rec gst) j s0 rewrite (subst-swapG s0 (suc j) zero (dualG gst)) =
  let rst = dual-lemmaG gst (suc j) s0 in cong rec (cong (swap-polG zero) rst)
dual-lemmaS {n} (var POS zero) zero s0          = sym (dual-weakenS' n s0)
dual-lemmaS {n} (var NEG zero) zero s0 rewrite (sym (dual-weakenS' n s0)) | (sym (dual-invS (weakenS n s0))) = refl
dual-lemmaS {suc n} (var POS zero) (suc j) s0 = refl
dual-lemmaS {suc n} (var NEG zero) (suc j) s0 = refl
dual-lemmaS {suc n} (var POS (suc x)) zero s0 = refl
dual-lemmaS {suc n} (var NEG (suc x)) zero s0 = refl
dual-lemmaS {suc n} (var POS (suc x)) (suc j) s0 rewrite (dual-weakenS zero (st-substS (var POS x) j s0)) = cong (weaken1'S zero) (dual-lemmaS (var POS x) j s0)
dual-lemmaS {suc n} (var NEG (suc x)) (suc j) s0 rewrite (dual-weakenS zero (st-substS (var NEG x) j s0)) = cong (weaken1'S zero) (dual-lemmaS (var NEG x) j s0)

dual-lemmaG (transmit d t s) j s0 = cong₂ (transmit (dual-dir d)) refl (dual-lemmaS s j s0)
dual-lemmaG (choice d m alt) j s0 = cong (choice (dual-dir d) m) (ext (λ m' → dual-lemmaS (alt m') j s0))
dual-lemmaG end j s0 = refl

----------------------------------------------------------------------
-- main result
dual-compatibleS : (ist : IND.SType 0) →
  COI.dual (ind2coiS ist) ≈ ind2coiS (IND.dualS ist)
dual-compatibleG : (gst : IND.GType 0) →
  COI.dualF (ind2coiG gst) ≈' ind2coiG (IND.dualG gst)

Equiv.force (dual-compatibleS (gdd gst)) = dual-compatibleG gst
Equiv.force (dual-compatibleS (rec gst))
  rewrite (dual-recG' (dualG gst) zero (rec gst))
          | dual-lemmaG gst zero (rec gst) = dual-compatibleG (st-substG gst zero (rec gst)) 

dual-compatibleG (transmit d t s) = eq-transmit (dual-dir d) ≈ᵗ-refl (dual-compatibleS s)
dual-compatibleG (choice d m alt) = eq-choice (dual-dir d) (dual-compatibleS ∘ alt)
dual-compatibleG end = eq-end

