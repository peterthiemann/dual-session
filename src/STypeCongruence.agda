module STypeCongruence where

open import Data.Fin

open import Duality

open import Direction

open COI

-- holes for session types

mutual
  data TypeH : Set where
      TPair-l : TypeH → (T₂ : Type) → TypeH
      TPair-r : (T₁ : Type) → TypeH → TypeH
      TChan   : (sh : STypeH) → TypeH

  data STypeH : Set where
    hole : STypeH
    transmit-s : (d : Dir) (T : Type) (sh : STypeH) → STypeH
    transmit-t : (d : Dir) (th : TypeH) (S : SType) → STypeH

-- apply a hole to a session type

apply-hole-T : TypeH → SType → Type
apply-hole-S : STypeH → SType → SType

apply-hole-T (TPair-l th T₂) S = TPair (apply-hole-T th S) T₂
apply-hole-T (TPair-r T₁ th) S = TPair T₁ (apply-hole-T th S)
apply-hole-T (TChan sh) S = TChan (apply-hole-S sh S)

apply-hole-S hole S = S
apply-hole-S (transmit-s d T sh) S = delay (transmit d T (apply-hole-S sh S))
apply-hole-S (transmit-t d th S₁) S = delay (transmit d (apply-hole-T th S) S₁)

-- test congruences

≈-cong-transmit : ∀ {d t S₁ S₂} → S₁ ≈ S₂ → transmit d t S₁ ≈' transmit d t S₂
≈-cong-transmit S1≈S2 = eq-transmit _ ≈ᵗ-refl S1≈S2

≈-cong-transmit-t : ∀ {d T₁ T₂ S} → T₁ ≈ᵗ T₂ → transmit d T₁ S ≈' transmit d T₂ S
≈-cong-transmit-t T1≈T2 = eq-transmit _ T1≈T2 ≈-refl

≈-cong-choice : ∀ {d m alt₁ alt₂} → ((i : Fin m) → alt₁ i ≈ alt₂ i) → choice d m alt₁ ≈' choice d m alt₂
≈-cong-choice f = eq-choice _ f

-- full congruences

≈-cong-hole-S : ∀ {sh S₁ S₂} → S₁ ≈ S₂ → apply-hole-S sh S₁ ≈ apply-hole-S sh S₂
≈-cong-hole-T : ∀ {th S₁ S₂} → S₁ ≈ S₂ → apply-hole-T th S₁ ≈ᵗ apply-hole-T th S₂

≈-cong-hole-S {hole} S1≈S2 = S1≈S2
≈-cong-hole-S {transmit-s d T sh} S1≈S2 =
  record { force = ≈-cong-transmit (≈-cong-hole-S S1≈S2 ) }
≈-cong-hole-S {transmit-t d th S} S1≈S2 =
  record { force = ≈-cong-transmit-t (≈-cong-hole-T S1≈S2) }

≈-cong-hole-T {TPair-l th T₂} S1≈S2 = eq-pair (≈-cong-hole-T S1≈S2) ≈ᵗ-refl
≈-cong-hole-T {TPair-r T₁ th} S1≈S2 = eq-pair ≈ᵗ-refl (≈-cong-hole-T S1≈S2)
≈-cong-hole-T {TChan sh} S1≈S2 = eq-chan (≈-cong-hole-S S1≈S2)
