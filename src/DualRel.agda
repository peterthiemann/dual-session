{-# OPTIONS --rewriting --guardedness #-}
module DualRel where

open import Data.Fin
open import Data.Nat

open import Types.Direction
import Types.IND as IND

variable
  m : ℕ
  g g₁ g₂ : IND.GType 0
  s s₁ s₂ : IND.SType 0
  t : IND.Type 0

data _⊥P_ : Dir → Dir → Set where
  sr⊥ : SND ⊥P RCV
  rs⊥ : RCV ⊥P SND

data _⊥S_ : IND.SType 0 → IND.SType 0 → Set
data _⊥G_ : IND.GType 0 → IND.GType 0 → Set

data _⊥S_ where
  gdd⊥ : g₁ ⊥G g₂ →
    IND.gdd g₁ ⊥S IND.gdd g₂
  rec⊥L : ∀ {g₁ : IND.GType 1} →
    IND.st-substG g₁ zero (IND.rec g₁) ⊥G g₂ →
    IND.rec g₁ ⊥S IND.gdd g₂
  rec⊥R : ∀ {g₂ : IND.GType 1} →
    g₁ ⊥G IND.st-substG g₂ zero (IND.rec g₂) →
    IND.gdd g₁ ⊥S IND.rec g₂
  rec⊥B : ∀ {g₁ g₂ : IND.GType 1} →
    IND.st-substG g₁ zero (IND.rec g₁) ⊥G IND.st-substG g₂ zero (IND.rec g₂) →
    IND.rec g₁ ⊥S IND.rec g₂

data _⊥G_ where
  transmit⊥ : ∀ {t : IND.Type 0} → 
    d₁ ⊥P d₂ →
    s₁ ⊥S s₂ →
    IND.transmit d₁ t s₁ ⊥G IND.transmit d₂ t s₂
  choice⊥ : ∀ {alt₁ alt₂ : Fin m → IND.SType 0} →
    d₁ ⊥P d₂ →
    (∀ i → alt₁ i ⊥S alt₂ i) →
    IND.choice d₁ m alt₁ ⊥G IND.choice d₂ m alt₂
  end⊥ :
    IND.end ⊥G IND.end
