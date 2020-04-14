module Types.Tail where

open import Data.Nat
open import Data.Fin
open import Function using (_∘_)
open import Types.Direction

-- session types restricted to tail recursion
-- can be recognized by type of TChan constructor

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

private
  variable
    n : ℕ

-- naive definition of duality for tail recursive session types
-- message types are ignored as they are closed

dualS : SType n → SType n
dualG : GType n → GType n

dualS (gdd g) = gdd (dualG g)
dualS (rec g) = rec (dualG g)
dualS (var x) = var x

dualG (transmit d t s) = transmit (dual-dir d) t (dualS s)
dualG (choice d m alt) = choice (dual-dir d) m (dualS ∘ alt)
dualG end = end
