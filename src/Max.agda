module Max where

open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat
open import Function using (_∘_)

open import Relation.Nullary

-- from https://github.com/zmthy/recursive-types/tree/ftfjp16
-- RecursiveTypes.Inductive.Type


-- A proposition that the indexed number is the largest it can be, i.e. one less
-- than its exclusive upper bound.
data Max : ∀ {n} → Fin n → Set where
  max : ∀ {n} → Max {suc n} (fromℕ n)

-- A lemma on Max: if a number is max, then one less than that number with a
-- simultaneously lowered upper bound is also max.
max-pre : ∀ {n} {x : Fin (suc n)} → Max (suc x) → Max x
max-pre max = max

-- A lemma on Max: if a number is max, then one more than that number with a
-- simultaneously increased upper bound is also max.
max-suc : ∀ {n} {x : Fin n} → Max x → Max (suc x)
max-suc max = max

-- Given a proof that a number is not max, reduce its lower bound by one,
-- keeping the value of the number the same.
reduce : ∀ {n} {x : Fin (suc n)} → ¬ Max x → Fin n
reduce {zero}  {zero}   ¬p = ⊥-elim (¬p max)
reduce {zero}  {suc ()} ¬p
reduce {suc n} {zero}   ¬p = zero
reduce {suc n} {suc x}  ¬p = suc (reduce {x = x} (¬p ∘ max-suc))

-- Max is a decidable proposition: just compare the number value to the value of
-- the upper bound.
max? : ∀ {n} (x : Fin n) → Dec (Max x)
max? {zero}        ()
max? {suc zero}    zero     = yes max
max? {suc zero}    (suc ())
max? {suc (suc n)} zero     = no (λ ())
max? {suc (suc n)} (suc x)  with max? x
max? {suc (suc n)} (suc .(fromℕ n)) | yes max = yes max
max? {suc (suc n)} (suc x)          | no ¬p = no (¬p ∘ max-pre)
