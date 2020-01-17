module Max where

open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.Nat hiding (_≤_)
open import Function using (_∘_)

open import Relation.Nullary

variable
  n : ℕ

-- from https://github.com/zmthy/recursive-types/tree/ftfjp16
-- RecursiveTypes.Inductive.Type
-- adapted to use "variable"


-- A proposition that the indexed number is the largest it can be, i.e. one less
-- than its exclusive upper bound.
data Max : Fin n → Set where
  max : Max {suc n} (fromℕ n)

-- A lemma on Max: if a number is max, then one less than that number with a
-- simultaneously lowered upper bound is also max.
max-pre : {x : Fin (suc n)} → Max (suc x) → Max x
max-pre max = max

-- A lemma on Max: if a number is max, then one more than that number with a
-- simultaneously increased upper bound is also max.
max-suc : {x : Fin n} → Max x → Max (suc x)
max-suc max = max

-- Given a proof that a number is not max, reduce its lower bound by one,
-- keeping the value of the number the same.
reduce : {x : Fin (suc n)} → ¬ Max x → Fin n
reduce {zero}  {zero}   ¬p = ⊥-elim (¬p max)
reduce {zero}  {suc ()} ¬p
reduce {suc n} {zero}   ¬p = zero
reduce {suc n} {suc x}  ¬p = suc (reduce {x = x} (¬p ∘ max-suc))

-- Max is a decidable proposition: just compare the number value to the value of
-- the upper bound.
max? : (x : Fin n) → Dec (Max x)
max? {zero}        ()
max? {suc zero}    zero     = yes max
max? {suc zero}    (suc ())
max? {suc (suc n)} zero     = no (λ ())
max? {suc (suc n)} (suc x)  with max? x
max? {suc (suc n)} (suc .(fromℕ n)) | yes max = yes max
max? {suc (suc n)} (suc x)          | no ¬p = no (¬p ∘ max-pre)

-- The reduce function preserves ≤.
reduce₁ : ∀ {m} {x : Fin n} (¬p : ¬ Max (suc x))
          → m ≤ x → suc m ≤ inject₁ (reduce ¬p)
reduce₁ {m = zero} ¬p₁ z≤n = s≤s z≤n
reduce₁ {m = suc m} {zero} ¬p ()
reduce₁ {m = suc m₁} {suc x₁} ¬p₁ (s≤s q₁) =
  s≤s (reduce₁ (λ z → ¬p₁ (max-suc z)) q₁)

-- Injection is compatible with ordering.
inject-≤ : {i j : Fin n} → inject₁ i ≤ inject₁ j → i ≤ j
inject-≤ {i = 0F} {0F} z≤n = z≤n
inject-≤ {i = 0F} {suc j} z≤n = z≤n
inject-≤ {i = suc i} {0F} ()
inject-≤ {i = suc i} {suc j} (s≤s ii≤ij) = s≤s (inject-≤ ii≤ij)

-- Technical lemma about reduce.
lemma-reduce : {i j : Fin (suc n)} →
  (i≤j : inject₁ i ≤ inject₁ j) → (¬p  : ¬ Max j) → i ≤ inject₁ (reduce ¬p)
lemma-reduce {i = 0F} i≤j ¬p = z≤n
lemma-reduce {i = suc i} {suc j} (s≤s i≤j) ¬p = reduce₁ ¬p (inject-≤ i≤j)

-- A lemma on ≤: if x ≤ y, then x ≤ suc y.
suc-≤ : {x y : Fin n} → x ≤ y → inject₁ x ≤ suc y
suc-≤ {x = zero} z≤n = z≤n
suc-≤ {x = suc x} {zero} ()
suc-≤ {x = suc x} {suc y} (s≤s p) = s≤s (suc-≤ p)


-- A lemma on ≤: if suc x ≤ y, then x ≤ y.
pred-≤ : {x y : Fin n} → suc x ≤ inject₁ y → inject₁ x ≤ inject₁ y
pred-≤ {y = zero} ()
pred-≤ {y = suc x} (s≤s p) = suc-≤ p

-- A lemma on ≤: if x ≤ y, then for any z < x, z ≤ y.
trans-< : {x y : Fin n} {z : Fin′ x} → x ≤ y → inject z ≤ y
trans-< {x = zero} {z = ()} p
trans-< {x = suc x} {zero} ()
trans-< {x = suc x} {suc y} {zero} (s≤s p) = z≤n
trans-< {x = suc x} {suc y} {suc z} (s≤s p) = s≤s (trans-< p)

