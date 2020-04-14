module Auxiliary.Extensionality where

open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  ext : {A : Set}{B : A → Set}{f : (x : A) → B x} {g : (x : A) → B x} →
    (∀ x → f x ≡ g x) → f ≡ g
