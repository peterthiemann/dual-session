{-# OPTIONS --rewriting #-}
module Auxiliary where

open import Data.Nat
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Fin.Properties

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Agda.Builtin.Equality.Rewrite

variable
  m n : ℕ

----------------------------------------------------------------------
-- auxiliaries for automatic rewriting

n+1=suc-n : n + 1 ≡ suc n
n+1=suc-n {zero} = refl
n+1=suc-n {suc n} = cong suc (n+1=suc-n {n})

{-# REWRITE n+1=suc-n #-}

n+0=n : n + 0 ≡ n
n+0=n {zero} = refl
n+0=n {suc n} = cong suc (n+0=n {n})

{-# REWRITE n+0=n #-}

inject+0-x=x : {x : Fin m} → inject+ 0 x ≡ x
inject+0-x=x {x = zero} = refl
inject+0-x=x {x = suc x} = cong suc inject+0-x=x

{-# REWRITE inject+0-x=x #-}

n+sucm : n + suc m ≡ suc (n + m)
n+sucm {zero} = refl
n+sucm {suc n} = cong suc n+sucm

{-# REWRITE n+sucm #-}

n=fromℕtoℕn : (toℕ (fromℕ n)) ≡ n
n=fromℕtoℕn {n} = toℕ-fromℕ n

{-# REWRITE n=fromℕtoℕn #-}

sucn∸suctoℕx≡n∸toℕx : {n : ℕ} {x : Fin n} → suc (n ∸ suc (toℕ x)) ≡ n ∸ (toℕ x)
sucn∸suctoℕx≡n∸toℕx {suc n} {zero} = refl
sucn∸suctoℕx≡n∸toℕx {suc n} {suc x} = sucn∸suctoℕx≡n∸toℕx {n}{x}

sym-sucn∸suctoℕx≡n∸toℕx : {n : ℕ} {x : Fin n} → n ∸ (toℕ x) ≡ suc (n ∸ suc (toℕ x))
sym-sucn∸suctoℕx≡n∸toℕx {suc n} {x} = sym (sucn∸suctoℕx≡n∸toℕx {suc n} {x})

----------------------------------------------------------------------
-- some more required properties on natural numbers and fin

toℕx≤n : {n : ℕ} {x : Fin n} → toℕ x ≤ n
toℕx≤n {suc n} {zero} = z≤n
toℕx≤n {suc n} {suc x} = s≤s toℕx≤n

toℕx≤n' : {n : ℕ} {x : Fin (suc n)} → toℕ x ≤ n
toℕx≤n' {zero} {zero} = z≤n
toℕx≤n' {suc n} {zero} = z≤n
toℕx≤n' {suc n} {suc x} = s≤s (toℕx≤n'{n}{x})

n∸x+x≡n : {n x : ℕ} → x ≤ n  → n ∸ x + x ≡ n
n∸x+x≡n {zero} {zero} le = refl
n∸x+x≡n {zero} {suc x} ()
n∸x+x≡n {suc n} {zero} le = refl
n∸x+x≡n {suc n} {suc x} (s≤s le) = cong suc (n∸x+x≡n le)

toℕx<n : {n : ℕ} {x : Fin n} → toℕ x < n
toℕx<n {suc n} {zero} = s≤s z≤n
toℕx<n {suc n} {suc x} = s≤s toℕx<n

n∸x≡suc[n∸sucx] : {n x : ℕ} → x < n → n ∸ x ≡ suc (n ∸ (suc x))
n∸x≡suc[n∸sucx] {suc n} {zero} le = refl
n∸x≡suc[n∸sucx] {suc n} {suc x} (s≤s le) = n∸x≡suc[n∸sucx] le

suc[n+x]≡n+sucx : {n x : ℕ} → suc (n + x) ≡ (n + suc x)
suc[n+x]≡n+sucx {zero} {x} = refl
suc[n+x]≡n+sucx {suc n} {x} = refl

suc[n∸sucx+x]≡n : {n x : ℕ} → x < n → suc (n ∸ (suc x) + x) ≡ n
suc[n∸sucx+x]≡n {suc n} {zero} le = refl
suc[n∸sucx+x]≡n {suc n} {suc x} (s≤s le) = cong suc (suc[n∸sucx+x]≡n {n} {x} le)

suc[n∸suc[toℕi]+toℕi]≡n : {n : ℕ} {i : Fin n} → suc (n ∸ (suc (toℕ i)) + toℕ i) ≡ n
suc[n∸suc[toℕi]+toℕi]≡n {suc n} {i} = suc[n∸sucx+x]≡n{suc n}{toℕ i} toℕx<n

{-# REWRITE suc[n∸suc[toℕi]+toℕi]≡n #-}

<suc : {n x : ℕ} → x < n → x < suc n
<suc {suc n} {zero} le = s≤s z≤n
<suc {suc n} {suc x} (s≤s le) = s≤s (<suc le)

