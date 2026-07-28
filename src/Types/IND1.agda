{-# OPTIONS --rewriting --guardedness #-}
module Types.IND1 where

open import Data.Nat using (ℕ; zero; suc; _+_; s≤s)
import Data.Nat.Properties as ℕₚ using (+-comm)
open import Data.Fin using (Fin; zero; suc; inject₁; _≤_)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import Types.Direction using (Dir; SND)
open import Auxiliary.Extensionality using (ext)

private
  variable
    m n : ℕ

----------------------------------------------------------------------
-- session type inductively with explicit rec
-- without polarized variables

mutual
  data Type n : Set where
    TUnit TInt : Type n
    TPair : (T₁ : Type n) (T₂ : Type n) → Type n
    TFun : (T₁ : Type n) (T₂ : Type n) → Type n
    TChan : (S : SType n) → Type n
  
  data SType n : Set where
    gdd : (G : GType n) → SType n
    rec : (G : GType (suc n) ) → SType n
    var : (x : Fin n) → SType n

  data GType n : Set where
    transmit : (d : Dir) (T : Type n) (S : SType n) → GType n
    choice : (d : Dir) (m : ℕ) (alt : Fin m → SType n) → GType n
    end : GType n
  
TType = Type

----------------------------------------------------------------------
-- renamings and substitutions

Ren : ℕ → ℕ → Set
Ren n m = Fin n → Fin m

Sub : ℕ → ℕ → Set
Sub n m = Fin n → SType m

liftRen : Ren n m → Ren (suc n) (suc m)
liftRen ρ zero = zero
liftRen ρ (suc x) = suc (ρ x)

renameS : Ren n m → SType n → SType m
renameG : Ren n m → GType n → GType m
renameT : Ren n m → TType n → TType m

renameS ρ (gdd gst) = gdd (renameG ρ gst)
renameS ρ (rec gst) = rec (renameG (liftRen ρ) gst)
renameS ρ (var x) = var (ρ x)

renameG ρ (transmit d t s) = transmit d (renameT ρ t) (renameS ρ s)
renameG ρ (choice d m alt) = choice d m (renameS ρ ∘ alt)
renameG ρ end = end

renameT ρ TUnit = TUnit
renameT ρ TInt = TInt
renameT ρ (TPair ty ty₁) = TPair (renameT ρ ty) (renameT ρ ty₁)
renameT ρ (TFun ty ty₁) = TFun (renameT ρ ty) (renameT ρ ty₁)
renameT ρ (TChan x) = TChan (renameS ρ x)

liftSub : Sub n m → Sub (suc n) (suc m)
liftSub σ zero = var zero
liftSub σ (suc x) = renameS suc (σ x)

substS : Sub n m → SType n → SType m
substG : Sub n m → GType n → GType m
substT : Sub n m → TType n → TType m

substS σ (gdd gst) = gdd (substG σ gst)
substS σ (rec gst) = rec (substG (liftSub σ) gst)
substS σ (var x) = σ x

substG σ (transmit d t s) = transmit d (substT σ t) (substS σ s)
substG σ (choice d m alt) = choice d m (substS σ ∘ alt)
substG σ end = end

substT σ TUnit = TUnit
substT σ TInt = TInt
substT σ (TPair ty ty₁) = TPair (substT σ ty) (substT σ ty₁)
substT σ (TFun ty ty₁) = TFun (substT σ ty) (substT σ ty₁)
substT σ (TChan x) = TChan (substS σ x)

----------------------------------------------------------------------
-- weakening as renaming

weakenRen : (n : ℕ) → Ren m (m + n)
weakenRen {zero} n ()
weakenRen {suc m} n = liftRen (weakenRen {m} n)

weakenS : (n : ℕ) → SType m → SType (m + n)
weakenG : (n : ℕ) → GType m → GType (m + n)
weakenT : (n : ℕ) → TType m → TType (m + n)

weakenS n s = renameS (weakenRen n) s
weakenG n g = renameG (weakenRen n) g
weakenT n t = renameT (weakenRen n) t

weaken1 : SType m → SType (suc m)
weaken1{m} stm with weakenS 1 stm
... | r rewrite ℕₚ.+-comm m 1 = r

module CheckWeaken where
  s0 : SType 0
  s0 = rec (transmit SND TUnit (var zero))
  s1 : SType 1
  s1 = rec (transmit SND TUnit (var zero))
  s2 : SType 2
  s2 = rec (transmit SND TUnit (var zero))

  check-weakenS1 : weakenS 1 s0 ≡ s1
  check-weakenS1 = cong rec (cong (transmit SND TUnit) refl)

  check-weakenS2 : weakenS 2 s0 ≡ s2
  check-weakenS2 = cong rec (cong (transmit SND TUnit) refl)

insertRen : Fin (suc n) → Ren n (suc n)
insertRen zero = suc
insertRen {suc n} (suc i) = liftRen (insertRen {n} i)

weaken1'N : Fin (suc n) → Fin n → Fin (suc n)
weaken1'N = insertRen

weaken1'S : Fin (suc n) → SType n → SType (suc n)
weaken1'G : Fin (suc n) → GType n → GType (suc n)
weaken1'T : Fin (suc n) → TType n → TType (suc n)

weaken1'S i s = renameS (weaken1'N i) s
weaken1'G i g = renameG (weaken1'N i) g
weaken1'T i t = renameT (weaken1'N i) t

weaken1S : SType n → SType (suc n)
weaken1G : GType n → GType (suc n)
weaken1T : Type n → Type (suc n)

weaken1S = weaken1'S zero
weaken1G = weaken1'G zero
weaken1T = weaken1'T zero

module CheckWeaken1' where
  sxy : ∀ n → Fin (suc n) → SType n
  sxy n x = rec (transmit SND TUnit (var x))

  s00 : SType 0
  s00 = sxy 0 zero
  s10 : SType 1
  s10 = sxy 1 zero
  s11 : SType 1
  s11 = sxy 1 (suc zero)
  s22 : SType 2
  s22 = sxy 2 (suc (suc zero))

  check-weaken-s01 : weaken1'S zero s00 ≡ s10
  check-weaken-s01 = refl

  check-weaken-s1-s2 : weaken1'S zero s11 ≡ s22
  check-weaken-s1-s2 = refl

  check-weaken-s21 : weaken1'S (suc zero) (sxy 2 (suc zero)) ≡ sxy 3 (suc zero)
  check-weaken-s21 = refl
--------------------------------------------------------------------

weak-weakN : (i : Fin (suc n)) (j : Fin (suc n)) (le : j ≤ i) (x : Fin n)
  → weaken1'N (suc i) (weaken1'N j x) ≡ weaken1'N (inject₁ j) (weaken1'N i x)
weak-weakG : (i : Fin (suc n)) (j : Fin (suc n)) (le : j ≤ i) (g : GType n)
  → weaken1'G (suc i) (weaken1'G j g) ≡ weaken1'G (inject₁ j) (weaken1'G i g)
weak-weakS : (i : Fin (suc n)) (j : Fin (suc n)) (le : j ≤ i) (s : SType n)
  → weaken1'S (suc i) (weaken1'S j s) ≡ weaken1'S (inject₁ j) (weaken1'S i s)
weak-weakT : (i : Fin (suc n)) (j : Fin (suc n)) (le : j ≤ i) (t : Type n)
  → weaken1'T (suc i) (weaken1'T j t) ≡ weaken1'T (inject₁ j) (weaken1'T i t)

weak-weakN zero zero le x                              = refl
weak-weakN (suc i) zero le x                         = refl
weak-weakN (suc i) (suc j) (s≤s le) zero           = refl
weak-weakN{suc n} (suc i) (suc j) (s≤s le) (suc x) = cong suc (weak-weakN i j le x) 

weak-weakG i j le (transmit d t s) = cong₂ (transmit d) (weak-weakT i j le t) (weak-weakS i j le s)
weak-weakG i j le (choice d m alt) = cong (choice d m) (ext (weak-weakS i j le ∘ alt))
weak-weakG i j le end              = refl

weak-weakS i j le (gdd gst) = cong gdd (weak-weakG i j le gst)
weak-weakS i j le (rec gst) = cong rec (weak-weakG (suc i) (suc j) (s≤s le) gst)
weak-weakS i j le (var x) = cong (var) (weak-weakN i j le x)

weak-weakT i j le TUnit        = refl
weak-weakT i j le TInt         = refl
weak-weakT i j le (TPair t t₁) = cong₂ TPair (weak-weakT i j le t) (weak-weakT i j le t₁)
weak-weakT i j le (TFun t t₁)  = cong₂ TFun (weak-weakT i j le t) (weak-weakT i j le t₁)
weak-weakT i j le (TChan s)    = cong TChan (weak-weakS i j le s)


weaken1-weakenN : (m : ℕ) (j : Fin (suc n)) (x : Fin n)
  → weakenRen m (weaken1'N j x) ≡ weaken1'N (weakenRen m j) (weakenRen m x)
weaken1-weakenN m zero zero           = refl
weaken1-weakenN m zero (suc x)      = refl
weaken1-weakenN m (suc j) zero      = refl
weaken1-weakenN m (suc j) (suc x) = cong suc (weaken1-weakenN m j x)

weaken1-weakenS : (m : ℕ) (j : Fin (suc n)) (s : SType n)
  → weakenS m (weaken1'S j s) ≡ weaken1'S (weakenRen m j) (weakenS m s) 
weaken1-weakenG : (m : ℕ) (j : Fin (suc n)) (g : GType n)
  → weakenG m (weaken1'G j g) ≡ weaken1'G (weakenRen m j) (weakenG m g)
weaken1-weakenT : (m : ℕ) (j : Fin (suc n)) (t : Type n)
  → weakenT m (weaken1'T j t) ≡ weaken1'T (weakenRen m j) (weakenT m t)
weaken1-weakenS m j (gdd gst) = cong gdd (weaken1-weakenG m j gst)
weaken1-weakenS m j (rec gst) = cong rec (weaken1-weakenG m (suc j) gst)
weaken1-weakenS m zero (var zero)      = refl
weaken1-weakenS m zero (var (suc x)) = refl
weaken1-weakenS {suc n} m (suc j) (var zero)      = refl
weaken1-weakenS {suc n} m (suc j) (var (suc x)) = cong (var) (cong suc (weaken1-weakenN m j x))

weaken1-weakenG m j (transmit d t s)  = cong₂ (transmit d) (weaken1-weakenT m j t) (weaken1-weakenS m j s)
weaken1-weakenG m j (choice d m₁ alt) = cong (choice d m₁) (ext (weaken1-weakenS m j ∘ alt))
weaken1-weakenG m j end = refl

weaken1-weakenT m j TUnit = refl
weaken1-weakenT m j TInt = refl
weaken1-weakenT m j (TPair t t₁) = cong₂ TPair (weaken1-weakenT m j t) (weaken1-weakenT m j t₁)
weaken1-weakenT m j (TFun t t₁) = cong₂ TFun (weaken1-weakenT m j t) (weaken1-weakenT m j t₁)
weaken1-weakenT m j (TChan x) = cong TChan (weaken1-weakenS m j x)


--------------------------------------------------------------------
-- single closed substitution as a simultaneous substitution

singleSub0 : Fin (suc n) → SType 0 → Sub (suc n) n
singleSub0 {n} zero st0 zero = weakenS n st0
singleSub0 {suc n} zero st0 (suc x) = var x
singleSub0 {suc n} (suc i) st0 = liftSub (singleSub0 {n} i st0)

st-substS : SType (suc n) → Fin (suc n) → SType 0 → SType n
st-substG : GType (suc n) → Fin (suc n) → SType 0 → GType n
st-substT : Type (suc n) → Fin (suc n) → SType 0 → Type n

st-substS s i st0 = substS (singleSub0 i st0) s
st-substG g i st0 = substG (singleSub0 i st0) g
st-substT t i st0 = substT (singleSub0 i st0) t

--------------------------------------------------------------------

trivial-subst-var : (x : Fin n) (ist₁ ist₂ : SType 0)
  → st-substS (var (suc x)) zero ist₁ ≡ st-substS (var (suc x)) zero ist₂
trivial-subst-var zero ist1 ist2 = refl
trivial-subst-var (suc x) ist1 ist2 = refl

trivial-subst-var' : (i : Fin n) (ist₁ ist₂ : SType 0)
  → st-substS (var zero) (suc i) ist₁ ≡ st-substS (var zero) (suc i) ist₂
trivial-subst-var' zero ist1 ist2 = refl
trivial-subst-var' (suc x) ist1 ist2 = refl

--------------------------------------------------------------------
-- equivalence
variable
  t t₁ t₂ t₁' t₂' : Type n
  s s₁ s₂ : SType n
  g g₁ g₂ : GType n

unfold : SType 0 → GType 0
unfold (gdd gst) = gst
unfold (rec gst) = st-substG gst zero (rec gst)

-- type equivalence
data EquivT (R : SType n → SType n → Set) : Type n → Type n → Set where
  eq-unit : EquivT R TUnit TUnit
  eq-int  : EquivT R TInt TInt
  eq-pair : EquivT R t₁ t₁' → EquivT R t₂ t₂' → EquivT R (TPair t₁ t₂) (TPair t₁' t₂')
  eq-fun  : EquivT R t₁ t₁' → EquivT R t₂ t₂' → EquivT R (TFun t₁ t₂) (TFun t₁' t₂')
  eq-chan : R s₁ s₂ → EquivT R (TChan s₁) (TChan s₂)

-- session type equivalence
data EquivG (R : SType n → SType n → Set) : GType n → GType n → Set where
  eq-transmit : (d : Dir) → EquivT R t₁ t₂ → R s₁ s₂ → EquivG R (transmit d t₁ s₁) (transmit d t₂ s₂)
  eq-choice : ∀ {alt alt'} → (d : Dir) → ((i : Fin m) → R (alt i) (alt' i)) → EquivG R (choice d m alt) (choice d m alt')
  eq-end : EquivG R end end

record Equiv (s₁ s₂ : SType 0) : Set where
  coinductive
  field force : EquivG Equiv (unfold s₁) (unfold s₂)

open Equiv

_≈_ = Equiv
_≈'_ = EquivG Equiv
_≈ᵗ_ = EquivT Equiv

-- reflexive

≈-refl : s ≈ s
≈'-refl : g ≈' g
≈ᵗ-refl : t ≈ᵗ t

force (≈-refl {s}) = ≈'-refl

≈'-refl {transmit d t s} = eq-transmit d ≈ᵗ-refl ≈-refl
≈'-refl {choice d m alt} = eq-choice d (λ i → ≈-refl)
≈'-refl {end} = eq-end

≈ᵗ-refl {TUnit} = eq-unit
≈ᵗ-refl {TInt} = eq-int
≈ᵗ-refl {TPair t t₁} = eq-pair ≈ᵗ-refl ≈ᵗ-refl
≈ᵗ-refl {TFun t t₁} = eq-fun ≈ᵗ-refl ≈ᵗ-refl
≈ᵗ-refl {TChan x} = eq-chan ≈-refl

-- symmetric

≈-symm : s₁ ≈ s₂ → s₂ ≈ s₁
≈'-symm : g₁ ≈' g₂ → g₂ ≈' g₁
≈ᵗ-symm : t₁ ≈ᵗ t₂ → t₂ ≈ᵗ t₁

force (≈-symm s₁≈s₂) = ≈'-symm (force s₁≈s₂)

≈'-symm (eq-transmit d x x₁) = eq-transmit d (≈ᵗ-symm x) (≈-symm x₁)
≈'-symm (eq-choice d x) = eq-choice d (≈-symm ∘ x)
≈'-symm eq-end = eq-end

≈ᵗ-symm eq-unit = eq-unit
≈ᵗ-symm eq-int = eq-int
≈ᵗ-symm (eq-pair t₁≈ᵗt₂ t₁≈ᵗt₃) = eq-pair (≈ᵗ-symm t₁≈ᵗt₂) (≈ᵗ-symm t₁≈ᵗt₃)
≈ᵗ-symm (eq-fun t₁≈ᵗt₂ t₁≈ᵗt₃) = eq-fun (≈ᵗ-symm t₁≈ᵗt₂) (≈ᵗ-symm t₁≈ᵗt₃)
≈ᵗ-symm (eq-chan x) = eq-chan (≈-symm x)
