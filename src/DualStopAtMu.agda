{-# OPTIONS --rewriting --guardedness #-}
module DualStopAtMu where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

open import Types.Direction
open import Types.IND1
import DualTail1 as DT
import Types.COI as COI

private
  variable
    n m : ℕ
    T : Type n
    S : SType n
    G : GType n
    alt : Fin m → SType n

-- A duality operation that is intentionally opaque at recursive binders.
--
-- The rewrite rules below say how duality behaves after a non-recursive
-- session head has been exposed.  There is deliberately no rule for
--   dualS (rec G)
-- or
--   dualS (var x)
-- so a μ-boundary remains a boundary for this operation.
postulate
  dualS : {n : ℕ} → SType n → SType n
  dualG : {n : ℕ} → GType n → GType n

  dual-gdd :
    {n : ℕ} {G : GType n} →
    dualS (gdd G) ≡ gdd (dualG G)

  dual-transmit :
    {n : ℕ} {d : Dir} {T : Type n} {S : SType n} →
    dualG (transmit d T S) ≡ transmit (dual-dir d) T (dualS S)

  dual-choice :
    {n m : ℕ} {d : Dir} {alt : Fin m → SType n} →
    dualG (choice d m alt) ≡ choice (dual-dir d) m (dualS ∘ alt)

  dual-end :
    {n : ℕ} →
    dualG {n = n} (end {n = n}) ≡ end {n = n}

{-# REWRITE dual-gdd dual-transmit dual-choice dual-end #-}

----------------------------------------------------------------------
-- Small exploration examples

send-end : SType 0
send-end = gdd (transmit SND TInt (gdd end))

send-end-dual :
  dualS send-end ≡ gdd (transmit RCV TInt (gdd end))
send-end-dual = refl

offer-two-alt : Fin 2 → SType 0
offer-two-alt = λ where
  zero → gdd end
  (suc zero) → send-end

offer-two : SType 0
offer-two = gdd (choice RCV 2 offer-two-alt)

offer-two-dual :
  dualS offer-two ≡ gdd (choice SND 2 (dualS ∘ offer-two-alt))
offer-two-dual = refl

offer-two-dual-zero :
  (dualS ∘ offer-two-alt) zero ≡ gdd end
offer-two-dual-zero = refl

offer-two-dual-one :
  (dualS ∘ offer-two-alt) (suc zero) ≡ gdd (transmit RCV TInt (gdd end))
offer-two-dual-one = refl

-- The Bernardi-Hennessy counterexample shape, μX.?X.X.
-- Since the dual operation has no rewrite rule for rec, this expression
-- does not turn into μX.!?.  It stays headed by the opaque dualS.
bh-shape : SType 0
bh-shape = rec (transmit RCV (TChan (var zero)) (var zero))

bh-stops-at-μ :
  dualS bh-shape ≡ dualS (rec (transmit RCV (TChan (var zero)) (var zero)))
bh-stops-at-μ = refl

-- If the body is exposed explicitly, the communication constructor can still
-- be dualized, but variables remain opaque as well.
bh-body-dual :
  dualG {n = suc zero} (transmit RCV (TChan (var zero)) (var zero)) ≡
  transmit SND (TChan (var zero)) (dualS {n = suc zero} (var zero))
bh-body-dual = refl

-- This is the local involution shape for a communication head.  It is not a
-- global involution theorem because recursive boundaries remain uninterpreted.
dual-transmit-twice :
  dualG (dualG (transmit d T S)) ≡ transmit d T (dualS (dualS S))
dual-transmit-twice {d = d} rewrite dual-dir-inv d = refl

----------------------------------------------------------------------
-- Ground-truth connection

-- The existing stack-based embedding interprets recursive syntax as a
-- coinductive tree in COI.  Recursive nodes and variables are handled by
-- unfolding them once in the stack semantics.
--
-- The tempting proof is to unfold rec/var with COI transitivity and then use a
-- congruence lemma for COI.dual.  That proof is mathematically fine, but the
-- recursive call is hidden under transitivity, so Agda's guardedness checker
-- does not accept it without a termination escape hatch.
--
-- Instead, we expose the exact force equations that the stopped syntactic
-- dual must satisfy after the stack semantics performs one unfolding step.
-- These rules do not make dualS compute on rec or var syntactically; they only
-- say what the first COI layer of the interpreted stopped dual is.
postulate
  dual-rec-force :
    {n : ℕ} {σ : DT.Stack {GType} n} {G : GType (suc n)} →
    COI.SType.force (DT.ind2coiS σ (dualS (rec G))) ≡
    COI.SType.force (DT.ind2coiS (DT.⟪ σ , G ⟫) (dualS (gdd G)))

  dual-var-force :
    {n : ℕ} {σ : DT.Stack {GType} n} {x : Fin n} →
    let entry = DT.get x σ in
    COI.SType.force (DT.ind2coiS σ (dualS (var x))) ≡
    COI.SType.force
      (DT.ind2coiS (DT.⟪ proj₁ (proj₂ entry) , proj₂ (proj₂ entry) ⟫)
                   (dualS (gdd (proj₂ (proj₂ entry)))))

{-# REWRITE dual-rec-force dual-var-force #-}

groundS :
  (σ : DT.Stack {GType} n) (S : SType n) →
  COI.dual (DT.ind2coiS σ S) COI.≈ DT.ind2coiS σ (dualS S)
groundG :
  (σ : DT.Stack {GType} n) (G : GType n) →
  COI.dualF (DT.ind2coiG σ G) COI.≈' DT.ind2coiG σ (dualG G)

COI.Equiv.force (groundS σ (gdd G)) =
  groundG σ G
COI.Equiv.force (groundS σ (rec G)) =
  groundG (DT.⟪ σ , G ⟫) G
COI.Equiv.force (groundS (DT.⟪ σ , G ⟫) (var zero)) =
  groundG (DT.⟪ σ , G ⟫) G
COI.Equiv.force (groundS (DT.⟪ σ , G ⟫) (var (suc x))) =
  COI.Equiv.force (groundS σ (var x))

groundG σ (transmit d T S) =
  COI.eq-transmit (dual-dir d) COI.≈ᵗ-refl (groundS σ S)
groundG σ (choice d m alt) =
  COI.eq-choice (dual-dir d) (groundS σ ∘ alt)
groundG σ end =
  COI.eq-end

ground :
  (S : SType 0) →
  COI.dual (DT.ind2coiS DT.ε S) COI.≈ DT.ind2coiS DT.ε (dualS S)
ground = groundS DT.ε
