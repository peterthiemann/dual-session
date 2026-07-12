{-# OPTIONS --rewriting --guardedness #-}
module Examples where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; punchOut) renaming (_≟_ to _≟Fin_)
import Data.Nat as Nat
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (yes; no)

open import Types.Direction
import Types.IND1 as IND
import Types.Tail1 as Tail
import MessageClosure as MC
import DualStopAtMu as Stop

private
  variable
    n : Nat.ℕ

----------------------------------------------------------------------
-- Message-closure examples extracted from the legacy Krause development.

send-self : IND.SType 0
send-self =
  IND.rec (IND.transmit SND (IND.TChan (IND.var zero)) (IND.var zero))

send-self-closure :
  MC.mclosureS send-self ≡
  Tail.rec (Tail.transmit SND (Tail.TChan send-self) (Tail.var zero))
send-self-closure = refl

send-self-twice : IND.SType 0
send-self-twice =
  IND.rec
    (IND.transmit SND (IND.TChan (IND.var zero))
      (IND.gdd (IND.transmit SND (IND.TChan (IND.var zero)) (IND.var zero))))

send-self-twice-closure :
  MC.mclosureS send-self-twice ≡
  Tail.rec
    (Tail.transmit SND (Tail.TChan send-self-twice)
      (Tail.gdd (Tail.transmit SND (Tail.TChan send-self-twice) (Tail.var zero))))
send-self-twice-closure = refl

nested-self : IND.SType 0
nested-self =
  IND.rec
    (IND.transmit SND (IND.TChan (IND.var zero))
      (IND.rec (IND.transmit SND (IND.TChan (IND.var zero)) (IND.var zero))))

nested-self-closure :
  MC.mclosureS nested-self ≡
  Tail.rec
    (Tail.transmit SND (Tail.TChan nested-self)
      (Tail.rec (Tail.transmit SND (Tail.TChan send-self) (Tail.var zero))))
nested-self-closure = refl

----------------------------------------------------------------------
-- Stopped-duality examples extracted from the stopped-duality branch.

stopped-send-end :
  Stop.dualS Stop.send-end ≡ IND.gdd (IND.transmit RCV IND.TInt (IND.gdd IND.end))
stopped-send-end = Stop.send-end-dual

stopped-offer-two :
  Stop.dualS Stop.offer-two ≡
  IND.gdd (IND.choice SND 2 (Stop.dualS ∘ Stop.offer-two-alt))
stopped-offer-two = Stop.offer-two-dual

stopped-bh :
  Stop.dualS Stop.bh-shape ≡
  Stop.dualS (IND.rec (IND.transmit RCV (IND.TChan (IND.var zero)) (IND.var zero)))
stopped-bh = Stop.bh-stops-at-μ

stopped-bh-body :
  Stop.dualG {n = Nat.suc Nat.zero}
    (IND.transmit RCV (IND.TChan (IND.var zero)) (IND.var zero)) ≡
  IND.transmit SND (IND.TChan (IND.var zero)) (Stop.dualS {n = Nat.suc Nat.zero} (IND.var zero))
stopped-bh-body = Stop.bh-body-dual

----------------------------------------------------------------------
-- Counterexample extracted from the legacy DualSubst development.

module SubstitutionDualCounterexample where

  singleSub : Fin (Nat.suc n) → IND.SType n → IND.Sub (Nat.suc n) n
  singleSub i s x with i ≟Fin x
  ... | yes refl = s
  ... | no i≢x = IND.var (punchOut i≢x)

  subst1S : Fin (Nat.suc n) → IND.SType n → IND.SType (Nat.suc n) → IND.SType n
  subst1S i s = IND.substS (singleSub i s)

  apply-substT : (IND.SType n → IND.SType n) → IND.TType n → IND.TType n
  apply-substT σ IND.TUnit = IND.TUnit
  apply-substT σ IND.TInt = IND.TInt
  apply-substT σ (IND.TPair T T₁) = IND.TPair (apply-substT σ T) (apply-substT σ T₁)
  apply-substT σ (IND.TChan S) = IND.TChan (σ S)

  dualG : IND.GType n → (IND.SType n → IND.SType n) → IND.GType n
  dualS : IND.SType n → (IND.SType n → IND.SType n) → IND.SType n

  dualS (IND.gdd G) σ = IND.gdd (dualG G σ)
  dualS (IND.rec G) σ =
    IND.rec (dualG G (IND.weaken1S ∘ σ ∘ subst1S zero (IND.rec G)))
  dualS (IND.var x) σ = IND.var x

  dualG (IND.transmit d T S) σ =
    IND.transmit (dual-dir d) (apply-substT σ T) (dualS S σ)
  dualG (IND.choice d m alt) σ =
    IND.choice (dual-dir d) m (λ i → dualS (alt i) σ)
  dualG IND.end σ =
    IND.end

  dual₀S : IND.SType n → IND.SType n
  dual₀S S = dualS S id

  bh : IND.SType 0
  bh =
    IND.rec (IND.transmit RCV (IND.TChan (IND.var zero)) (IND.var zero))

  bh-dual :
    dual₀S bh ≡ IND.rec (IND.transmit SND (IND.TChan (IND.weaken1S bh)) (IND.var zero))
  bh-dual = refl

  bh-dual-dual :
    dual₀S (dual₀S bh) ≡ IND.rec (IND.transmit RCV (IND.TChan (IND.weaken1S bh)) (IND.var zero))
  bh-dual-dual = refl

  payload0 : IND.SType 0 → IND.SType 1
  payload0 (IND.rec (IND.transmit d (IND.TChan S) k)) = S
  payload0 _ = IND.var zero

  is-recS : IND.SType n → Bool
  is-recS (IND.rec G) = true
  is-recS _ = false

  true≢false : true ≢ false
  true≢false ()

  bh-not-involutive : dual₀S (dual₀S bh) ≢ bh
  bh-not-involutive eq = true≢false (cong is-recS (cong payload0 eq))
