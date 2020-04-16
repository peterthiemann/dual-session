{-# OPTIONS --rewriting #-}
module MessageClosureProperties where

open import Data.Nat using (ℕ; zero ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; sym; refl)

open import Auxiliary.Extensionality
open import Auxiliary.RewriteLemmas

import Types.COI as COI
import Types.IND1 as IND
import Types.Tail1 as Tail
import Duality as DI
import DualTail1 as DT
import MessageClosure as MC

open COI using (_≈_; _≈'_; _≈ᵗ_)
open DT using (ε)

private
  variable
    n : ℕ

----------------------------------------------------------------------

var=shift-var : (i : Fin (suc n)) → IND.var i ≡ MC.shift{m = n}{n = 0} IND.var i
var=shift-var zero = refl
var=shift-var (suc i) = refl

apply-id-S : (S : IND.SType n) → MC.applyS{n = 0} IND.var S ≡ S
apply-id-G : (G : IND.GType n) → MC.applyG{n = 0} IND.var G ≡ G
apply-id-T : (T : IND.TType n) → MC.applyT{n = 0} IND.var T ≡ T

apply-id-S (IND.gdd G) = cong IND.gdd (apply-id-G G)
apply-id-S{n} (IND.rec G) rewrite sym (ext (var=shift-var{n})) = cong IND.rec (apply-id-G G)
apply-id-S (IND.var x) = refl

apply-id-G (IND.transmit d T S) = cong₂ (IND.transmit d) (apply-id-T T) (apply-id-S S)
apply-id-G (IND.choice d m alt) = cong (IND.choice d m) (ext (apply-id-S ∘ alt))
apply-id-G IND.end = refl

apply-id-T IND.TUnit = refl
apply-id-T IND.TInt = refl
apply-id-T (IND.TPair T T₁) = cong₂ IND.TPair (apply-id-T T) (apply-id-T T₁)
apply-id-T (IND.TChan S) = cong IND.TChan (apply-id-S S)

mc-equiv-S : (s : IND.SType 0)
  → DT.ind2coiS s ≈ DT.tail2coiS ε (MC.mclosureS s)
mc-equiv-G : (g : IND.GType 0)
  → DT.ind2coiG g ≈' DT.tail2coiG ε (MC.mclosureG g)
mc-equiv-T : (t : IND.TType 0)
  → (DT.ind2coiT t) ≈ᵗ DT.tail2coiT (MC.injectT (MC.applyT IND.var t))

COI.Equiv.force (mc-equiv-S (IND.gdd g)) = mc-equiv-G g
COI.Equiv.force (mc-equiv-S (IND.rec G)) = {!!}
-- mc-equiv-G (IND.st-substG G zero (IND.rec G))

mc-equiv-G (IND.transmit d t s) =
  COI.eq-transmit d (mc-equiv-T t) (mc-equiv-S s)
mc-equiv-G (IND.choice d m alt) =
  COI.eq-choice d (mc-equiv-S ∘ alt)
mc-equiv-G IND.end =
  COI.eq-end

mc-equiv-T IND.TUnit = COI.eq-unit
mc-equiv-T IND.TInt = COI.eq-int
mc-equiv-T (IND.TPair t t₁) = COI.eq-pair (mc-equiv-T t) (mc-equiv-T t₁)
mc-equiv-T (IND.TChan S) rewrite apply-id-S S = COI.eq-chan COI.≈-refl
