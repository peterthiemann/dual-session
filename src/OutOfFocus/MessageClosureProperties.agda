{-# OPTIONS --rewriting --guardedness #-}
module OutOfFocus.MessageClosureProperties where

open import Data.Nat using (ℕ; zero ; suc)
import Data.Nat.Properties as ℕₚ using (+-identityʳ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; sym; refl)
open import Agda.Builtin.Equality.Rewrite

{-# REWRITE ℕₚ.+-identityʳ #-}

open import Auxiliary.Extensionality

import Types.COI as COI
import Types.IND1 as IND
import Types.Tail1 as Tail
import DualTail1 as DT
import MessageClosure as MC

open COI using (_≈_; _≈'_; _≈ᵗ_)
open DT using (Stack; ε; ⟪_,_⟫)

private
  variable
    n : ℕ
    σ σ′ : Stack n
    G : IND.GType n

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
apply-id-T (IND.TFun T T₁) = cong₂ IND.TFun (apply-id-T T) (apply-id-T T₁)
apply-id-T (IND.TChan S) = cong IND.TChan (apply-id-S S)

mc-equiv-S-1 : {G' : IND.GType 1} → (S : IND.SType 1) →
  (DT.ind2coiS ⟪ ε , G' ⟫ S) ≈
  (DT.tail2coiS ⟪ ε , MC.mcloG (MC.ext IND.var (IND.rec G')) G' ⟫
       (MC.mcloS (MC.ext IND.var (IND.rec G')) S))

mc-equiv-G-1 : {G' : IND.GType 1} → (G : IND.GType 1) →
  (DT.ind2coiG ⟪ ε , G' ⟫ G) ≈'
  (DT.tail2coiG ⟪ ε , MC.mcloG (MC.ext IND.var (IND.rec G')) G' ⟫
                (MC.mcloG (MC.ext IND.var (IND.rec G')) G))
mc-equiv-T-1 : {G' : IND.GType 1} → (T : IND.Type 1) →
  (DT.ind2coiT ⟪ ε , G' ⟫ T) ≈ᵗ
  (DT.tail2coiT
       (MC.injectT (MC.applyT (MC.ext IND.var (IND.rec G')) T)))

COI.Equiv.force (mc-equiv-S-1 (IND.gdd G)) = mc-equiv-G-1 G
COI.Equiv.force (mc-equiv-S-1 (IND.rec G)) = {!!}
COI.Equiv.force (mc-equiv-S-1 {G'} (IND.var x)) = {!!}

mc-equiv-G-1 (IND.transmit d T S) = COI.eq-transmit d (mc-equiv-T-1 T) (mc-equiv-S-1 S)
mc-equiv-G-1 (IND.choice d m alt) = COI.eq-choice d (mc-equiv-S-1 ∘ alt)
mc-equiv-G-1 IND.end = COI.eq-end

mc-equiv-T-1 IND.TUnit = COI.eq-unit
mc-equiv-T-1 IND.TInt = COI.eq-int
mc-equiv-T-1 (IND.TPair T T₁) = COI.eq-pair (mc-equiv-T-1 T) (mc-equiv-T-1 T₁)
mc-equiv-T-1 (IND.TFun T T₁) = COI.eq-fun (mc-equiv-T-1 T) (mc-equiv-T-1 T₁)
mc-equiv-T-1 (IND.TChan S) = COI.eq-chan {!!}

mc-equiv-S : (s : IND.SType 0)
  → DT.ind2coiS ε s ≈ DT.tail2coiS ε (MC.mclosureS s)
mc-equiv-G : (g : IND.GType 0)
  → DT.ind2coiG ε g ≈' DT.tail2coiG ε (MC.mclosureG g)
mc-equiv-T : (t : IND.TType 0)
  → DT.ind2coiT ε t ≈ᵗ DT.tail2coiT (MC.injectT (MC.applyT IND.var t))

COI.Equiv.force (mc-equiv-S (IND.gdd g)) = mc-equiv-G g
COI.Equiv.force (mc-equiv-S (IND.rec G)) = mc-equiv-G-1 G
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
mc-equiv-T (IND.TFun t t₁) = COI.eq-fun (mc-equiv-T t) (mc-equiv-T t₁)
mc-equiv-T (IND.TChan S) rewrite apply-id-S S = COI.eq-chan COI.≈-refl

-- relation between two stacks (to fill above hole in mc-equiv-S)

data Related : DT.Stack {IND.GType} n → Stack {Tail.GType} n → Set where
  base : Related {0} ε ε
  step : Related {n} σ σ′
       → Related {suc n} ⟪ σ , G ⟫ ⟪ σ′ , MC.mcloG (MC.ext {!!} (IND.rec G)) G ⟫
