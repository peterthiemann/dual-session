{-# OPTIONS --rewriting --guardedness #-}
module StopDualSoundness where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Function using (_∘_)
import Types.IND1 as IND
import Types.COI as COI
import DualTail1 as DT
import DualStopAtMu as Stop
import Conversion as Conv

private
  variable
    m : ℕ
    T U V : IND.Type 0
    S R Q : IND.SType 0
    G H : IND.GType 0
    G₁ : IND.GType 1
    F K L M : COI.STypeF COI.SType
    X Y Z W : COI.SType

----------------------------------------------------------------------
-- Transport of coinductive duality along coinductive equivalence

⊥-resp-≈ :
  X COI.≈ Y →
  Z COI.≈ W →
  Y COI.⊥ Z →
  X COI.⊥ W
⊥'-resp-≈ :
  COI.EquivF COI.Equiv F K →
  COI.EquivF COI.Equiv L M →
  COI.DualF COI.Dual K L →
  COI.DualF COI.Dual F M

COI.Dual.force (⊥-resp-≈ X≈Y Z≈Q Y⊥Z) =
  ⊥'-resp-≈
    (COI.Equiv.force X≈Y)
    (COI.Equiv.force Z≈Q)
    (COI.Dual.force Y⊥Z)

⊥'-resp-≈
  (COI.eq-transmit d T≈U S≈R)
  (COI.eq-transmit d' T'≈U' S'≈R')
  (COI.dual-transmit dualD U≈T' R⊥S') =
  COI.dual-transmit
    dualD
    (COI.≈ᵗ-trans T≈U (COI.≈ᵗ-trans U≈T' T'≈U'))
    (⊥-resp-≈ S≈R S'≈R' R⊥S')
⊥'-resp-≈
  (COI.eq-choice d S≈R)
  (COI.eq-choice d' S'≈R')
  (COI.dual-choice dualD R⊥S') =
  COI.dual-choice dualD (λ i → ⊥-resp-≈ (S≈R i) (S'≈R' i) (R⊥S' i))
⊥'-resp-≈ COI.eq-end COI.eq-end COI.dual-end =
  COI.dual-end

----------------------------------------------------------------------
-- Syntactic equivalence is sound for the stack interpretation

unfold-sound :
  (S : IND.SType 0) →
  DT.ind2coiS DT.ε S COI.≈ DT.ind2coiS DT.ε (IND.gdd (IND.unfold S))

COI.Equiv.force (unfold-sound (IND.gdd G)) =
  COI.≈'-refl
COI.Equiv.force (unfold-sound (IND.rec G)) =
  Conv.subst-soundG (Conv.root G) G

data EqRel : COI.SType → COI.SType → Set where
  eq-state :
    S IND.≈ R →
    EqRel (DT.ind2coiS DT.ε S) (DT.ind2coiS DT.ε R)

  eq-known :
    X COI.≈ Y →
    EqRel X Y

  eq-trans :
    EqRel X Y →
    EqRel Y Z →
    EqRel X Z

eq-step :
  EqRel X Y →
  COI.EquivF EqRel (COI.SType.force X) (COI.SType.force Y)
eq-stepG :
  G IND.≈' H →
  COI.EquivF EqRel (DT.ind2coiG DT.ε G) (DT.ind2coiG DT.ε H)
eq-stepT :
  IND.EquivT IND.Equiv T U →
  COI.EquivT EqRel
    (DT.ind2coiT DT.ε T)
    (DT.ind2coiT DT.ε U)

eq-step (eq-known p) =
  COI.mapEquivF eq-known (COI.Equiv.force p)
eq-step (eq-trans p q) =
  COI.transEquivF eq-trans (eq-step p) (eq-step q)
eq-step (eq-state {S = S} {R = R} S≈R) =
  COI.transEquivF eq-trans
    (COI.mapEquivF eq-known (COI.Equiv.force (unfold-sound S)))
    (COI.transEquivF eq-trans
      (eq-stepG (IND.Equiv.force S≈R))
      (COI.mapEquivF eq-known (COI.≈'-symm (COI.Equiv.force (unfold-sound R)))))

eq-stepG (IND.eq-transmit d T≈U S≈R) =
  COI.eq-transmit d (eq-stepT T≈U) (eq-state S≈R)
eq-stepG (IND.eq-choice d S≈R) =
  COI.eq-choice d (eq-state ∘ S≈R)
eq-stepG IND.eq-end =
  COI.eq-end

eq-stepT IND.eq-unit =
  COI.eq-unit
eq-stepT IND.eq-int =
  COI.eq-int
eq-stepT (IND.eq-pair T≈U V≈W) =
  COI.eq-pair (eq-stepT T≈U) (eq-stepT V≈W)
eq-stepT (IND.eq-fun T≈U V≈W) =
  COI.eq-fun (eq-stepT T≈U) (eq-stepT V≈W)
eq-stepT (IND.eq-chan S≈R) =
  COI.eq-chan (eq-state S≈R)

module EqClose = COI.CloseEquiv EqRel eq-step

equiv-soundS :
  S IND.≈ R →
  DT.ind2coiS DT.ε S COI.≈ DT.ind2coiS DT.ε R
equiv-soundS S≈R =
  EqClose.close (eq-state S≈R)

equiv-soundG :
  G IND.≈' H →
  DT.ind2coiG DT.ε G COI.≈' DT.ind2coiG DT.ε H
equiv-soundG G≈H =
  EqClose.closeF (eq-stepG G≈H)

equiv-soundT :
  IND.EquivT IND.Equiv T U →
  COI.EquivT COI.Equiv
    (DT.ind2coiT DT.ε T)
    (DT.ind2coiT DT.ε U)
equiv-soundT T≈U =
  EqClose.closeT (eq-stepT T≈U)

----------------------------------------------------------------------
-- Soundness of stopped duality

data SdRel : COI.SType → COI.SType → Set where
  sd-state :
    S Stop.⊥sd R →
    SdRel (DT.ind2coiS DT.ε S) (DT.ind2coiS DT.ε R)

  sd-transport :
    X COI.≈ Y →
    SdRel Y Z →
    Z COI.≈ W →
    SdRel X W

sd-respF :
  COI.EquivF COI.Equiv F K →
  COI.EquivF COI.Equiv L M →
  COI.DualF SdRel K L →
  COI.DualF SdRel F M
sd-respF
  (COI.eq-transmit d T≈U S≈R)
  (COI.eq-transmit d' T'≈U' S'≈R')
  (COI.dual-transmit dualD U≈T' R⊥S') =
  COI.dual-transmit
    dualD
    (COI.≈ᵗ-trans T≈U (COI.≈ᵗ-trans U≈T' T'≈U'))
    (sd-transport S≈R R⊥S' S'≈R')
sd-respF
  (COI.eq-choice d S≈R)
  (COI.eq-choice d' S'≈R')
  (COI.dual-choice dualD R⊥S') =
  COI.dual-choice dualD
    (λ i → sd-transport (S≈R i) (R⊥S' i) (S'≈R' i))
sd-respF COI.eq-end COI.eq-end COI.dual-end =
  COI.dual-end

sd-step :
  SdRel X Y →
  COI.DualF SdRel (COI.SType.force X) (COI.SType.force Y)
sd-stepG :
  Stop.StopDualG Stop.StopDual G H →
  COI.DualF SdRel (DT.ind2coiG DT.ε G) (DT.ind2coiG DT.ε H)

sd-step (sd-state {S = S} {R = R} S⊥R) =
  sd-respF
    (COI.Equiv.force (unfold-sound S))
    (COI.≈'-symm (COI.Equiv.force (unfold-sound R)))
    (sd-stepG (Stop.StopDual.observe S⊥R))
sd-step (sd-transport X≈Y Y⊥Z Z≈W) =
  sd-respF
    (COI.Equiv.force X≈Y)
    (COI.Equiv.force Z≈W)
    (sd-step Y⊥Z)

sd-stepG (Stop.sd-transmit dualD T≈U S⊥R) =
  COI.dual-transmit dualD (equiv-soundT T≈U) (sd-state S⊥R)
sd-stepG (Stop.sd-choice dualD S⊥R) =
  COI.dual-choice dualD (sd-state ∘ S⊥R)
sd-stepG Stop.sd-end =
  COI.dual-end

sd-close :
  SdRel X Y →
  X COI.⊥ Y
sd-closeF :
  COI.DualF SdRel F K →
  COI.DualF COI.Dual F K

COI.Dual.force (sd-close rel) =
  sd-closeF (sd-step rel)

sd-closeF (COI.dual-transmit dualD T≈U S⊥R) =
  COI.dual-transmit dualD T≈U (sd-close S⊥R)
sd-closeF (COI.dual-choice dualD S⊥R) =
  COI.dual-choice dualD (sd-close ∘ S⊥R)
sd-closeF COI.dual-end =
  COI.dual-end

sd-sound :
  S Stop.⊥sd R →
  DT.ind2coiS DT.ε S COI.⊥ DT.ind2coiS DT.ε R
sd-sound S⊥R =
  sd-close (sd-state S⊥R)

sd-soundG :
  Stop.StopDualG Stop.StopDual G H →
  DT.ind2coiG DT.ε G COI.⊥' DT.ind2coiG DT.ε H
sd-soundG G⊥H =
  sd-closeF (sd-stepG G⊥H)

----------------------------------------------------------------------
-- Completeness of syntactic equivalence for the stack interpretation

data EqCompleteRel : IND.SType 0 → IND.SType 0 → Set where
  eqc-state :
    DT.ind2coiS DT.ε S COI.≈ DT.ind2coiS DT.ε R →
    EqCompleteRel S R

eqc-step :
  EqCompleteRel S R →
  IND.EquivG EqCompleteRel (IND.unfold S) (IND.unfold R)
eqc-stepG :
  COI.EquivF COI.Equiv (DT.ind2coiG DT.ε G) (DT.ind2coiG DT.ε H) →
  IND.EquivG EqCompleteRel G H
eqc-stepT :
  COI.EquivT COI.Equiv (DT.ind2coiT DT.ε T) (DT.ind2coiT DT.ε U) →
  IND.EquivT EqCompleteRel T U

eqc-step (eqc-state {S = S} {R = R} S≈R) =
  eqc-stepG
    (COI.Equiv.force
      (COI.≈-trans
        (COI.≈-symm (unfold-sound S))
        (COI.≈-trans S≈R (unfold-sound R))))

eqc-stepG
  {G = IND.transmit d T S}
  {H = IND.transmit .d U R}
  (COI.eq-transmit .d T≈U S≈R) =
  IND.eq-transmit d (eqc-stepT T≈U) (eqc-state S≈R)
eqc-stepG
  {G = IND.choice d m alt}
  {H = IND.choice .d .m alt'}
  (COI.eq-choice .d S≈R) =
  IND.eq-choice d (eqc-state ∘ S≈R)
eqc-stepG
  {G = IND.end}
  {H = IND.end}
  COI.eq-end =
  IND.eq-end

eqc-stepT {T = IND.TUnit} {U = IND.TUnit} COI.eq-unit =
  IND.eq-unit
eqc-stepT {T = IND.TInt} {U = IND.TInt} COI.eq-int =
  IND.eq-int
eqc-stepT
  {T = IND.TPair T U}
  {U = IND.TPair T' U'}
  (COI.eq-pair T≈T' U≈U') =
  IND.eq-pair (eqc-stepT T≈T') (eqc-stepT U≈U')
eqc-stepT
  {T = IND.TFun T U}
  {U = IND.TFun T' U'}
  (COI.eq-fun T≈T' U≈U') =
  IND.eq-fun (eqc-stepT T≈T') (eqc-stepT U≈U')
eqc-stepT
  {T = IND.TChan S}
  {U = IND.TChan R}
  (COI.eq-chan S≈R) =
  IND.eq-chan (eqc-state S≈R)

eqc-close :
  EqCompleteRel S R →
  S IND.≈ R
eqc-closeG :
  IND.EquivG EqCompleteRel G H →
  G IND.≈' H
eqc-closeT :
  IND.EquivT EqCompleteRel T U →
  IND.EquivT IND.Equiv T U

IND.Equiv.force (eqc-close rel) =
  eqc-closeG (eqc-step rel)

eqc-closeG (IND.eq-transmit d T≈U S≈R) =
  IND.eq-transmit d (eqc-closeT T≈U) (eqc-close S≈R)
eqc-closeG (IND.eq-choice d S≈R) =
  IND.eq-choice d (eqc-close ∘ S≈R)
eqc-closeG IND.eq-end =
  IND.eq-end

eqc-closeT IND.eq-unit =
  IND.eq-unit
eqc-closeT IND.eq-int =
  IND.eq-int
eqc-closeT (IND.eq-pair T≈U V≈W) =
  IND.eq-pair (eqc-closeT T≈U) (eqc-closeT V≈W)
eqc-closeT (IND.eq-fun T≈U V≈W) =
  IND.eq-fun (eqc-closeT T≈U) (eqc-closeT V≈W)
eqc-closeT (IND.eq-chan S≈R) =
  IND.eq-chan (eqc-close S≈R)

equiv-completeS :
  DT.ind2coiS DT.ε S COI.≈ DT.ind2coiS DT.ε R →
  S IND.≈ R
equiv-completeS S≈R =
  eqc-close (eqc-state S≈R)

equiv-completeG :
  DT.ind2coiG DT.ε G COI.≈' DT.ind2coiG DT.ε H →
  G IND.≈' H
equiv-completeG G≈H =
  eqc-closeG (eqc-stepG G≈H)

equiv-completeT :
  COI.EquivT COI.Equiv
    (DT.ind2coiT DT.ε T)
    (DT.ind2coiT DT.ε U) →
  IND.EquivT IND.Equiv T U
equiv-completeT T≈U =
  eqc-closeT (eqc-stepT T≈U)

----------------------------------------------------------------------
-- Completeness of stopped duality

data SdCompleteRel : IND.SType 0 → IND.SType 0 → Set where
  sdc-state :
    DT.ind2coiS DT.ε S COI.⊥ DT.ind2coiS DT.ε R →
    SdCompleteRel S R

sdc-step :
  SdCompleteRel S R →
  Stop.StopDualG SdCompleteRel (IND.unfold S) (IND.unfold R)
sdc-stepG :
  DT.ind2coiG DT.ε G COI.⊥' DT.ind2coiG DT.ε H →
  Stop.StopDualG SdCompleteRel G H

sdc-step (sdc-state {S = S} {R = R} S⊥R) =
  sdc-stepG
    (COI.Dual.force
      (⊥-resp-≈
        (COI.≈-symm (unfold-sound S))
        (unfold-sound R)
        S⊥R))

sdc-stepG
  {G = IND.transmit d T S}
  {H = IND.transmit d' U R}
  (COI.dual-transmit dualD T≈U S⊥R) =
  Stop.sd-transmit dualD (equiv-completeT T≈U) (sdc-state S⊥R)
sdc-stepG
  {G = IND.choice d m alt}
  {H = IND.choice d' .m alt'}
  (COI.dual-choice dualD S⊥R) =
  Stop.sd-choice dualD (sdc-state ∘ S⊥R)
sdc-stepG
  {G = IND.end}
  {H = IND.end}
  COI.dual-end =
  Stop.sd-end

sdc-close :
  SdCompleteRel S R →
  S Stop.⊥sd R
sdc-closeG :
  Stop.StopDualG SdCompleteRel G H →
  Stop.StopDualG Stop.StopDual G H

Stop.StopDual.observe (sdc-close rel) =
  sdc-closeG (sdc-step rel)

sdc-closeG (Stop.sd-transmit dualD T≈U S⊥R) =
  Stop.sd-transmit dualD T≈U (sdc-close S⊥R)
sdc-closeG (Stop.sd-choice dualD S⊥R) =
  Stop.sd-choice dualD (sdc-close ∘ S⊥R)
sdc-closeG Stop.sd-end =
  Stop.sd-end

sd-complete :
  DT.ind2coiS DT.ε S COI.⊥ DT.ind2coiS DT.ε R →
  S Stop.⊥sd R
sd-complete S⊥R =
  sdc-close (sdc-state S⊥R)

sd-completeG :
  DT.ind2coiG DT.ε G COI.⊥' DT.ind2coiG DT.ε H →
  Stop.StopDualG Stop.StopDual G H
sd-completeG G⊥H =
  sdc-closeG (sdc-stepG G⊥H)
