{-# OPTIONS --rewriting --guardedness #-}
module ConversionStopDualSoundness where

import Types.IND1 as IND
import Types.COI as COI
import DualTail1 as DT
import DualStopAtMu as Stop
import Conversion as Conv
import StopDualSoundness as SDS

private
  variable
    S R : IND.SType 0

semS : IND.SType 0 → COI.SType
semS =
  DT.ind2coiS DT.ε

infix 1 _↔_

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    to : A → B
    from : B → A

----------------------------------------------------------------------
-- Conversion to the stopped-dual term implies observational stopped duality

conv-dual-sound-coi :
  Conv.ConvS (Stop.dualS S) R →
  semS S COI.⊥ semS R
conv-dual-sound-coi {S = S} Sdual≈R =
  SDS.⊥-resp-≈
    COI.≈-refl
    (COI.≈-trans (Stop.ground S) (Conv.convS-sound Sdual≈R))
    COI.dual-soundS

conv-dual-sound-sd :
  Conv.ConvS (Stop.dualS S) R →
  S Stop.⊥sd R
conv-dual-sound-sd Sdual≈R =
  SDS.sd-complete (conv-dual-sound-coi Sdual≈R)

----------------------------------------------------------------------
-- Observational stopped duality implies equivalence to the stopped-dual term

sd-complete-dualS-coi :
  S Stop.⊥sd R →
  semS (Stop.dualS S) COI.≈ semS R
sd-complete-dualS-coi {S = S} S⊥R =
  COI.≈-trans
    (COI.≈-symm (Stop.ground S))
    (COI.≈-symm (COI.dual-completeS (COI.⊥-symm (SDS.sd-sound S⊥R))))

sd-complete-dualS-≈ :
  S Stop.⊥sd R →
  Stop.dualS S IND.≈ R
sd-complete-dualS-≈ S⊥R =
  SDS.equiv-completeS (sd-complete-dualS-coi S⊥R)

sd-sound-dualS-coi :
  semS (Stop.dualS S) COI.≈ semS R →
  semS S COI.⊥ semS R
sd-sound-dualS-coi {S = S} dualS≈R =
  SDS.⊥-resp-≈
    COI.≈-refl
    (COI.≈-trans (Stop.ground S) dualS≈R)
    COI.dual-soundS

sd-sound-dualS-≈ :
  Stop.dualS S IND.≈ R →
  S Stop.⊥sd R
sd-sound-dualS-≈ dualS≈R =
  SDS.sd-complete (sd-sound-dualS-coi (SDS.equiv-soundS dualS≈R))

----------------------------------------------------------------------
-- Master comparison

coi-dual-complete :
  semS S COI.⊥ semS R →
  COI.dual (semS S) COI.≈ semS R
coi-dual-complete S⊥R =
  COI.≈-symm (COI.dual-completeS (COI.⊥-symm S⊥R))

coi-dual-sound :
  COI.dual (semS S) COI.≈ semS R →
  semS S COI.⊥ semS R
coi-dual-sound dualS≈R =
  SDS.⊥-resp-≈ COI.≈-refl dualS≈R COI.dual-soundS

functional-to-stopped-coi :
  COI.dual (semS S) COI.≈ semS R →
  semS (Stop.dualS S) COI.≈ semS R
functional-to-stopped-coi {S = S} dualS≈R =
  COI.≈-trans (COI.≈-symm (Stop.ground S)) dualS≈R

stopped-to-functional-coi :
  semS (Stop.dualS S) COI.≈ semS R →
  COI.dual (semS S) COI.≈ semS R
stopped-to-functional-coi {S = S} stopped≈R =
  COI.≈-trans (Stop.ground S) stopped≈R

record MasterComparison (S R : IND.SType 0) : Set where
  field
    sd-coi :
      (S Stop.⊥sd R) ↔
      (semS S COI.⊥ semS R)

    sd-functional :
      (S Stop.⊥sd R) ↔
      (COI.dual (semS S) COI.≈ semS R)

    sd-stopped-coi :
      (S Stop.⊥sd R) ↔
      (semS (Stop.dualS S) COI.≈ semS R)

    sd-stopped-syntax :
      (S Stop.⊥sd R) ↔
      (Stop.dualS S IND.≈ R)

master-comparison :
  MasterComparison S R
master-comparison =
  record
    { sd-coi =
        iff SDS.sd-sound SDS.sd-complete

    ; sd-functional =
        iff
          (λ S⊥R → coi-dual-complete (SDS.sd-sound S⊥R))
          (λ dualS≈R → SDS.sd-complete (coi-dual-sound dualS≈R))

    ; sd-stopped-coi =
        iff
          sd-complete-dualS-coi
          (λ stopped≈R → SDS.sd-complete (sd-sound-dualS-coi stopped≈R))

    ; sd-stopped-syntax =
        iff sd-complete-dualS-≈ sd-sound-dualS-≈
    }
