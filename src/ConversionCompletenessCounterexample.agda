{-# OPTIONS --rewriting --guardedness #-}
module ConversionCompletenessCounterexample where

open import Data.Fin using (zero)
open import Types.Direction using (SND; RCV)
import Types.IND1 as IND
import Types.COI as COI
import Conversion as Conv
import DualStopAtMu as Stop
import StopDualSoundness as SDS

----------------------------------------------------------------------
-- Candidate counterexample to completeness of conversion for stopped duality

-- The left endpoint receives forever.
recv-loop : IND.SType 0
recv-loop =
  IND.rec (IND.transmit RCV IND.TUnit (IND.var zero))

-- The right endpoint sends forever, but its syntactic period contains two
-- sends before returning to the recursive variable.
send-loop₂ : IND.SType 0
send-loop₂ =
  IND.rec
    (IND.transmit SND IND.TUnit
      (IND.gdd (IND.transmit SND IND.TUnit (IND.var zero))))

send-loop₁ : IND.SType 0
send-loop₁ =
  IND.rec (IND.transmit SND IND.TUnit (IND.var zero))

-- Conversion can expose one send from the stopped dual of recv-loop.
dual-recv-loop-step :
  Conv.ConvS
    (Stop.dualS recv-loop)
    (IND.gdd (IND.transmit SND IND.TUnit (Stop.dualS recv-loop)))
dual-recv-loop-step =
  Conv.conv-dual Conv.conv-unroll

-- Conversion can expose two sends from send-loop₂.
send-loop₂-step :
  Conv.ConvS
    send-loop₂
    (IND.gdd
      (IND.transmit SND IND.TUnit
        (IND.gdd (IND.transmit SND IND.TUnit send-loop₂))))
send-loop₂-step =
  Conv.conv-unroll

-- Coinductively, recv-loop is dual to send-loop₂: after one receive/send
-- step, the same obligation reappears with one extra unfolding on the right.
mutual
  recv-loop⊥sd-send-loop₂ :
    recv-loop Stop.⊥sd send-loop₂
  Stop.StopDual.observe recv-loop⊥sd-send-loop₂ =
    Stop.sd-transmit
      COI.dual-rs
      IND.eq-unit
      recv-loop⊥sd-send-loop₂'

  recv-loop⊥sd-send-loop₂' :
    recv-loop Stop.⊥sd IND.gdd (IND.transmit SND IND.TUnit send-loop₂)
  Stop.StopDual.observe recv-loop⊥sd-send-loop₂' =
    Stop.sd-transmit
      COI.dual-rs
      IND.eq-unit
      recv-loop⊥sd-send-loop₂

recv-loop⊥coi-send-loop₂ :
  Conv.semS recv-loop COI.⊥ Conv.semS send-loop₂
recv-loop⊥coi-send-loop₂ =
  SDS.sd-sound recv-loop⊥sd-send-loop₂
