module Direction where

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

----------------------------------------------------------------------
-- direction

data Dir : Set where
  SND RCV : Dir

variable
  d d₁ d₂ d₃ : Dir

-- dual
dual-dir : Dir → Dir
dual-dir SND = RCV
dual-dir RCV = SND

dual-dir-inv : (d : Dir) → dual-dir (dual-dir d) ≡ d
dual-dir-inv SND = refl
dual-dir-inv RCV = refl

