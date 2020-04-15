module MessageClosure where

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat
open import Function

open import Types.IND
import Types.Tail1 as Tail

private
  variable
    m n : ℕ

-- message closure guarantees that the type of each message in a session type is closed

upS : SType m → SType (suc m)
upG : GType m → GType (suc m)
upT : Type m → Type (suc m)

upS (gdd G) = gdd (upG G)
upS (rec G) = rec (upG G)
upS (var p x) = var p (suc x)

upG (transmit d T S) = transmit d (upT T) (upS S)
upG (choice d m alt) = choice d m (upS ∘ alt)
upG end = end

upT TUnit = TUnit
upT TInt = TInt
upT (TPair t t₁) = TPair (upT t) (upT t₁)
upT (TChan S) = TChan (upS S)

shift : (Fin (m + n) → SType m) → (Fin (suc m + n) → SType (suc m))
shift σ zero = var POS zero
shift σ (suc x) = upS (σ x)

applyT : (Fin (m + n) → SType m) → TType (m + n) → TType m
applyS : (Fin (m + n) → SType m) → SType (m + n) → SType m
applyG : (Fin (m + n) → SType m) → GType (m + n) → GType m

applyT σ TUnit = TUnit
applyT σ TInt = TInt
applyT σ (TPair T T₁) = TPair (applyT σ T) (applyT σ T₁)
applyT σ (TChan x) = TChan (applyS σ x)

applyS σ (gdd gst) = gdd (applyG σ gst)
applyS σ (rec gst) = rec (applyG (shift σ) gst)
applyS σ (var p x) = σ x 

applyG σ (transmit d t s) = transmit d (applyT σ t) (applyS σ s)
applyG σ (choice d m alt) = choice d m (applyS σ ∘ alt)
applyG σ end = end

injectT : TType 0 → Tail.Type

injectT TUnit = Tail.TUnit
injectT TInt = Tail.TInt
injectT (TPair t t₁) = Tail.TPair (injectT t) (injectT t₁)
injectT (TChan S) = Tail.TChan S

ext : (Fin n → SType 0) → SType n → (Fin (suc n) → SType 0)

ext σ S zero = applyS σ S
ext σ S (suc i) = σ i

mcloS : (Fin n → SType 0) → SType n → Tail.SType n
mcloG : (Fin n → SType 0) → GType n → Tail.GType n

mcloS σ (gdd gst) = Tail.gdd (mcloG σ gst)
mcloS σ (rec gst) = Tail.rec (mcloG (ext σ (rec gst)) gst)
mcloS σ (var p x) = Tail.var x

mcloG σ (transmit d t s) = Tail.transmit d (injectT (applyT σ t)) (mcloS σ s)
mcloG σ (choice d m alt) = Tail.choice d m (mcloS σ ∘ alt)
mcloG σ end = Tail.end

mclosureS : SType 0 → Tail.SType 0
mclosureS = mcloS λ()

mclosureG : GType 0 → Tail.GType 0
mclosureG = mcloG λ()
