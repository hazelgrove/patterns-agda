open import Nat
open import contexts
open import core
open import dynamics-core
open import statics-core
open import result-judgements

module preservation where
  preservation : ∀{Δ e1 τ e2} →
                 ∅ , Δ ⊢ e1 :: τ →
                 e1 ↦ e2 →
                 ∅ , Δ ⊢ e2 :: τ
  preservation (TAAp wt1 wt2) (ITApFun stp) =
    TAAp (preservation wt1 stp) wt2
  preservation (TAAp wt1 wt2) (ITApArg eval stp) =
    TAAp wt1 (preservation wt2 stp)
  preservation (TAAp wt1 wt2) (ITAp eval) = {!!}
  preservation (TAInl wt) (ITInl stp) =
    TAInl (preservation wt stp)
  preservation (TAInr wt) (ITInr stp) =
    TAInr (preservation wt stp)
  preservation (TAMatchZPre wt rst) stp = {!!}
  preservation (TAMatchNZPre wt fin pre post ¬red) stp = {!!}
  preservation (TAPair wt1 wt2) (ITPairL stp) =
    TAPair (preservation wt1 stp) wt2
  preservation (TAPair wt1 wt2) (ITPairR val1 stp) =
    TAPair wt1 (preservation wt2 stp)
  preservation (TAFst (TAPair wt1 wt2)) (ITFst fin) = wt1
  preservation (TASnd (TAPair wt1 wt2)) (ITSnd fin) = wt2
  preservation (TANEHole x wt) (ITNEHole stp) =
    TANEHole x (preservation wt stp)
  
