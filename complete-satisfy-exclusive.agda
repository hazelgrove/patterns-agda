open import Nat
open import Prelude
open import complete-satisfy-decidable
open import complete-constraints-core
open import contexts
open import core
open import judgemental-dual
open import result-judgements
open import statics-core
open import value-judgements

module complete-satisfy-exclusive where

  val-not-sat-sat-dual : ∀{Δ e τ ξ ξbar} →
                         e val →
                         ∅ , Δ ⊢ e :: τ →
                         ξ :cc: τ →
                         dual ξ ξbar →
                         (e ⊧ ξ → ⊥) →
                         e ⊧ ξbar
  val-not-sat-sat-dual eval wt ct CDTruth ¬sat = abort (¬sat CSTruth)
  val-not-sat-sat-dual eval wt ct CDFalsity ¬sat = CSTruth
  val-not-sat-sat-dual {e = N n} eval TANum ct (CDNum {n = m}) ¬sat
    with natEQ n m
  ... | Inl refl = CSNotNum (λ _ → ¬sat CSNum)
  ... | Inr ¬n=m = CSNotNum ¬n=m
  val-not-sat-sat-dual {e = N n} eval TANum ct (CDNotNum {n = m}) ¬sat
    with natEQ n m
  ... | Inl refl = CSNum
  ... | Inr ¬n=m = abort (¬sat (CSNotNum ¬n=m))
  val-not-sat-sat-dual {e = inl τ e} {ξ = inl ξ}
                       (VInl eval) (TAInl wt) (CTInl ct) (CDInl du) ¬sat
    with comp-satisfy-dec e ξ
  ... | Inl esat = abort (¬sat (CSInl esat))
  ... | Inr ¬esat = CSOrL (CSInl (val-not-sat-sat-dual eval wt ct du ¬esat))
  val-not-sat-sat-dual (VInr eval) (TAInr wt) (CTInl ct) (CDInl du) ¬sat =
    CSOrR (CSInr CSTruth)
  val-not-sat-sat-dual (VInl eval) (TAInl wt) (CTInr ct) (CDInr du) ¬sat =
    CSOrR (CSInl CSTruth)
  val-not-sat-sat-dual {e = inr τ e} {ξ = inr ξ}
                       (VInr eval) (TAInr wt) (CTInr ct) (CDInr du) ¬sat
    with comp-satisfy-dec e ξ
  ... | Inl esat = abort (¬sat (CSInr esat))
  ... | Inr ¬esat = CSOrL (CSInr (val-not-sat-sat-dual eval wt ct du ¬esat))
  val-not-sat-sat-dual {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                       (VPair eval1 eval2) (TAPair wt1 wt2)
                       (CTPair ct1 ct2) (CDPair du1 du2) ¬sat
    with comp-satisfy-dec e1 ξ1 | comp-satisfy-dec e2 ξ2
  ... | Inl sat1 | Inl sat2 = abort (¬sat (CSPair sat1 sat2))
  ... | Inl sat1 | Inr ¬sat2 =
    CSOrL (CSOrL (CSPair sat1 (val-not-sat-sat-dual eval2 wt2 ct2 du2 ¬sat2)))
  ... | Inr ¬sat1 | Inl sat2 =
    CSOrL (CSOrR (CSPair (val-not-sat-sat-dual eval1 wt1 ct1 du1 ¬sat1) sat2))
  ... | Inr ¬sat1 | Inr ¬sat2 =
    CSOrR (CSPair (val-not-sat-sat-dual eval1 wt1 ct1 du1 ¬sat1)
                  (val-not-sat-sat-dual eval2 wt2 ct2 du2 ¬sat2))
  val-not-sat-sat-dual {e = e} {ξ = ξ1 ∨ ξ2} eval wt (CTOr ct1 ct2) (CDOr du1 du2) ¬sat
    with comp-satisfy-dec e ξ1 | comp-satisfy-dec e ξ2
  ... | Inl sat1 | Inl sat2 = abort (¬sat (CSOrL sat1))
  ... | Inl sat1 | Inr ¬sat2 = abort (¬sat (CSOrL sat1))
  ... | Inr ¬sat1 | Inl sat2 = abort (¬sat (CSOrR sat2))
  ... | Inr ¬sat1 | Inr ¬sat2 =
    CSAnd (val-not-sat-sat-dual eval wt ct1 du1 ¬sat1)
          (val-not-sat-sat-dual eval wt ct2 du2 ¬sat2)
  val-not-sat-sat-dual {e = e} {ξ = ξ1 ∧ ξ2} eval wt (CTAnd ct1 ct2) (CDAnd du1 du2) ¬sat
    with comp-satisfy-dec e ξ1 | comp-satisfy-dec e ξ2
  ... | Inl sat1 | Inl sat2 = abort (¬sat (CSAnd sat1 sat2))
  ... | Inl sat1 | Inr ¬sat2 = CSOrR (val-not-sat-sat-dual eval wt ct2 du2 ¬sat2)
  ... | Inr ¬sat1 | Inl sat2 = CSOrL (val-not-sat-sat-dual eval wt ct1 du1 ¬sat1)
  ... | Inr ¬sat1 | Inr ¬sat2 = CSOrL (val-not-sat-sat-dual eval wt ct1 du1 ¬sat1)
  
  val-sat-dual-not-sat : ∀{e ξ ξbar} →
                         e val →
                         dual ξ ξbar →
                         e ⊧ ξbar →
                         e ⊧ ξ →
                         ⊥
  val-sat-dual-not-sat eval CDNum (CSNotNum n≠n) CSNum = n≠n refl
  val-sat-dual-not-sat eval CDNotNum CSNum (CSNotNum n≠n) = n≠n refl
  val-sat-dual-not-sat (VInl eval) (CDInl du) (CSOrL (CSInl satbar)) (CSInl sat) =
    val-sat-dual-not-sat eval du satbar sat
  val-sat-dual-not-sat (VInl eval) (CDInl du) (CSOrR ()) (CSInl sat)
  val-sat-dual-not-sat (VInr eval) (CDInr du) (CSOrL (CSInr satbar)) (CSInr sat) =
    val-sat-dual-not-sat eval du satbar sat
  val-sat-dual-not-sat (VInr eval) (CDInr du) (CSOrR ()) (CSInr sat)
  val-sat-dual-not-sat (VPair eval1 eval2) (CDPair du1 du2)
                       (CSOrL (CSOrL (CSPair sat1' satbar2))) (CSPair sat1 sat2) =
    val-sat-dual-not-sat eval2 du2 satbar2 sat2
  val-sat-dual-not-sat (VPair eval1 eval2) (CDPair du1 du2)
                       (CSOrL (CSOrR (CSPair satbar1 sat2'))) (CSPair sat1 sat2) =
    val-sat-dual-not-sat eval1 du1 satbar1 sat1
  val-sat-dual-not-sat (VPair eval1 eval2) (CDPair du1 du2)
                       (CSOrR (CSPair satbar1 satbar2)) (CSPair sat1 sat2) =
    val-sat-dual-not-sat eval2 du2 satbar2 sat2
  val-sat-dual-not-sat eval (CDOr du1 du2) (CSAnd satbar1 satbar2) (CSOrL sat1) =
    val-sat-dual-not-sat eval du1 satbar1 sat1
  val-sat-dual-not-sat eval (CDOr du1 du2) (CSAnd satbar1 satbar2) (CSOrR sat2) =
    val-sat-dual-not-sat eval du2 satbar2 sat2
  val-sat-dual-not-sat eval (CDAnd du1 du2) (CSOrL satbar1) (CSAnd sat1 sat2) =
    val-sat-dual-not-sat eval du1 satbar1 sat1
  val-sat-dual-not-sat eval (CDAnd du1 du2) (CSOrR satbar2) (CSAnd sat1 sat2) =
    val-sat-dual-not-sat eval du2 satbar2 sat2


  -- result of the exclusivity theorem
  data ExCompSat (e : ihexp) (ξ : comp-constr) : Set where
    Satisfy     : (e ⊧ ξ)     → (e ⊧ (ξ ◆d) → ⊥) → ExCompSat e ξ
    SatisfyDual : (e ⊧ ξ → ⊥) → (e ⊧ (ξ ◆d))     → ExCompSat e ξ
  

  -- exclusivity of satisfaction
  comp-satisfy-exclusive : ∀{ξ τ Δ e} →
                           ξ :cc: τ →
                           ∅ , Δ ⊢ e :: τ →
                           e val →
                           ExCompSat e ξ
  comp-satisfy-exclusive {ξ = ξ} {e = e} ct wt eval
    with comp-satisfy-dec e ξ | comp-satisfy-dec e (ξ ◆d)
  ... | Inl sat | Inl satd = abort (val-sat-dual-not-sat eval (rel◆d ξ) satd sat)
  ... | Inr ¬sat | Inr ¬satd = abort (¬satd (val-not-sat-sat-dual eval wt ct (rel◆d ξ) ¬sat))
  ... | Inl sat | Inr ¬satd = Satisfy sat ¬satd
  ... | Inr ¬sat | Inl satd = SatisfyDual ¬sat satd
