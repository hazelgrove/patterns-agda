open import Prelude
open import core
open import complete-constraints-core
open import constraints-core
open import lemmas-satisfy
open import statics-core
open import value-judgements

module complete-relationship where
  val-satmay-sat-truthify : ∀{e ξ} →
                            e val →
                            e ⊧̇†? ξ →
                            e ⊧ (ξ ◆⊤)
  val-satmay-sat-truthify eval (CSMSSat CSTruth) = CSTruth
  val-satmay-sat-truthify eval (CSMSSat CSNum) = CSNum
  val-satmay-sat-truthify (VInl eval) (CSMSSat (CSInl sat)) =
    CSInl (val-satmay-sat-truthify eval (CSMSSat sat))
  val-satmay-sat-truthify (VInr eval) (CSMSSat (CSInr sat)) =
    CSInr (val-satmay-sat-truthify eval (CSMSSat sat))
  val-satmay-sat-truthify (VPair eval1 eval2) (CSMSSat (CSPair sat1 sat2)) =
    CSPair (val-satmay-sat-truthify eval1 (CSMSSat sat1))
           (val-satmay-sat-truthify eval2 (CSMSSat sat2))
  val-satmay-sat-truthify eval (CSMSSat (CSNotIntroPair ni sat1 sat2)) =
    abort (val-notintro-not eval ni)
  val-satmay-sat-truthify eval (CSMSSat (CSOrL sat1)) =
    CSOrL (val-satmay-sat-truthify eval (CSMSSat sat1))
  val-satmay-sat-truthify eval (CSMSSat (CSOrR sat2)) =
    CSOrR (val-satmay-sat-truthify eval (CSMSSat sat2))
  val-satmay-sat-truthify eval (CSMSMay CMSUnknown) = CSTruth
  val-satmay-sat-truthify (VInl eval) (CSMSMay (CMSInl msat)) =
    CSInl (val-satmay-sat-truthify eval (CSMSMay msat))
  val-satmay-sat-truthify (VInr eval) (CSMSMay (CMSInr msat)) =
    CSInr (val-satmay-sat-truthify eval (CSMSMay msat))
  val-satmay-sat-truthify (VPair eval1 eval2) (CSMSMay (CMSPairL msat1 sat2)) =
    CSPair (val-satmay-sat-truthify eval1 (CSMSMay msat1))
           (val-satmay-sat-truthify eval2 (CSMSSat sat2))
  val-satmay-sat-truthify (VPair eval1 eval2) (CSMSMay (CMSPairR sat1 msat2)) =
    CSPair (val-satmay-sat-truthify eval1 (CSMSSat sat1))
           (val-satmay-sat-truthify eval2 (CSMSMay msat2))
  val-satmay-sat-truthify (VPair eval1 eval2) (CSMSMay (CMSPair msat1 msat2)) =
    CSPair (val-satmay-sat-truthify eval1 (CSMSMay msat1))
           (val-satmay-sat-truthify eval2 (CSMSMay msat2))
  val-satmay-sat-truthify eval (CSMSMay (CMSOrL msat1 ¬sat2)) =
    CSOrL (val-satmay-sat-truthify eval (CSMSMay msat1))
  val-satmay-sat-truthify eval (CSMSMay (CMSOrR ¬sat1 msat2)) =
    CSOrR (val-satmay-sat-truthify eval (CSMSMay msat2))
  val-satmay-sat-truthify eval (CSMSMay (CMSNotIntro ni ref pos)) =
    abort (val-notintro-not eval ni)
  
  sat-truthify-satmay : ∀{e ξ} →
                        e ⊧ (ξ ◆⊤) →
                        e ⊧̇†? ξ
  sat-truthify-satmay {ξ = ·⊤} sat = CSMSSat CSTruth
  sat-truthify-satmay {ξ = ·?} sat = CSMSMay CMSUnknown
  sat-truthify-satmay {ξ = N n} CSNum = CSMSSat CSNum
  sat-truthify-satmay {ξ = inl ξ} (CSInl sat) = satormay-inl (sat-truthify-satmay sat)
  sat-truthify-satmay {ξ = inr ξ} (CSInr sat) = satormay-inr (sat-truthify-satmay sat)
  sat-truthify-satmay {ξ = ⟨ ξ1 , ξ2 ⟩} (CSPair sat1 sat2) =
    satormay-pair (sat-truthify-satmay sat1) (sat-truthify-satmay sat2)
  sat-truthify-satmay {ξ = ξ1 ∨ ξ2} (CSOrL sat1) =
    satormay-or-l (sat-truthify-satmay sat1)
  sat-truthify-satmay {ξ = ξ1 ∨ ξ2} (CSOrR sat2) =
    satormay-or-r (sat-truthify-satmay sat2)

  val-sat-sat-falsify : ∀{e ξ} →
                        e val →
                        e ⊧̇ ξ →
                        e ⊧ (ξ ◆⊥)
  val-sat-sat-falsify eval CSTruth = CSTruth
  val-sat-sat-falsify eval CSNum = CSNum
  val-sat-sat-falsify (VInl eval) (CSInl sat) = CSInl (val-sat-sat-falsify eval sat)
  val-sat-sat-falsify (VInr eval) (CSInr sat) = CSInr (val-sat-sat-falsify eval sat)
  val-sat-sat-falsify (VPair eval1 eval2) (CSPair sat1 sat2) =
    CSPair (val-sat-sat-falsify eval1 sat1) (val-sat-sat-falsify eval2 sat2)
  val-sat-sat-falsify eval (CSNotIntroPair ni sat1 sat2) = abort (val-notintro-not eval ni)
  val-sat-sat-falsify eval (CSOrL sat1) = CSOrL (val-sat-sat-falsify eval sat1)
  val-sat-sat-falsify eval (CSOrR sat2) = CSOrR (val-sat-sat-falsify eval sat2)
  
  sat-falsify-sat : ∀{e ξ} →
                    e ⊧ (ξ ◆⊥) →
                    e ⊧̇ ξ
  sat-falsify-sat {ξ = ·⊤} sat = CSTruth
  sat-falsify-sat {ξ = N n} CSNum = CSNum
  sat-falsify-sat {ξ = inl ξ} (CSInl sat) = CSInl (sat-falsify-sat sat)
  sat-falsify-sat {ξ = inr ξ} (CSInr sat) = CSInr (sat-falsify-sat sat)
  sat-falsify-sat {ξ = ⟨ ξ1 , ξ2 ⟩} (CSPair sat1 sat2) =
    CSPair (sat-falsify-sat sat1) (sat-falsify-sat sat2)
  sat-falsify-sat {ξ = ξ1 ∨ ξ2} (CSOrL sat1) = CSOrL (sat-falsify-sat sat1)
  sat-falsify-sat {ξ = ξ1 ∨ ξ2} (CSOrR sat2) = CSOrR (sat-falsify-sat sat2)

  
  -- final-sat-val-sat : ∀{ξ τ}

  -- val-sat-final-sat
