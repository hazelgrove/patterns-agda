open import Prelude
open import constraints-core
open import core
open import dynamic-result-judgements
open import notintro-decidable
open import satisfy-decidable
open import statics-core
open import value-result-judgements
open import xrefutable-decidable

module lemmas-satisfy where

  not-maysat-truth : ∀{e} →
                     (e ⊧̇? ·⊤ → ⊥)
  not-maysat-truth (CMSNotIntro _ () _)

  not-maysat-falsity : ∀{e} →
                       (e ⊧̇? ·⊥ → ⊥)
  not-maysat-falsity (CMSNotIntro _ _ ())

  not-satormay-falsity : ∀{e} →
                         (e ⊧̇†? ·⊥ → ⊥)
  not-satormay-falsity (CSMSMay (CMSNotIntro _ _ ()))

  notintro-sat-not-ref : ∀{e ξ} →
                         e notintro →
                         e ⊧̇ ξ →
                         ξ xrefutable →
                         ⊥
  notintro-sat-not-ref ni (CSNotIntroPair ni' sat1 sat2) (RXPairL ref1) =
    notintro-sat-not-ref NVFst sat1 ref1
  notintro-sat-not-ref ni (CSNotIntroPair ni' sat1 sat2) (RXPairR ref2) =
    notintro-sat-not-ref NVSnd sat2 ref2
  notintro-sat-not-ref ni (CSOrL sat1) (RXOr ref1 ref2) =
    notintro-sat-not-ref ni sat1 ref1
  notintro-sat-not-ref ni (CSOrR sat2) (RXOr ref1 ref2) =
    notintro-sat-not-ref ni sat2 ref2

                         
  not-ref-not-pos-not : ∀{ξ} →
                        (ξ xrefutable → ⊥) →
                        (ξ possible → ⊥) →
                        ⊥
  not-ref-not-pos-not {·⊤} ¬ref ¬pos = ¬pos PTruth
  not-ref-not-pos-not {·⊥} ¬ref ¬pos = ¬ref RXFalsity
  not-ref-not-pos-not {·?} ¬ref ¬pos = ¬pos PUnknown
  not-ref-not-pos-not {N n} ¬ref ¬pos = ¬pos PNum
  not-ref-not-pos-not {inl ξ} ¬ref ¬pos = ¬ref RXInl
  not-ref-not-pos-not {inr ξ} ¬ref ¬pos = ¬ref RXInr
  not-ref-not-pos-not {⟨ ξ1 , ξ2 ⟩} ¬ref ¬pos =
    not-ref-not-pos-not (λ ref1 → ¬ref (RXPairL ref1))
                        (λ pos1 →
                           not-ref-not-pos-not (λ ref2 → ¬ref (RXPairR ref2))
                                             (λ pos2 → ¬pos (PPair pos1 pos2)))
  not-ref-not-pos-not {ξ1 ∨ ξ2} ¬ref ¬pos =
    not-ref-not-pos-not (λ ref1 →
                           not-ref-not-pos-not (λ ref2 → ¬ref (RXOr ref1 ref2))
                                               (λ pos2 → ¬pos (POrR pos2)))
                        (λ pos1 → ¬pos (POrL pos1))

  sat-pos : ∀{ξ e} →
            e ⊧̇ ξ →
            ξ possible
  sat-pos CSTruth = PTruth
  sat-pos CSNum = PNum
  sat-pos (CSInl sat) = PInl (sat-pos sat)
  sat-pos (CSInr sat) = PInr (sat-pos sat)
  sat-pos (CSPair sat1 sat2) = PPair (sat-pos sat1) (sat-pos sat2)
  sat-pos (CSNotIntroPair ni sat1 sat2) = PPair (sat-pos sat1) (sat-pos sat2)
  sat-pos (CSOrL sat) = POrL (sat-pos sat)
  sat-pos (CSOrR sat) = POrR (sat-pos sat)

  msat-pos : ∀{ξ e} →
             e ⊧̇? ξ →
             ξ possible
  msat-pos CMSUnknown = PUnknown
  msat-pos (CMSInl msat) = PInl (msat-pos msat)
  msat-pos (CMSInr msat) = PInr (msat-pos msat)
  msat-pos (CMSPairL msat1 sat2) = PPair (msat-pos msat1) (sat-pos sat2)
  msat-pos (CMSPairR sat1 msat2) = PPair (sat-pos sat1) (msat-pos msat2)
  msat-pos (CMSPair msat1 msat2) = PPair (msat-pos msat1) (msat-pos msat2)
  msat-pos (CMSOrL msat1 ¬sat2) = POrL (msat-pos msat1)
  msat-pos (CMSOrR ¬sat1 msat2) = POrR (msat-pos msat2)
  msat-pos (CMSNotIntro ni ref pos) = pos

  satm-pos : ∀{ξ e} →
             e ⊧̇†? ξ →
             ξ possible
  satm-pos (CSMSSat sat) = sat-pos sat
  satm-pos (CSMSMay msat) = msat-pos msat
  
  not-ref-sat : ∀{ξ Γ Δ e τ} →
                ξ :c: τ →
                Γ , Δ ⊢ e :: τ →
                e final →
                (ξ xrefutable → ⊥) →
                e ⊧̇ ξ
  not-ref-sat CTTruth wt fin ¬ref = CSTruth
  not-ref-sat CTFalsity wt fin ¬ref = abort (¬ref RXFalsity)
  not-ref-sat CTUnknown wt fin ¬ref = abort (¬ref RXUnknown)
  not-ref-sat CTNum wt fin ¬ref = abort (¬ref RXNum)
  not-ref-sat (CTInl ct) wt fin ¬ref = abort (¬ref RXInl)
  not-ref-sat (CTInr ct) wt fin ¬ref = abort (¬ref RXInr)
  not-ref-sat {ξ = ⟨ ξ1 , ξ2 ⟩} (CTPair ct1 ct2) wt fin ¬ref
    with xrefutable-dec ξ1
  ... | Inl ref1 = abort (¬ref (RXPairL ref1))
  ... | Inr ¬ref1
    with xrefutable-dec ξ2
  ... | Inl ref2 = abort (¬ref (RXPairR ref2))
  ... | Inr ¬ref2 with wt | fin
  ... | TAVar x | FVal ()
  ... | TAVar x | FIndet ()
  ... | TAAp wt1 wt2 | FIndet ind =
    CSNotIntroPair NVAp
                   (not-ref-sat ct1 (TAFst wt) (FIndet (IFst ind)) ¬ref1)
                   (not-ref-sat ct2 (TASnd wt) (FIndet (ISnd ind)) ¬ref2)
  ... | TAMatchZPre wt' x | FIndet ind =
    CSNotIntroPair NVMatch
                   (not-ref-sat ct1 (TAFst wt) (FIndet (IFst ind)) ¬ref1)
                   (not-ref-sat ct2 (TASnd wt) (FIndet (ISnd ind)) ¬ref2)
  ... | TAMatchNZPre wt' x x₁ x₂ x₃ | FIndet ind =
    CSNotIntroPair NVMatch
                   (not-ref-sat ct1 (TAFst wt) (FIndet (IFst ind)) ¬ref1)
                   (not-ref-sat ct2 (TASnd wt) (FIndet (ISnd ind)) ¬ref2)
  ... | TAFst wt' | FIndet ind =
    CSNotIntroPair NVFst
                   (not-ref-sat ct1 (TAFst wt) (FIndet (IFst ind)) ¬ref1)
                   (not-ref-sat ct2 (TASnd wt) (FIndet (ISnd ind)) ¬ref2)
  ... | TASnd wt' | FIndet ind =
    CSNotIntroPair NVSnd
                   (not-ref-sat ct1 (TAFst wt) (FIndet (IFst ind)) ¬ref1)
                   (not-ref-sat ct2 (TASnd wt) (FIndet (ISnd ind)) ¬ref2)
  ... | TAEHole x | FIndet ind =
    CSNotIntroPair NVEHole
                   (not-ref-sat ct1 (TAFst wt) (FIndet (IFst ind)) ¬ref1)
                   (not-ref-sat ct2 (TASnd wt) (FIndet (ISnd ind)) ¬ref2)
  ... | TANEHole x wt' | FIndet ind = 
    CSNotIntroPair NVNEHole
                   (not-ref-sat ct1 (TAFst wt) (FIndet (IFst ind)) ¬ref1)
                   (not-ref-sat ct2 (TASnd wt) (FIndet (ISnd ind)) ¬ref2)
  ... | TAPair wt1 wt2 | fin
    with pair-final fin
  ... | fin1 , fin2 =
    CSPair (not-ref-sat ct1 wt1 fin1 ¬ref1)
           (not-ref-sat ct2 wt2 fin2 ¬ref2)
  not-ref-sat {ξ = ξ1 ∨ ξ2} (CTOr ct1 ct2) wt fin ¬ref
    with xrefutable-dec ξ1
  ... | Inr ¬ref1 = CSOrL (not-ref-sat ct1 wt fin ¬ref1)
  ... | Inl ref1
    with xrefutable-dec ξ2
  ... | Inr ¬ref2 = CSOrR (not-ref-sat ct2 wt fin ¬ref2)
  ... | Inl ref2 = abort (¬ref (RXOr ref1 ref2))


  notintro-not-sat-ref : ∀{ξ e} →
                         e notintro →
                         (e ⊧̇ ξ → ⊥) →
                         ξ xrefutable
  notintro-not-sat-ref {·⊤} ni ¬sat = abort (¬sat CSTruth)
  notintro-not-sat-ref {·⊥} ni ¬sat = RXFalsity
  notintro-not-sat-ref {·?} ni ¬sat = RXUnknown
  notintro-not-sat-ref {N n} ni ¬sat = RXNum
  notintro-not-sat-ref {inl ξ} ni ¬sat = RXInl
  notintro-not-sat-ref {inr ξ} ni ¬sat = RXInr
  notintro-not-sat-ref {⟨ ξ1 , ξ2 ⟩} {e = e} ni ¬sat
    with satisfy-dec (fst e) ξ1 | satisfy-dec (snd e) ξ2
  ... | Inl sat1 | Inl sat2 =
    abort (¬sat (CSNotIntroPair ni sat1 sat2))
  ... | Inl sat1 | Inr ¬sat2 =
    RXPairR (notintro-not-sat-ref NVSnd ¬sat2)
  ... | Inr ¬sat1 | Inl sat2 =
    RXPairL (notintro-not-sat-ref NVFst ¬sat1)
  ... | Inr ¬sat1 | Inr ¬sat2 =
    RXPairL (notintro-not-sat-ref NVFst ¬sat1)
  notintro-not-sat-ref {ξ1 ∨ ξ2} ni ¬sat =
    RXOr (notintro-not-sat-ref ni (λ sat1 → ¬sat (CSOrL sat1)))
         (notintro-not-sat-ref ni (λ sat2 → ¬sat (CSOrR sat2)))

  notintro-msat-ref : ∀{ξ e} →
                      e notintro →
                      e ⊧̇? ξ →
                      ξ xrefutable
  notintro-msat-ref ni CMSUnknown = RXUnknown
  notintro-msat-ref ni (CMSInl msat) = RXInl
  notintro-msat-ref ni (CMSInr msat) = RXInr
  notintro-msat-ref () (CMSPairL _ _)
  notintro-msat-ref () (CMSPairR _ _)
  notintro-msat-ref () (CMSPair msat1 msat2)
  notintro-msat-ref ni (CMSOrL msat1 ¬sat2) =
    RXOr (notintro-msat-ref ni msat1) (notintro-not-sat-ref ni ¬sat2)
  notintro-msat-ref ni (CMSOrR ¬sat1 msat2) =
    RXOr (notintro-not-sat-ref ni ¬sat1) (notintro-msat-ref ni msat2)
  notintro-msat-ref ni (CMSNotIntro ni' ref pos) = ref
