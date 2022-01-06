open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import freshness
open import lemmas-freshness
open import lemmas-satisfy
open import notintro-decidable
open import patterns-core
open import result-judgements
open import satisfy-decidable
open import statics-core
open import type-assignment-unicity
open import value-judgements
open import weakening

module lemmas-values where
  values-same-type : ∀{e e' Δ τ} →
                     e' ∈[ Δ ]values e →
                     ∅ , Δ ⊢ e :: τ →
                     ∅ , Δ ⊢ e' :: τ
  values-same-type (IVVal eval wt₁) wt = wt
  values-same-type (IVIndet ni wt₁ eval' wt₁') wt
    with expr-type-unicity wt wt₁
  ... | refl = wt₁'
  values-same-type (IVInl ind (TAInl wt₁) vals) (TAInl wt)
    with expr-type-unicity wt wt₁
  ... | refl
    with values-same-type vals wt₁
  ... | wt₁' = TAInl wt₁'
  values-same-type (IVInr ind (TAInr wt₁) vals) (TAInr wt)
    with expr-type-unicity wt wt₁
  ... | refl
    with values-same-type vals wt₁
  ... | wt₁' = TAInr wt₁'
  values-same-type (IVPair ind (TAPair wt1₁ wt2₁) vals1 vals2) (TAPair wt1 wt2)
    with expr-type-unicity wt1 wt1₁ | expr-type-unicity wt2 wt2₁
  ... | refl | refl
    with values-same-type vals1 wt1₁ | values-same-type vals2 wt2₁
  ... | wt1₁' | wt2₁' = TAPair wt1₁' wt2₁'

  values-val : ∀{e e' Δ} →
               e' ∈[ Δ ]values e →
               e' val
  values-val (IVVal eval wt) = eval
  values-val (IVIndet ni wt eval' wt') = eval'
  values-val (IVInl ind wt vals) = VInl (values-val vals)
  values-val (IVInr ind wt vals) = VInr (values-val vals)
  values-val (IVPair ind wt vals1 vals2) =
    VPair (values-val vals1) (values-val vals2)

  type-has-val : (τ : htyp) →
                 (Δ : tctx) →
                 Σ[ e ∈ ihexp ] (e val × (∅ , Δ ⊢ e :: τ))
  type-has-val num Δ = N 0 , VNum , TANum
  type-has-val (τ1 ==> τ2) Δ
    with type-has-val τ2 Δ
  ... | e' , eval' , wt'
    with exists-fresh e'
  ... | x , frsh =
    (·λ x ·[ τ1 ] e') , VLam , TALam refl (weaken-ta-Γ frsh wt')
  type-has-val (τ1 ⊕ τ2) Δ
    with type-has-val τ1 Δ | type-has-val τ2 Δ
  ... | e1 , eval1 , wt1 | e2 , eval2 , wt2 =
    inl τ2 e1 , VInl eval1 , TAInl wt1
  type-has-val (τ1 ⊠ τ2) Δ
    with type-has-val τ1 Δ | type-has-val τ2 Δ
  ... | e1 , eval1 , wt1 | e2 , eval2 , wt2 =
    ⟨ e1 , e2 ⟩ , VPair eval1 eval2 , TAPair wt1 wt2
  
  indet-has-values : ∀{e Δ τ} →
                     e indet →
                     ∅ , Δ ⊢ e :: τ →
                     Σ[ e' ∈ ihexp ] (e' ∈[ Δ ]values e)
  indet-has-values {Δ = Δ} {τ = τ} (IAp ind1 fin2) (TAAp wt1 wt2)
    with type-has-val τ Δ
  ... | e , eval , ewt = e , IVIndet NVAp (TAAp wt1 wt2) eval ewt
  indet-has-values (IInl ind) (TAInl wt)
    with indet-has-values ind wt
  ... | e' , evals = inl _ e' , IVInl (IInl ind) (TAInl wt) evals
  indet-has-values (IInr ind) (TAInr wt)
    with indet-has-values ind wt
  ... | e' , evals = inr _ e' , IVInr (IInr ind) (TAInr wt) evals
  indet-has-values {Δ = Δ} {τ = τ} (IMatch fin mp) wt
    with type-has-val τ Δ
  ... | e , eval , ewt = e , IVIndet NVMatch wt eval ewt
  indet-has-values {e = ⟨ e1 , e2 ⟩} (IPairL ind1 val2) (TAPair wt1 wt2)
    with indet-has-values ind1 wt1
  ... | e1' , e1vals =
    ⟨ e1' , e2 ⟩ ,
    IVPair (IPairL ind1 val2) (TAPair wt1 wt2) e1vals (IVVal val2 wt2)
  indet-has-values {e = ⟨ e1 , e2 ⟩} (IPairR val1 ind2) (TAPair wt1 wt2)
    with indet-has-values ind2 wt2
  ... | e2' , e2vals = 
    ⟨ e1 , e2' ⟩ ,
    IVPair (IPairR val1 ind2) (TAPair wt1 wt2) (IVVal val1 wt1) e2vals
  indet-has-values {e = ⟨ e1 , e2 ⟩} (IPair ind1 ind2) (TAPair wt1 wt2)
    with indet-has-values ind1 wt1 | indet-has-values ind2 wt2
  ... | e1' , e1vals | e2' , e2vals =
    ⟨ e1' , e2' ⟩ ,
    IVPair (IPair ind1 ind2) (TAPair wt1 wt2) e1vals e2vals
  indet-has-values {Δ = Δ} {τ = τ} (IFst ind1) wt
    with type-has-val τ Δ
  ... | e , eval , ewt = e , IVIndet NVFst wt eval ewt
  indet-has-values {Δ = Δ} {τ = τ} (ISnd ind2) wt
    with type-has-val τ Δ
  ... | e , eval , ewt = e , IVIndet NVSnd wt eval ewt
  indet-has-values {Δ = Δ} {τ = τ} IEHole wt
    with type-has-val τ Δ
  ... | e , eval , ewt = e , IVIndet NVEHole wt eval ewt
  indet-has-values {Δ = Δ} {τ = τ} (INEHole x) wt
    with type-has-val τ Δ
  ... | e , eval , ewt = e , IVIndet NVNEHole wt eval ewt

  indet-values-not-satormay : ∀{e Δ τ ξ e'} →
                             e indet →
                             e' ∈[ Δ ]values e →
                             ∅ , Δ ⊢ e :: τ →
                             ξ :c: τ →
                             (e ⊧̇†? ξ → ⊥) →
                             e' ⊧̇†? ξ →
                             ⊥
  indet-values-not-satormay ind vals wt CTTruth ¬satm satm' =
    ¬satm (CSMSSat CSTruth)
  indet-values-not-satormay ind vals wt CTFalsity ¬satm
                            (CSMSMay (CMSNotIntro _ _ ()))
  indet-values-not-satormay ind vals wt CTUnknown ¬satm satm' =
    ¬satm (CSMSMay CMSUnknown)
  indet-values-not-satormay (IAp ind1 fin2) vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVAp RXNum PNum))
  indet-values-not-satormay (IMatch fin mp) vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVMatch RXNum PNum))
  indet-values-not-satormay (IFst ind) vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVFst RXNum PNum))
  indet-values-not-satormay (ISnd ind) vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVSnd RXNum PNum))
  indet-values-not-satormay IEHole vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVEHole RXNum PNum))
  indet-values-not-satormay (INEHole fin) vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVNEHole RXNum PNum))
  indet-values-not-satormay (IAp ind1 fin2) vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVAp RXInl (satormay-pos satm')))
  indet-values-not-satormay (IInl ind) (IVVal eval wt₁) (TAInl wt)
                            (CTInl ct) ¬satm satm' = ¬satm satm'
  indet-values-not-satormay (IInl ind) (IVInl ind₁ wt₁ vals) (TAInl wt)
                            (CTInl ct) ¬satm satm' =
    indet-values-not-satormay ind vals wt ct
                              (λ satm → ¬satm (satormay-inl satm))
                              (inl-satormay satm')
  indet-values-not-satormay (IInr ind) (IVVal eval wt₁) (TAInr wt)
                            (CTInl ct) ¬satm (CSMSMay (CMSNotIntro () _ _))
  indet-values-not-satormay (IInr ind) (IVInr ind₁ wt₁ vals) (TAInr wt)
                            (CTInl ct) ¬satm (CSMSMay (CMSNotIntro () _ _))
  indet-values-not-satormay (IMatch fin mp) vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVMatch RXInl (satormay-pos satm')))
  indet-values-not-satormay (IFst ind) vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVFst RXInl (satormay-pos satm')))
  indet-values-not-satormay (ISnd ind) vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVSnd RXInl (satormay-pos satm')))
  indet-values-not-satormay IEHole vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVEHole RXInl (satormay-pos satm')))
  indet-values-not-satormay (INEHole x) vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVNEHole RXInl (satormay-pos satm')))
  indet-values-not-satormay (IAp ind x) vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVAp RXInr (satormay-pos satm')))
  indet-values-not-satormay (IInl ind) (IVVal eval wt₁) (TAInl wt)
                            (CTInr ct) ¬satm (CSMSMay (CMSNotIntro () _ _))
  indet-values-not-satormay (IInl ind) (IVInl ind₁ wt₁ vals) (TAInl wt)
                            (CTInr ct) ¬satm (CSMSMay (CMSNotIntro () _ _))
  indet-values-not-satormay (IInr ind) (IVVal eval wt₁) (TAInr wt)
                            (CTInr ct) ¬satm satm' = ¬satm satm'
  indet-values-not-satormay (IInr ind) (IVInr ind₁ wt₁ vals) (TAInr wt)
                            (CTInr ct) ¬satm satm' =
    indet-values-not-satormay ind vals wt ct
                              (λ satm → ¬satm (satormay-inr satm))
                              (inr-satormay satm')
  indet-values-not-satormay (IMatch x x₁) vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVMatch RXInr (satormay-pos satm')))
  indet-values-not-satormay (IFst ind) vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVFst RXInr (satormay-pos satm')))
  indet-values-not-satormay (ISnd ind) vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVSnd RXInr (satormay-pos satm')))
  indet-values-not-satormay IEHole vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVEHole RXInr (satormay-pos satm')))
  indet-values-not-satormay (INEHole x) vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVNEHole RXInr (satormay-pos satm')))
  indet-values-not-satormay {e = e} {ξ = ⟨ ξ1 , ξ2 ⟩} ind vals wt
                            (CTPair ct1 ct2) ¬satm satm'
    with notintro-dec e
  ... | Inl ni 
    with satisfyormay-dec (fst e) ξ1
  ... | Inl satm1
    with satisfyormay-dec (snd e) ξ2
  ... | Inl satm2
    with satm1
  ... | CSMSMay msat1 =
    ¬satm (CSMSMay (CMSNotIntro ni
                                (RXPairL (notintro-maysat-ref NVFst msat1))
                                (satormay-pos satm')))
  ... | CSMSSat sat1
    with satm2
  ... | CSMSMay msat2 =
    ¬satm (CSMSMay (CMSNotIntro ni
                                (RXPairR (notintro-maysat-ref NVSnd msat2))
                                (satormay-pos satm')))
  ... | CSMSSat sat2 = ¬satm (CSMSSat (CSNotIntroPair ni sat1 sat2))
  
  indet-values-not-satormay {e = e} {ξ = ⟨ ξ1 , ξ2 ⟩} ind vals wt
                            (CTPair ct1 ct2) ¬satm satm' 
      | Inl ni | Inl satm1 | Inr ¬satm2
    with vals
  ... | IVVal eval wt₁ = val-notintro-not eval ni
  ... | IVIndet ni₁ wt₁ eval' wt'
    with expr-type-unicity wt wt₁
  ... | refl with eval'
  ... | VPair val1 val2
    with wt'
  ... | TAPair wt1' wt2' =
    indet-values-not-satormay (ISnd ind) (IVIndet NVSnd (TASnd wt) val2 wt2')
                              (TASnd wt) ct2 ¬satm2 (π2 (pair-satormay satm'))
  indet-values-not-satormay {e = e} {ξ = ⟨ ξ1 , ξ2 ⟩} ind vals wt
                            (CTPair ct1 ct2) ¬satm satm' 
      | Inl ni | Inr ¬satm1
    with vals
  ... | IVVal eval wt₁ = val-notintro-not eval ni
  ... | IVIndet ni₁ wt₁ eval' wt'
    with expr-type-unicity wt wt₁
  ... | refl with eval'
  ... | VPair val1 val2
    with wt'
  ... | TAPair wt1' wt2' =
    indet-values-not-satormay (IFst ind) (IVIndet NVFst (TAFst wt) val1 wt1')
                              (TAFst wt) ct1 ¬satm1 (π1 (pair-satormay satm'))
  indet-values-not-satormay ind vals wt (CTPair ct1 ct2) ¬satm satm'
      | Inr ¬ni
    with vals
  ... | IVVal _ _ = ¬satm satm'
  ... | IVIndet ni _ _ _ = ¬ni ni
  ... | IVPair _ _ vals1 vals2
    with wt
  ... | TAPair wt1 wt2
    with ind
  indet-values-not-satormay {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                            ind vals wt (CTPair ct1 ct2) ¬satm satm'
      | Inr ¬ni | IVPair _ _ vals1 vals2 | TAPair wt1 wt2 | IPair ind1 ind2
    with satisfyormay-dec e1 ξ1
  ... | Inr ¬sat1 =
    indet-values-not-satormay ind1 vals1 wt1 ct1 ¬sat1
                              (π1 (pair-satormay satm'))
  ... | Inl sat1
    with satisfyormay-dec e2 ξ2
  ... | Inl sat2 = ¬satm (satormay-pair sat1 sat2)
  ... | Inr ¬sat2 =
    indet-values-not-satormay ind2 vals2 wt2 ct2 ¬sat2
                              (π2 (pair-satormay satm'))
  indet-values-not-satormay {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                            ind vals wt (CTPair ct1 ct2) ¬satm satm'
      | Inr ¬ni | IVPair _ _ vals1 vals2 | TAPair wt1 wt2 | IPairL ind1 val2
    with satisfyormay-dec e1 ξ1
  ... | Inr ¬sat1 = 
    indet-values-not-satormay ind1 vals1 wt1 ct1 ¬sat1
                              (π1 (pair-satormay satm'))
  indet-values-not-satormay {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                            ind vals wt (CTPair ct1 ct2) ¬satm satm'
      | Inr ¬ni | IVPair _ _ vals1 vals2 | TAPair wt1 wt2 | IPairL ind1 val2
      | Inl sat1
    with satisfyormay-dec e2 ξ2
  ... | Inl sat2 = ¬satm (satormay-pair sat1 sat2)
  ... | Inr ¬sat2
    with vals2
  ... | IVVal _ _ = ¬sat2 (π2 (pair-satormay satm'))
  ... | IVIndet ni2 _ _ _ = val-notintro-not val2 ni2
  ... | IVInl ind2 _ _ = val-indet-not val2 ind2
  ... | IVInr ind2 _ _ = val-indet-not val2 ind2
  ... | IVPair ind2 _ _ _ = val-indet-not val2 ind2
  
  indet-values-not-satormay {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                            ind vals wt (CTPair ct1 ct2) ¬satm satm'
      | Inr ¬ni | IVPair _ _ vals1 vals2 |  TAPair wt1 wt2 | IPairR val1 ind2
    with satisfyormay-dec e2 ξ2
  ... | Inr ¬sat2 =
    indet-values-not-satormay ind2 vals2 wt2 ct2 ¬sat2
                              (π2 (pair-satormay satm'))
  ... | Inl sat2
    with satisfyormay-dec e1 ξ1
  ... | Inl sat1 = ¬satm (satormay-pair sat1 sat2)
  ... | Inr ¬sat1
    with vals1
  ... | IVVal _ _ = ¬sat1 (π1 (pair-satormay satm'))
  ... | IVIndet ni1 _ _ _ = val-notintro-not val1 ni1
  ... | IVInl ind1 _ _ = val-indet-not val1 ind1
  ... | IVInr ind1 _ _ = val-indet-not val1 ind1
  ... | IVPair ind1 _ _ _ = val-indet-not val1 ind1
  indet-values-not-satormay ind vals wt (CTOr ct1 ct2) ¬satm satm'
    with or-satormay satm'
  ... | Inl satm1' =
    indet-values-not-satormay ind vals wt ct1
                              (λ satm1 → ¬satm (satormay-or-l satm1)) satm1'
  ... | Inr satm2' =
    indet-values-not-satormay ind vals wt ct2
                              (λ satm2 → ¬satm (satormay-or-r satm2)) satm2'
  
