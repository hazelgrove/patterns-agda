open import Prelude
open import constraints-core
open import contexts
open import core
open import lemmas-patterns
open import matching-determinism
open import notintro-decidable
open import patterns-core
open import result-judgements
open import satisfy-exclusive
open import statics-core
open import substitution-env

module matching-coherence where
  sat-mat : ∀{e Δe τ p ξ Γ Δ} →
            e final →
            ∅ , Δe ⊢ e :: τ →
            p :: τ [ ξ ]⊣ Γ , Δ →
            e ⊧̇ ξ →
            Σ[ θ ∈ env ] e ▹ p ⊣ θ
  sat-mat {e = e} fin wt (PTVar {x = x}) sat =
    Subst e x (Id ∅) , MVar
  sat-mat fin wt PTNum CSNum = Id ∅ , MNum
  sat-mat fin (TAInl wt) (PTInl pt) (CSInl sat)
    with sat-mat (inl-final fin) wt pt sat
  ... | θ , mat = θ , MInl mat
  sat-mat fin (TAInr wt) (PTInr pt) (CSInr sat)
    with sat-mat (inr-final fin) wt pt sat
  ... | θ , mat = θ , MInr mat
  sat-mat {e = e} fin wt (PTPair disj disjh pt1 pt2) sat
    with notintro-dec e
  ... | Inl ni
    with sat
  ... | CSNotIntroPair ni sat1 sat2
    with sat-mat (FIndet (IFst (final-notintro-indet fin ni)))
                 (TAFst wt) pt1 sat1 |
         sat-mat (FIndet (ISnd (final-notintro-indet fin ni)))
                 (TASnd wt) pt2 sat2
  ... | θ1 , mat1 | θ2 , mat2 =
    θ1 ⊎ θ2 , MNotIntroPair ni mat1 mat2
  sat-mat {e = e} fin wt (PTPair disj disjh pt1 pt2) sat
      | Inr ¬ni
    with sat
  ... | CSNotIntroPair ni sat1 sat2 = abort (¬ni ni)
  ... | CSPair sat1 sat2
    with wt
  ... | TAPair wt1 wt2 
    with sat-mat (π1 (pair-final fin)) wt1 pt1 sat1 |
         sat-mat (π2 (pair-final fin)) wt2 pt2 sat2
  ... | θ1 , mat1 | θ2 , mat2 = θ1 ⊎ θ2 , MPair mat1 mat2
  sat-mat fin wt PTWild sat = Id ∅ , MWild
  
  mat-sat : ∀{e Δe τ p ξ Γ Δ θ} →
            e final →
            ∅ , Δe ⊢ e :: τ →
            p :: τ [ ξ ]⊣ Γ , Δ →
            e ▹ p ⊣ θ →
            e ⊧̇ ξ
  mat-sat fin wt PTVar MVar = CSTruth
  mat-sat fin wt PTNum MNum = CSNum
  mat-sat fin (TAInl wt) (PTInl pt) (MInl mat)
    with mat-sat (inl-final fin) wt pt mat
  ... | sat = CSInl sat
  mat-sat fin (TAInr wt) (PTInr pt) (MInr mat)
    with mat-sat (inr-final fin) wt pt mat
  ... | sat = CSInr sat
  mat-sat {e = e} fin wt (PTPair disj disjh pt1 pt2) mat
    with notintro-dec e
  ... | Inl ni
    with mat
  ... | MNotIntroPair ni mat1 mat2
    with mat-sat (FIndet (IFst (final-notintro-indet fin ni)))
                 (TAFst wt) pt1 mat1 |
         mat-sat (FIndet (ISnd (final-notintro-indet fin ni)))
                 (TASnd wt) pt2 mat2
  ... | sat1 | sat2 = CSNotIntroPair ni sat1 sat2
  mat-sat {e = e} fin wt (PTPair disj disjh pt1 pt2) mat
      | Inr ¬ni
    with mat
  ... | MNotIntroPair ni mat1 mat2 = abort (¬ni ni)
  ... | MPair mat1 mat2
    with wt
  ... | TAPair wt1 wt2
    with mat-sat (π1 (pair-final fin)) wt1 pt1 mat1 |
         mat-sat (π2 (pair-final fin)) wt2 pt2 mat2
  ... | sat1 | sat2 = CSPair sat1 sat2
  mat-sat fin wt PTWild MWild = CSTruth
  
  maysat-maymat : ∀{e Δe τ p ξ Γ Δ} →
                  e final →
                  ∅ , Δe ⊢ e :: τ →
                  p :: τ [ ξ ]⊣ Γ , Δ →
                  e ⊧̇? ξ →
                  e ?▹ p
  maysat-maymat fin wt PTVar (CMSNotIntro ni () pos)
  maysat-maymat fin wt PTNum (CMSNotIntro ni ref pos) =
    MMNotIntro ni RNum
  maysat-maymat {e = e} fin wt (PTInl pt) msat
    with notintro-dec e
  ... | Inl ni
    with msat
  ... | CMSNotIntro ni ref pos = MMNotIntro ni RInl
  maysat-maymat {e = e} fin wt (PTInl pt) msat
      | Inr ¬ni
    with msat
  ... | CMSNotIntro ni ref pos = abort (¬ni ni)
  ... | CMSInl msat₁
    with wt
  ... | TAInl wt₁
    with maysat-maymat (inl-final fin) wt₁ pt msat₁
  ... | mmat = MMInl mmat
  maysat-maymat {e = e} fin wt (PTInr pt) msat
    with notintro-dec e
  ... | Inl ni
    with msat
  ... | CMSNotIntro ni ref pos = MMNotIntro ni RInr
  maysat-maymat {e = e} fin wt (PTInr pt) msat
      | Inr ¬ni
    with msat
  ... | CMSNotIntro ni ref pos = abort (¬ni ni)
  ... | CMSInr msat₁
    with wt
  ... | TAInr wt₁
    with maysat-maymat (inr-final fin) wt₁ pt msat₁
  ... | mmat = MMInr mmat
  maysat-maymat {e = e} fin wt (PTPair disj disjh pt1 pt2) msat
    with notintro-dec e
  ... | Inl ni
    with msat
  ... | CMSNotIntro ni (RXPairL ref1) pos =
    MMNotIntro ni (RPairL (constr-ref-pattern-ref pt1 ref1))
  ... | CMSNotIntro ni (RXPairR ref2) pos =
    MMNotIntro ni (RPairR (constr-ref-pattern-ref pt2 ref2))
  maysat-maymat {e = e} fin wt (PTPair disj disjh pt1 pt2) msat
      | Inr ¬ni
    with msat
  ... | CMSNotIntro ni ref pos = abort (¬ni ni)
  maysat-maymat {e = e} fin (TAPair wt1 wt2) (PTPair disj disjh pt1 pt2) msat | Inr ¬ni
      | CMSPairL msat1 sat2
    with maysat-maymat (π1 (pair-final fin)) wt1 pt1 msat1 |
         sat-mat (π2 (pair-final fin)) wt2 pt2 sat2
  ... | mmat1 | θ2 , mat2 = MMPairL mmat1 mat2
  maysat-maymat {e = e} fin (TAPair wt1 wt2) (PTPair disj disjh pt1 pt2) msat | Inr ¬ni
      | CMSPairR sat1 msat2
    with sat-mat (π1 (pair-final fin)) wt1 pt1 sat1 |
         maysat-maymat (π2 (pair-final fin)) wt2 pt2 msat2
  ... | θ1 , mat1 | mmat2 = MMPairR mat1 mmat2
  maysat-maymat {e = e} fin (TAPair wt1 wt2) (PTPair disj disjh pt1 pt2) msat | Inr ¬ni
     | CMSPair msat1 msat2
    with maysat-maymat (π1 (pair-final fin)) wt1 pt1 msat1 |
         maysat-maymat (π2 (pair-final fin)) wt2 pt2 msat2
  ... | mmat1 | mmat2 = MMPair mmat1 mmat2
  maysat-maymat fin wt PTEHole msat = MMEHole
  maysat-maymat fin wt (PTNEHole pt x) msat = MMNEHole
  maysat-maymat fin wt PTWild (CMSNotIntro ni () pos)
  
  maymat-maysat : ∀{e Δe τ p ξ Γ Δ} →
                  e final →
                  ∅ , Δe ⊢ e :: τ →
                  p :: τ [ ξ ]⊣ Γ , Δ →
                  e ?▹ p →
                  e ⊧̇? ξ
  maymat-maysat fin wt PTVar (MMNotIntro ni ())
  maymat-maysat fin wt PTNum (MMNotIntro ni ref) =
    CMSNotIntro ni RXNum PNum
  maymat-maysat {e = e} fin wt (PTInl pt) mmat
    with notintro-dec e
  ... | Inl ni
    with mmat
  ... | MMNotIntro ni ref =
    CMSNotIntro ni RXInl (PInl (pattern-constr-pos pt))
  maymat-maysat {e = e} fin wt (PTInl pt) mmat
      | Inr ¬ni
    with mmat
  ... | MMNotIntro ni rf = abort (¬ni ni)
  ... | MMInl mmat₁
    with wt
  ... | TAInl wt₁
    with maymat-maysat (inl-final fin) wt₁ pt mmat₁
  ... | msat = CMSInl msat
  maymat-maysat {e = e} fin wt (PTInr pt) mmat
    with notintro-dec e
  ... | Inl ni
    with mmat
  ... | MMNotIntro ni ref =
    CMSNotIntro ni RXInr (PInr (pattern-constr-pos pt))
  maymat-maysat {e = e} fin wt (PTInr pt) mmat
      | Inr ¬ni
    with mmat
  ... | MMNotIntro ni rf = abort (¬ni ni)
  ... | MMInr mmat₁
    with wt
  ... | TAInr wt₁
    with maymat-maysat (inr-final fin) wt₁ pt mmat₁
  ... | msat = CMSInr msat
  maymat-maysat {e = e} fin wt (PTPair disj disjh pt1 pt2) mmat
    with notintro-dec e
  ... | Inl ni
    with mmat
  ... | MMPairL msat1 sat2 = abort (contra ni λ ())
  ... | MMPairR sat1 msat2 = abort (contra ni λ ())
  ... | MMPair msat1 msat2 = abort (contra ni λ ())
  ... | MMNotIntro ni (RPairL ref1) =
    CMSNotIntro ni (RXPairL (pattern-ref-constr-ref pt1 ref1))
                (PPair (pattern-constr-pos pt1) (pattern-constr-pos pt2))
  ... | MMNotIntro ni (RPairR ref2) =
    CMSNotIntro ni (RXPairR (pattern-ref-constr-ref pt2 ref2))
                (PPair (pattern-constr-pos pt1) (pattern-constr-pos pt2))
  maymat-maysat {e = e} fin wt (PTPair disj disjh pt1 pt2) mmat
      | Inr ¬ni
    with mmat
  ... | MMNotIntro ni ref = abort (¬ni ni)
  maymat-maysat {e = e} fin (TAPair wt1 wt2) (PTPair disj disjh pt1 pt2) mmat | Inr ¬ni
      | MMPairL mmat1 mat2
    with maymat-maysat (π1 (pair-final fin)) wt1 pt1 mmat1 |
         mat-sat (π2 (pair-final fin)) wt2 pt2 mat2
  ... | msat1 | sat2 = CMSPairL msat1 sat2
  maymat-maysat {e = e} fin (TAPair wt1 wt2) (PTPair disj disjh pt1 pt2) mmat | Inr ¬ni
      | MMPairR mat1 mmat2
    with mat-sat (π1 (pair-final fin)) wt1 pt1 mat1 |
         maymat-maysat (π2 (pair-final fin)) wt2 pt2 mmat2
  ... | sat1 | msat2 = CMSPairR sat1 msat2
  maymat-maysat {e = e} fin (TAPair wt1 wt2) (PTPair disj disjh pt1 pt2) mmat | Inr ¬ni
      | MMPair mmat1 mmat2
    with maymat-maysat (π1 (pair-final fin)) wt1 pt1 mmat1 |
         maymat-maysat (π2 (pair-final fin)) wt2 pt2 mmat2
  ... | msat1 | msat2 = CMSPair msat1 msat2
  maymat-maysat fin wt PTEHole mmat = CMSUnknown
  maymat-maysat fin wt (PTNEHole pt x) mmat = CMSUnknown
  maymat-maysat fin wt PTWild (MMNotIntro ni ())

  not-satormay-notmat : ∀{e Δe τ p ξ Γ Δ} →
                  e final →
                  ∅ , Δe ⊢ e :: τ →
                  p :: τ [ ξ ]⊣ Γ , Δ →
                  (e ⊧̇†? ξ → ⊥) →
                  e ⊥▹ p
  not-satormay-notmat fin wt pt ¬satm
    with satisfy-exclusive (pattern-constr-same-type pt) wt fin
  ... | Satisfy sat ¬msat satm = abort (¬satm satm)
  ... | MaySatisfy ¬sat msat satm = abort (¬satm satm)
  ... | NotSatisfy ¬sat ¬msat ¬satm
    with matching-det fin wt pt
  ... | Match (θ , mat) ¬mmat ¬nmat =
    abort (¬sat (mat-sat fin wt pt mat))
  ... | MayMatch ¬mat mmat ¬nmat =
    abort (¬msat (maymat-maysat fin wt pt mmat))
  ... | NotMatch ¬mat ¬mmat nmat = nmat
  
  notmat-not-satormay : ∀{e Δe τ p ξ Γ Δ} →
                        e final →
                        ∅ , Δe ⊢ e :: τ →
                        p :: τ [ ξ ]⊣ Γ , Δ →
                        e ⊥▹ p →
                        e ⊧̇†? ξ →
                        ⊥
  notmat-not-satormay fin wt pt nmat
    with matching-det fin wt pt
  ... | Match mat ¬mmat ¬nmat = abort (¬nmat nmat)
  ... | MayMatch ¬mat mmat ¬nmat = abort (¬nmat nmat)
  ... | NotMatch ¬mat ¬mmat nmat
    with satisfy-exclusive (pattern-constr-same-type pt) wt fin
  ... | Satisfy sat ¬msat satm =
    abort (¬mat (sat-mat fin wt pt sat))
  ... | MaySatisfy ¬sat msat satm =
    abort (¬mmat (maysat-maymat fin wt pt msat))
  ... | NotSatisfy ¬sat ¬msat ¬satm = ¬satm
