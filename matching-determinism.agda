open import Nat
open import Prelude
open import contexts
open import core
open import notintro-decidable
open import patterns-core
open import result-judgements
open import statics-core
open import substitution-env

module matching-determinism where

  data DetMatch (e : ihexp) (p : pattrn) : Set where
       Match    : (Σ[ θ ∈ env ] e ▹ p ⊣ θ) →
                  (e ?▹ p → ⊥) →
                  (e ⊥▹ p → ⊥) →
                  DetMatch e p
       MayMatch : ((Σ[ θ ∈ env ] e ▹ p ⊣ θ) → ⊥) →
                  (e ?▹ p) →
                  (e ⊥▹ p → ⊥) →
                  DetMatch e p
       NotMatch : ((Σ[ θ ∈ env ] e ▹ p ⊣ θ) → ⊥) →
                  (e ?▹ p → ⊥) →
                  (e ⊥▹ p) →
                  DetMatch e p
       
  matching-det : ∀{e Δe τ p ξ Γ Δ} →
                 e final →
                 ∅ , Δe ⊢ e :: τ →
                 p :: τ [ ξ ]⊣ Γ , Δ →
                 DetMatch e p
  matching-det {e = e} {p = p} fin wt (PTVar {x = x}) =
    Match (Subst e x (Id ∅) , MVar)
          (λ{(MMNotIntro ni ())})
          (λ ())
  matching-det {e = e} {p = p} fin wt (PTNum {n = n})
    with notintro-dec e
  ... | Inl ni =
    MayMatch (λ{(_ , MNum) → contra ni λ ()})
             (MMNotIntro ni RNum)
             (λ{(NMNum _) → contra ni λ ()})
  ... | Inr ¬ni
    with wt
  ... | TAAp _ _ = abort (¬ni NVAp)
  ... | TAMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TAMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TAFst _ = abort (¬ni NVFst)
  ... | TASnd _ = abort (¬ni NVSnd)
  ... | TAEHole _ = abort (¬ni NVEHole)
  ... | TANEHole _ _ = abort (¬ni NVNEHole)
  ... | TANum {n = m}
    with natEQ m n
  ... | Inl refl =
    Match (Id ∅ , MNum)
          (λ{(MMNotIntro () _)})
          (λ{(NMNum n≠n) → n≠n refl})
  ... | Inr m≠n =
    NotMatch (λ{(_ , MNum) → m≠n refl})
             (λ{(MMNotIntro () _)})
             (NMNum m≠n)
  matching-det {e = e} {p = p} fin wt (PTInl pt)
    with notintro-dec e
  ... | Inl ni =
    MayMatch (λ{(θ , MInl mat) → contra ni λ ()})
             (MMNotIntro ni RInl)
             (λ{NMConfL → contra ni λ ()
              ; (NMInl nmat) → contra ni λ ()})
  ... | Inr ¬ni
    with wt
  ... | TAAp _ _ = abort (¬ni NVAp)
  ... | TAMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TAMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TAFst _ = abort (¬ni NVFst)
  ... | TASnd _ = abort (¬ni NVSnd)
  ... | TAEHole _ = abort (¬ni NVEHole)
  ... | TANEHole _ _ = abort (¬ni NVNEHole)
  ... | TAInr wt₁ =
    NotMatch (λ ()) (λ{(MMNotIntro () _)}) NMConfL
  ... | TAInl wt₁
    with matching-det (inl-final fin) wt₁ pt
  ... | Match (θ , mat) ¬mmat ¬nnat =
    Match (θ , (MInl mat))
          (λ{(MMInl mmat) → ¬mmat mmat})
          (λ{(NMInl nmat) → ¬nnat nmat})
  ... | MayMatch ¬mat mmat ¬nnat =
    MayMatch (λ{(θ , MInl mat) → ¬mat (θ , mat)})
             (MMInl mmat)
             (λ{(NMInl nnat) → ¬nnat nnat})
  ... | NotMatch ¬mat ¬mmat nnat =
    NotMatch (λ{(θ , MInl mat) → ¬mat (θ , mat)})
             (λ{(MMInl mmat) → ¬mmat mmat})
             (NMInl nnat)
  matching-det {e = e} {p = p} fin wt (PTInr pt)
    with notintro-dec e
  ... | Inl ni =
    MayMatch (λ{(θ , MInr mat) → contra ni λ ()})
             (MMNotIntro ni RInr)
             (λ{NMConfR → contra ni λ () ;
               (NMInr nmat) → contra ni λ ()})
  ... | Inr ¬ni
    with wt
  ... | TAAp _ _ = abort (¬ni NVAp)
  ... | TAMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TAMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TAFst _ = abort (¬ni NVFst)
  ... | TASnd _ = abort (¬ni NVSnd)
  ... | TAEHole _ = abort (¬ni NVEHole)
  ... | TANEHole _ _ = abort (¬ni NVNEHole)
  ... | TAInl wt₁ =
    NotMatch (λ ()) (λ{(MMNotIntro () _)}) NMConfR
  ... | TAInr wt₁
    with matching-det (inr-final fin) wt₁ pt
  ... | Match (θ , mat) ¬mmat ¬nnat =
    Match (θ , MInr mat)
          (λ{(MMInr mmat) → ¬mmat mmat})
          (λ{(NMInr nmat) → ¬nnat nmat})
  ... | MayMatch ¬mat mmat ¬nnat =
    MayMatch (λ{(θ , MInr mat) → ¬mat (θ , mat)})
             (MMInr mmat)
             (λ{(NMInr nnat) → ¬nnat nnat})
  ... | NotMatch ¬mat ¬mmat nnat =
    NotMatch (λ{(θ , MInr mat) → ¬mat (θ , mat)})
             (λ{(MMInr mmat) → ¬mmat mmat})
             (NMInr nnat)
  matching-det {e = e} fin wt (PTPair disj disjh pt1 pt2)
    with notintro-dec e
  ... | Inl ni
    with matching-det (FIndet (IFst (final-notintro-indet fin ni)))
                      (TAFst wt) pt1 |
         matching-det (FIndet (ISnd (final-notintro-indet fin ni)))
                      (TASnd wt) pt2
  ... | Match (θ1 , mat1) ¬mmat1 ¬nmat1 |
        Match (θ2 , mat2) ¬mmat2 ¬nmat2 =
    Match (θ1 ⊎ θ2 , MNotIntroPair ni mat1 mat2)
          (λ{(MMNotIntro ni (RPairL ref1)) →
              ¬mmat1 (MMNotIntro NVFst ref1)
           ; (MMNotIntro ni (RPairR ref2)) →
              ¬mmat2 (MMNotIntro NVSnd ref2)})
          λ{(NMPairL nmat1) → contra ni λ ()
          ; (NMPairR nmat2) → contra ni λ ()}
  ... | Match mat1 ¬mmat1 ¬nmat1 |
        MayMatch ¬mat2 (MMNotIntro ni2 ref2) ¬nmat2 =
    MayMatch (λ{(_ , MNotIntroPair {θ1 = θ1} {θ2 = θ2} ni mat1 mat2) →
                ¬mat2 (θ2 , mat2)})
             (MMNotIntro ni (RPairR ref2))
             (λ{(NMPairL nmat1) → contra ni λ ()
              ; (NMPairR nmat2) → contra ni λ ()})
  ... | Match mat1 ¬mmat1 ¬nmat1 | MayMatch ¬mat2 MMEHole ¬nmat2 =
    MayMatch (λ{(_ , MPair mat1 ()) 
              ; (_ , MNotIntroPair ni mat1 ())})
             (MMNotIntro ni (RPairR REHole))
             (λ{(NMPairL nmat1) → contra ni λ ()
              ; (NMPairR nmat2) → contra ni λ ()})
  ... | Match mat1 ¬mmat1 ¬nmat1 | MayMatch ¬mat2 MMNEHole ¬nmat2 =
    MayMatch (λ{(_ , MPair mat1 ()) 
              ; (_ , MNotIntroPair ni mat1 ())})
             (MMNotIntro ni (RPairR RNEHole))
             (λ{(NMPairL nmat1) → contra ni λ ()
              ; (NMPairR nmat2) → contra ni λ ()})
  ... | MayMatch ¬mat1 (MMNotIntro ni1 ref1) ¬nmat1 |
        Match mat2 ¬mmat2 ¬nmat2 =
    MayMatch ((λ{(_ , MNotIntroPair {θ1 = θ1} {θ2 = θ2} ni mat1 mat2) →
                 ¬mat1 (θ1 , mat1)}))
             (MMNotIntro ni (RPairL ref1))
             (λ{(NMPairL nmat1) → contra ni λ ()
              ; (NMPairR nmat2) → contra ni λ ()})
  ... | MayMatch ¬mat1 MMEHole ¬nmat1 | Match mat2 ¬mmat2 ¬nmat2 =
    MayMatch (λ{(_ , MPair () mat2) 
              ; (_ , MNotIntroPair ni () mat2)})
             (MMNotIntro ni (RPairL REHole))
             (λ{(NMPairL nmat1) → contra ni λ ()
              ; (NMPairR nmat2) → contra ni λ ()})
  ... | MayMatch ¬mat1 MMNEHole ¬nmat1 | Match mat2 ¬mmat2 ¬nmat2 =
    MayMatch (λ{(_ , MPair () mat2) 
              ; (_ , MNotIntroPair ni () mat2)})
             (MMNotIntro ni (RPairL RNEHole))
             (λ{(NMPairL nmat1) → contra ni λ ()
              ; (NMPairR nmat2) → contra ni λ ()})
  ... | MayMatch ¬mat1 (MMNotIntro ni1 ref1) ¬nmat1 |
        MayMatch ¬mat2 mmat2 ¬nmat2 =
    MayMatch ((λ{(_ , MNotIntroPair {θ1 = θ1} {θ2 = θ2} ni mat1 mat2) →
                 ¬mat1 (θ1 , mat1)}))
             (MMNotIntro ni (RPairL ref1))
             (λ{(NMPairL nmat1) → contra ni λ ()
              ; (NMPairR nmat2) → contra ni λ ()})
  ... | MayMatch ¬mat1 MMEHole ¬nmat1 | MayMatch ¬mat2 mmat2 ¬nmat2 =
    MayMatch (λ{(_ , MPair () mat2) 
              ; (_ , MNotIntroPair ni () mat2)})
             (MMNotIntro ni (RPairL REHole))
             (λ{(NMPairL nmat1) → contra ni λ ()
              ; (NMPairR nmat2) → contra ni λ ()})
  ... | MayMatch ¬mat1 MMNEHole ¬nmat1 | MayMatch ¬mat2 mmat2 ¬nmat2 =
    MayMatch (λ{(_ , MPair () mat2) 
              ; (_ , MNotIntroPair ni () mat2)})
             (MMNotIntro ni (RPairL RNEHole))
             (λ{(NMPairL nmat1) → contra ni λ ()
              ; (NMPairR nmat2) → contra ni λ ()})
  matching-det {e = e} fin wt (PTPair disj disjh pt1 pt2) | Inr ¬ni
    with wt
  ... | TAAp _ _ = abort (¬ni NVAp)
  ... | TAMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TAMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TAFst _ = abort (¬ni NVFst)
  ... | TASnd _ = abort (¬ni NVSnd)
  ... | TAEHole _ = abort (¬ni NVEHole)
  ... | TANEHole _ _ = abort (¬ni NVNEHole)
  ... | TAPair wt1 wt2
    with matching-det (π1 (pair-final fin)) wt1 pt1 |
         matching-det (π2 (pair-final fin)) wt2 pt2
  ... | Match (θ1 , mat1) ¬mmat1 ¬nmat1 | Match (θ2 , mat2) ¬mmat2 ¬nmat2 =
    Match (θ1 ⊎ θ2 , MPair mat1 mat2)
          (λ{(MMPairL mmat1 mat2) → ¬mmat1 mmat1
           ; (MMPairR mat1 mmat2) → ¬mmat2 mmat2
           ; (MMPair mmat1 mmat2) → ¬mmat1 mmat1})
          (λ{(NMPairL nmat1) → ¬nmat1 nmat1
           ; (NMPairR nmat2) → ¬nmat2 nmat2})
  ... | Match (θ1 , mat1) ¬mmat1 ¬nmat1 | MayMatch ¬mat2 mmat2 ¬nmat2 =
    MayMatch (λ{(_ , MPair {θ1 = θ1} {θ2 = θ2} mat1 mat2) →
                ¬mat2 (θ2 , mat2)})
             (MMPairR mat1 mmat2)
             (λ{(NMPairL nmat1) → ¬nmat1 nmat1
              ; (NMPairR nmat2) → ¬nmat2 nmat2})
  ... | Match mat1 ¬mmat1 ¬nmat1 | NotMatch ¬mat2 ¬mmat2 nmat2 =
    NotMatch (λ{(_ , MPair {θ1 = θ1} {θ2 = θ2} mat1 mat2) →
                ¬mat2 (θ2 , mat2)})
             (λ{(MMPairL {θ = θ} mmat1 mat2) → ¬mat2 (θ , mat2)
              ; (MMPairR {θ = θ} mat1 mmat2) → ¬mmat2 mmat2
              ; (MMPair mmat1 mmat2) → ¬mmat2 mmat2})
             (NMPairR nmat2)
  ... | MayMatch ¬mat1 mmat1 ¬nmat1 | Match (θ2 , mat2) ¬mmat2 ¬nmat2 =
    MayMatch (λ{(_ , MPair {θ1 = θ1} {θ2 = θ2} mat1 mat2) →
                ¬mat1 (θ1 , mat1)})
             (MMPairL mmat1 mat2)
             (λ{(NMPairL nmat1) → ¬nmat1 nmat1
              ; (NMPairR nmat2) → ¬nmat2 nmat2})
  ... | MayMatch ¬mat1 mmat1 ¬nmat1 | MayMatch ¬mat2 mmat2 ¬nmat2 =
    MayMatch (λ{(_ , MPair {θ1 = θ1} {θ2 = θ2} mat1 mat2) →
                ¬mat1 (θ1 , mat1)})
             (MMPair mmat1 mmat2)
             (λ{(NMPairL nmat1) → ¬nmat1 nmat1
              ; (NMPairR nmat2) → ¬nmat2 nmat2})
  ... | MayMatch ¬mat1 mmat1 ¬nmat1 | NotMatch ¬mat2 ¬mmat2 nmat2 =
    NotMatch (λ{(_ , MPair {θ1 = θ1} {θ2 = θ2} mat1 mat2) →
                ¬mat2 (θ2 , mat2)})
             (λ{(MMPairL {θ = θ} mmat1 mat2) → ¬mat2 (θ , mat2)
              ; (MMPairR {θ = θ} mat1 mmat2) → ¬mmat2 mmat2
              ; (MMPair mmat1 mmat2) → ¬mmat2 mmat2})
             (NMPairR nmat2)
  ... | NotMatch ¬mat1 ¬mmat1 nmat1 | md2 =
    NotMatch (λ{(_ , MPair {θ1 = θ1} {θ2 = θ2} mat1 mat2) →
                ¬mat1 (θ1 , mat1)})
             (λ{(MMPairL {θ = θ} mmat1 mat2) → ¬mmat1 mmat1
              ; (MMPairR {θ = θ} mat1 mmat2) → ¬mat1 (θ , mat1)
              ; (MMPair mmat1 mmat2) → ¬mmat1 mmat1})
             (NMPairL nmat1)
  matching-det {e = e} {p = p} fin wt PTEHole =
    MayMatch (λ ()) MMEHole (λ ())
  matching-det {e = e} {p = p} fin wt (PTNEHole pt apt) =
    MayMatch (λ ()) MMNEHole (λ ())
  matching-det {e = e} {p = p} fin wt PTWild =
    Match (Id ∅ , MWild)
          (λ{(MMNotIntro _ ())})
          (λ ())
