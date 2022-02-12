open import List
open import Nat
open import Prelude
open import contexts
open import core
open import notintro-decidable
open import patterns-core
open import result-judgements
open import statics-core

module matching-determinism where       
  data ExhaustMatch (e : ihexp) (τ : htyp) (p : pattrn) : Set where
       Match    : Σ[ θ ∈ subst-list ] e ·: τ ▹ p ⊣ θ →
                  ExhaustMatch e τ p
       MayMatch : e ·: τ ?▹ p →
                  ExhaustMatch e τ p
       NotMatch : e ⊥▹ p →
                  ExhaustMatch e τ p
                  
  matching-exhaust : ∀{Δ Δpe e τ Δp p ξ Γ} →
                     e final →
                     ∅ , Δ , Δpe ⊢ e :: τ →
                     Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                     ExhaustMatch e τ p
  matching-exhaust {e = e} {τ = τ} {p = p}
                   fin wt (PTVar {x = x}) =
    Match ((e , τ , x) :: [] , MVar)
  matching-exhaust {e = e} {p = p} fin wt (PTNum {n = n})
    with notintro-dec e
  ... | Inl ni =
    MayMatch (MMNotIntro ni RNum) 
  ... | Inr ¬ni
    with wt
  ... | TAAp _ _ = abort (¬ni NVAp)
  ... | TAMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TAMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TAFst _ = abort (¬ni NVFst)
  ... | TASnd _ = abort (¬ni NVSnd)
  ... | TAEHole _ _ = abort (¬ni NVEHole)
  ... | TANEHole _ _ _ = abort (¬ni NVNEHole)
  ... | TANum {n = m}
    with nat-dec m n
  ... | Inl refl =
    Match ([] , MNum)
  ... | Inr m≠n =
    NotMatch (NMNum m≠n)
  matching-exhaust {e = e} {p = p} fin wt (PTInl pt)
    with notintro-dec e
  ... | Inl ni =
    MayMatch (MMNotIntro ni RInl) 
  ... | Inr ¬ni
    with wt
  ... | TAAp _ _ = abort (¬ni NVAp)
  ... | TAMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TAMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TAFst _ = abort (¬ni NVFst)
  ... | TASnd _ = abort (¬ni NVSnd)
  ... | TAEHole _ _ = abort (¬ni NVEHole)
  ... | TANEHole _ _ _ = abort (¬ni NVNEHole)
  ... | TAInr wt₁ =
    NotMatch NMConfL
  ... | TAInl wt₁
    with matching-exhaust (inl-final fin) wt₁ pt
  ... | Match (θ , mat) =
    Match (θ , (MInl mat))
  ... | MayMatch mmat =
    MayMatch (MMInl mmat)   
  ... | NotMatch nmat =
    NotMatch (NMInl nmat)
  matching-exhaust {e = e} {p = p} fin wt (PTInr pt)
    with notintro-dec e
  ... | Inl ni =
    MayMatch (MMNotIntro ni RInr) 
  ... | Inr ¬ni
    with wt
  ... | TAAp _ _ = abort (¬ni NVAp)
  ... | TAMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TAMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TAFst _ = abort (¬ni NVFst)
  ... | TASnd _ = abort (¬ni NVSnd)
  ... | TAEHole _ _ = abort (¬ni NVEHole)
  ... | TANEHole _ _ _ = abort (¬ni NVNEHole)
  ... | TAInl wt₁ =
    NotMatch NMConfR
  ... | TAInr wt₁
    with matching-exhaust (inr-final fin) wt₁ pt
  ... | Match (θ , mat) =
    Match (θ , MInr mat)
  ... | MayMatch mmat =
    MayMatch (MMInr mmat)
  ... | NotMatch nmat =
    NotMatch (NMInr nmat)
  matching-exhaust {e = e} fin wt (PTPair disj pt1 pt2)
    with notintro-dec e
  ... | Inl ni
    with matching-exhaust
           (FIndet (IFst (λ{e1 e2 refl → contra ni (λ ())})
                         (final-notintro-indet fin ni)))
           (TAFst wt) pt1 |
         matching-exhaust
           (FIndet (ISnd (λ{e1 e2 refl → contra ni λ ()})
                         (final-notintro-indet fin ni)))
           (TASnd wt) pt2
  ... | Match (θ1 , mat1) | Match (θ2 , mat2) =
    Match (θ1 ++ θ2 , MNotIntroPair ni mat1 mat2)
  ... | Match mat1 | MayMatch (MMNotIntro ni2 ref2) =
    MayMatch (MMNotIntro ni (RPairR ref2))
  ... | Match mat1 | MayMatch MMEHole =
    MayMatch (MMNotIntro ni (RPairR REHole))
  ... | Match mat1 | MayMatch MMNEHole =
    MayMatch (MMNotIntro ni (RPairR RNEHole)) 
  ... | MayMatch (MMNotIntro ni1 ref1) | Match mat2 =
    MayMatch (MMNotIntro ni (RPairL ref1))  
  ... | MayMatch MMEHole | Match mat2 =
    MayMatch (MMNotIntro ni (RPairL REHole))
  ... | MayMatch MMNEHole | Match mat2 =
    MayMatch (MMNotIntro ni (RPairL RNEHole))
  ... | MayMatch (MMNotIntro ni1 ref1) | MayMatch mmat2 =
    MayMatch (MMNotIntro ni (RPairL ref1))   
  ... | MayMatch MMEHole | MayMatch mmat2 =
    MayMatch (MMNotIntro ni (RPairL REHole))
  ... | MayMatch MMNEHole | MayMatch mmat2 =
    MayMatch (MMNotIntro ni (RPairL RNEHole))       
  matching-exhaust {e = e} fin wt (PTPair disj pt1 pt2) | Inr ¬ni
    with wt
  ... | TAAp _ _ = abort (¬ni NVAp)
  ... | TAMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TAMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TAFst _ = abort (¬ni NVFst)
  ... | TASnd _ = abort (¬ni NVSnd)
  ... | TAEHole _ _ = abort (¬ni NVEHole)
  ... | TANEHole _ _ _ = abort (¬ni NVNEHole)
  ... | TAPair wt1 wt2
    with matching-exhaust (π1 (pair-final fin)) wt1 pt1 |
         matching-exhaust (π2 (pair-final fin)) wt2 pt2
  ... | Match (θ1 , mat1) | Match (θ2 , mat2) =
    Match (θ1 ++ θ2 , MPair mat1 mat2)
  ... | Match (θ1 , mat1) | MayMatch mmat2 =
    MayMatch (MMPairR mat1 mmat2)
  ... | Match mat1 | NotMatch nmat2 =
    NotMatch (NMPairR nmat2)
  ... | MayMatch mmat1 | Match (θ2 , mat2) =
    MayMatch (MMPairL mmat1 mat2)
  ... | MayMatch mmat1 | MayMatch mmat2 =
    MayMatch (MMPair mmat1 mmat2)  
  ... | MayMatch mmat1 | NotMatch nmat2 =
    NotMatch (NMPairR nmat2)
  ... | NotMatch nmat1 | md2 =
    NotMatch (NMPairL nmat1)
  matching-exhaust {e = e} {p = p} fin wt (PTEHole w∈Δp) =
    MayMatch MMEHole
  matching-exhaust {e = e} {p = p} fin wt (PTNEHole w∈Δp pt) =
    MayMatch MMNEHole
  matching-exhaust {e = e} {p = p} fin wt PTWild =
    Match ([] , MWild)

  mat-maymat-not : ∀{e τ p θ} →
                   e ·: τ ▹ p ⊣ θ →
                   e ·: τ ?▹ p →
                   ⊥
  mat-maymat-not MNum (MMNotIntro () ref)
  mat-maymat-not MVar (MMNotIntro ni ())
  mat-maymat-not (MInl mat) (MMInl mmat) =
    mat-maymat-not mat mmat
  mat-maymat-not (MInr mat) (MMInr mmat) =
    mat-maymat-not mat mmat
  mat-maymat-not (MPair mat1 mat2) (MMPairL mmat1 mat2') =
    mat-maymat-not mat1 mmat1
  mat-maymat-not (MPair mat1 mat2) (MMPairR mat1' mmat2) =
    mat-maymat-not mat2 mmat2
  mat-maymat-not (MPair mat1 mat2) (MMPair mmat1 mmat2) =
    mat-maymat-not mat1 mmat1
  mat-maymat-not (MNotIntroPair ni mat1 mat2)
                 (MMNotIntro ni₁ (RPairL ref1)) =
    mat-maymat-not mat1 (MMNotIntro NVFst ref1)
  mat-maymat-not (MNotIntroPair ni mat1 mat2)
                 (MMNotIntro ni₁ (RPairR ref2)) =
    mat-maymat-not mat2 (MMNotIntro NVSnd ref2)
  mat-maymat-not MWild (MMNotIntro ni ())

  mat-notmat-not : ∀{e τ p θ} →
                   e ·: τ ▹ p ⊣ θ →
                   e ⊥▹ p →
                   ⊥
  mat-notmat-not MNum (NMNum n≠n) = n≠n refl
  mat-notmat-not (MInl mat) (NMInl nmat) =
    mat-notmat-not mat nmat
  mat-notmat-not (MInr mat) (NMInr nmat) =
    mat-notmat-not mat nmat
  mat-notmat-not (MPair mat mat₁) (NMPairL nmat) =
    mat-notmat-not mat nmat
  mat-notmat-not (MPair mat mat₁) (NMPairR nmat) =
    mat-notmat-not mat₁ nmat

  maymat-notmat-not : ∀{e τ p} →
                      e ·: τ ?▹ p →
                      e ⊥▹ p →
                      ⊥
  maymat-notmat-not (MMInl mmat) (NMInl nmat) =
    maymat-notmat-not mmat nmat
  maymat-notmat-not (MMInr mmat) (NMInr nmat) =
    maymat-notmat-not mmat nmat
  maymat-notmat-not (MMPairL mmat1 mat2) (NMPairL nmat1) =
    maymat-notmat-not mmat1 nmat1
  maymat-notmat-not (MMPairL mmat1 mat2) (NMPairR nmat2) =
    mat-notmat-not mat2 nmat2
  maymat-notmat-not (MMPairR mat1 mmat2) (NMPairL nmat1) =
    mat-notmat-not mat1 nmat1
  maymat-notmat-not (MMPairR mat1 mmat2) (NMPairR nmat2) =
    maymat-notmat-not mmat2 nmat2
  maymat-notmat-not (MMPair mmat1 mmat2) (NMPairL nmat1) =
    maymat-notmat-not mmat1 nmat1
  maymat-notmat-not (MMPair mmat1 mmat2) (NMPairR nmat2) =
    maymat-notmat-not mmat2 nmat2
  maymat-notmat-not (MMNotIntro () ref) (NMNum n1≠n2)
  maymat-notmat-not (MMNotIntro () ref) NMConfL
  maymat-notmat-not (MMNotIntro () ref) NMConfR
  maymat-notmat-not (MMNotIntro () ref) (NMInl nmat)
  maymat-notmat-not (MMNotIntro () ref) (NMInr nmat)
  maymat-notmat-not (MMNotIntro () ref) (NMPairL nmat1)
  maymat-notmat-not (MMNotIntro () ref) (NMPairR nmat2)
  
  data DetMatch (e : ihexp) (τ : htyp) (p : pattrn) : Set where
       Match    : (Σ[ θ ∈ subst-list ] e ·: τ ▹ p ⊣ θ) →
                  (e ·: τ ?▹ p → ⊥) →
                  (e ⊥▹ p → ⊥) →
                  DetMatch e τ p
       MayMatch : ((Σ[ θ ∈ subst-list ] e ·: τ ▹ p ⊣ θ) → ⊥) →
                  (e ·: τ ?▹ p) →
                  (e ⊥▹ p → ⊥) →
                  DetMatch e τ p
       NotMatch : ((Σ[ θ ∈ subst-list ] e ·: τ ▹ p ⊣ θ) → ⊥) →
                  (e ·: τ ?▹ p → ⊥) →
                  (e ⊥▹ p) →
                  DetMatch e τ p
                  
  matching-det : ∀{Δ Δpe e τ Δp p ξ Γ} →
                 e final →
                 ∅ , Δ , Δpe ⊢ e :: τ →
                 Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                 DetMatch e τ p
  matching-det fin wt pt
    with matching-exhaust fin wt pt
  ... | Match mat =
    Match mat
          (λ mmat → mat-maymat-not (π2 mat) mmat)
          (λ nmat → mat-notmat-not (π2 mat) nmat)
  ... | MayMatch mmat =
    MayMatch (λ mat → mat-maymat-not (π2 mat) mmat)
             mmat
             (λ nmat → maymat-notmat-not mmat nmat)
  ... | NotMatch nmat =
    NotMatch (λ mat → mat-notmat-not (π2 mat) nmat)
             (λ mmat → maymat-notmat-not mmat nmat)
             nmat
