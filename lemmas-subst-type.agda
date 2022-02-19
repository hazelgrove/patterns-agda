open import List
open import Nat
open import Prelude
open import binders-disjointness
open import binders-disjoint-symmetric
open import binders-uniqueness
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import exchange
open import freshness
open import freshness-decidable
open import hole-binders-disjoint-symmetric
open import lemmas-contexts
open import lemmas-freshness
open import lemmas-subst-disjointness
open import lemmas-subst-satisfy
open import lemmas-subst-result
open import patterns-core
open import result-judgements
open import statics-core
open import type-assignment-unicity
open import weakening

module lemmas-subst-type where
  subst-erase : ∀{rs-pre r rs-post rs x e2} →
                erase-r (rs-pre / r / rs-post) rs →
                erase-r ([ e2 / x ]zrs (rs-pre / r / rs-post))
                        ([ e2 / x ]rs rs)
  subst-erase ERZPre = ERZPre
  subst-erase (ERNZPre er) = ERNZPre (subst-erase er)
  
  mutual
    subst-type : ∀{Γ Δ Δp x τ1 e1 τ e2} →
                 binders-disjoint e1 e2 →
                 hole-binders-disjoint e1 e2 →
                 e2 final →
                 (Γ ,, (x , τ1)) , Δ , Δp ⊢ e1 :: τ →
                 Γ , Δ , Δp ⊢ e2 :: τ1 →
                 Γ , Δ , Δp ⊢ [ e2 / x ] e1 :: τ
    subst-type bd hbd fin2 TAUnit wt2 = TAUnit
    subst-type bd hbd fin2 TANum wt2 = TANum
    subst-type {x = x} bd hbd fin2 (TAVar {x = y} y∈) wt2
      with nat-dec y x
    ... | Inl refl
      with nat-dec x x
    ... | Inr x≠x = abort (x≠x refl)
    ... | Inl refl
      with some-inj y∈
    ... | refl = wt2
    subst-type {x = x} bd hbd fin2 (TAVar {x = y} y∈) wt2
        | Inr y≠x
      with nat-dec x y
    ... | Inl refl = abort (y≠x refl)
    ... | Inr x≠y = TAVar y∈
    subst-type {Γ = Γ} {x = x} bd hbd bu
               (TALam {x = y} y# wts) wt2
      with nat-dec y x
    ... | Inl refl
      with nat-dec x x
    ... | Inr x≠x = abort (x≠x refl)
    ... | Inl refl = abort (some-not-none y#)
    subst-type {Γ = Γ} {x = x} (BDLam ub bd) (HBDLam hbd) fin2
               (TALam {x = y} y# wts) wt2
        | Inr y≠x
      with nat-dec x y
    ... | Inl refl = abort (y≠x refl)
    ... | Inr x≠y =
      TALam y#
            (subst-type
              bd hbd fin2
              (exchange-ta-Γ x≠y wts)
              (weaken-ta-Γ (binders-fresh wt2 ub y#) wt2))
    subst-type (BDAp bd1 bd2) (HBDAp hbd1 hbd2) fin2
               (TAAp wts1 wts2) wt2 =
      TAAp (subst-type bd1 hbd1 fin2 wts1 wt2)
           (subst-type bd2 hbd2 fin2 wts2 wt2)
    subst-type (BDInl bd) (HBDInl hbd) fin2 (TAInl wts) wt2 =
      TAInl (subst-type bd hbd fin2 wts wt2)
    subst-type (BDInr bd) (HBDInr hbd) fin2 (TAInr wts) wt2 =
      TAInr (subst-type bd hbd fin2 wts wt2)
    subst-type (BDMatch 1d2 (BDZRules _ (BDRules rd2 _)))
               (HBDMatch 1hd2 (HBDZRules _ (HBDRules rhd2 _))) fin2
               (TAMatchZPre wts (RTOneRule rt)) wt2 = 
      TAMatchZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                  (RTOneRule (subst-type-r rd2 rhd2 fin2
                                           rt wt2))
    subst-type (BDMatch 1d2 (BDZRules _ (BDRules rd2 postd2)))
               (HBDMatch 1hd2 (HBDZRules _ (HBDRules rhd2 posthd2))) fin2
               (TAMatchZPre wts (RTRules rt rst)) wt2 =
      TAMatchZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                  (RTRules (subst-type-r rd2 rhd2 fin2 rt wt2)
                           (subst-type-rs postd2 posthd2 fin2
                                          rst wt2))
    subst-type (BDMatch 1d2
                            (BDZRules pred2 (BDRules rd2 predpost)))
               (HBDMatch 1hd2
                         (HBDZRules prehd2 (HBDRules rhd2 prehdpost))) fin2
               (TAMatchNZPre wts fin1 pret
                             (RTOneRule rt) ¬red) wt2 =
      TAMatchNZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                   (final-subst-final fin1 fin2)
                   (subst-type-rs pred2 prehd2 fin2 pret wt2)
                   (subst-type-rs (BDRules rd2 BDNoRules)
                                  (HBDRules rhd2 HBDNoRules)
                                  fin2 (RTOneRule rt) wt2)
                   λ{satm → ¬red (final-satormay-subst fin1 satm)}
    subst-type (BDMatch 1d2 (BDZRules pred2 (BDRules rd2 postd2)))
               (HBDMatch 1hd2
                         (HBDZRules prehd2 (HBDRules rhd2 posthd2))) fin2
               (TAMatchNZPre wts fin1 pret
                                 (RTRules rt postt) ¬red) wt2 =
      TAMatchNZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                   (final-subst-final fin1 fin2)
                   (subst-type-rs pred2 prehd2 fin2 pret wt2)
                   (subst-type-rs (BDRules rd2 postd2)
                                  (HBDRules rhd2 posthd2)
                                  fin2 (RTRules rt postt) wt2)
                   λ{satm → ¬red (final-satormay-subst fin1 satm)}
    subst-type (BDPair bd1 bd2) (HBDPair hbd1 hbd2) fin2
               (TAPair wts1 wts2) wt2 =
      TAPair (subst-type bd1 hbd1 fin2 wts1 wt2)
             (subst-type bd2 hbd2 fin2 wts2 wt2)
    subst-type (BDFst bd) (HBDFst hbd) fin2 (TAFst wts) wt2 =
      TAFst (subst-type bd hbd fin2 wts wt2)
    subst-type (BDSnd bd) (HBDSnd hbd) fin2 (TASnd wts) wt2 =
      TASnd (subst-type bd hbd fin2 wts wt2)
    subst-type bd hbd fin2 (TAEHole u∈Δ st) wt2 =
      TAEHole u∈Δ (STASubst st wt2)
    subst-type (BDNEHole bdσ bd) (HBDNEHole hbdσ hbd) fin2
               (TANEHole u∈Δ st wts) wt2 =
      TANEHole u∈Δ (STASubst st wt2)
               (subst-type bd hbd fin2 wts wt2)          
    
    subst-type-rs : ∀{Γ Δ Δp x τ1 rs τ ξ τ' e2} →
                    binders-disjoint-rs rs e2 →
                    hole-binders-disjoint-rs rs e2 →
                    e2 final →
                    (Γ ,, (x , τ1)) , Δ , Δp ⊢ rs ::s τ [ ξ ]=> τ' →
                    Γ , Δ , Δp ⊢ e2 :: τ1 →
                    Γ , Δ , Δp ⊢ [ e2 / x ]rs rs ::s τ [ ξ ]=> τ'
    subst-type-rs (BDRules rd2 rsd2)
                  (HBDRules rhd2 rshd2) fin2 (RTOneRule rt) wt2 =
      RTOneRule (subst-type-r rd2 rhd2 fin2 rt wt2)
    subst-type-rs (BDRules rd2 rsd2)
                  (HBDRules rhd2 rshd2) fin2 (RTRules rt rst) wt2 =
      RTRules (subst-type-r rd2 rhd2 fin2 rt wt2)
              (subst-type-rs rsd2 rshd2 fin2 rst wt2)
              
    subst-type-r : ∀{Γ Δ Δp x τ1 r τ ξ τ' e2} →
                   binders-disjoint-r r e2 →
                   hole-binders-disjoint-r r e2 →
                   e2 final →
                   (Γ ,, (x , τ1)) , Δ , Δp ⊢ r :: τ [ ξ ]=> τ' →
                   Γ , Δ , Δp ⊢ e2 :: τ1 →
                   Γ , Δ , Δp ⊢ [ e2 / x ]r r :: τ [ ξ ]=> τ'
    subst-type-r {Γ = Γ} {Δ = Δ} {x = x} {τ1 = τ1} {e2 = e2}
                 (BDRule {p = p} pd2 1d2)
                 (HBDRule {p = p} phd2 1hd2) fin2
                 (RTRule {Γp = Γp} pt Γ,##Γp wts)
                 wt2
      with unbound-in-p-dec x p
    ... | Inr ¬ub =
      abort (¬ub (apart-Γp-unbound-in-p
                    pt
                    (disjoint-singleton-apart
                      (union-disjoint-l Γ,##Γp))))
    ... | Inl ub rewrite (∪-assoc (■ (x , τ1)) Γ Γp) =
      RTRule pt
             (union-disjoint-r {Γ1 = ■ (x , τ1)} {Γ2 = Γ} Γ,##Γp)
             (subst-type 1d2 1hd2 fin2 wts (weaken-ta-Γ∪ frsh wt2))
      where
        frsh : ∀{z} →
               dom Γp z →
               fresh z e2
        frsh {z = z} z∈Γp = 
          binders-fresh wt2
                        (dom-Γp-unbound-in pt z∈Γp pd2)
                        z#Γ
          where
            z#Γ : z # Γ
            z#Γ with Γ z in Γz
            ... | None = refl
            ... | Some τ =
              abort (some-not-none
                      (! Γz · apart-union-r (■ (x , τ1)) Γ z
                                            (π2 Γ,##Γp z z∈Γp)))

  apply-substs-concat : (θ1 θ2 : subst-list)
                        (e : ihexp) →
                        apply-substs (θ1 ++ θ2) e ==
                          apply-substs θ1 (apply-substs θ2 e)
  apply-substs-concat [] θ2 e = refl
  apply-substs-concat (( d , τ , y ) :: θ1) θ2 e =
    ap1 (λ qq → (·λ y ·[ τ ] qq) ∘ d) (apply-substs-concat θ1 θ2 e)

  unbound-in-θ-apart-Γθ : ∀{Γ Δ Δp θ Γθ x} →
                          Γ , Δ , Δp ⊢ θ :sl: Γθ →
                          unbound-in-θ x θ →
                          x # Γθ
  unbound-in-θ-apart-Γθ STAEmpty UBθEmpty = refl
  unbound-in-θ-apart-Γθ {x = x}
                        (STAExtend {Γθ = Γθ} y#Γ wst wt)
                        (UBθExtend xubd x≠y xubθ) =
    neq-apart-extend Γθ x≠y
                     (unbound-in-θ-apart-Γθ wst xubθ)

  -- the substituted variables in θ are unique,
  -- and none is a binder present in a substitued expression.
  -- this allows us to apply all the substitutions
  -- "simultaneously"
  data _simultaneous : (θ : subst-list) → Set where
    SθEmpty  : [] simultaneous
    SθExtend : ∀{d τ y θ} →
               unbound-in-θ y θ →
               θ simultaneous →
               ((d , τ , y) :: θ) simultaneous

  -- if θ1 and θ2 are simultaneous, then so is θ1 ++ θ2
  data jointly-simultaneous : (θ1 θ2 : subst-list) → Set where
    CθEmpty  : ∀{θ2} →
               jointly-simultaneous [] θ2
    CθExtend : ∀{d τ y θ1 θ2} →
               unbound-in-θ y θ2 →
               jointly-simultaneous θ1 θ2 →
               jointly-simultaneous ((d , τ , y) :: θ1) θ2
  
  substs-concat-type : ∀{Γ Δ Δp θ1 θ2 Γ1 Γ2} →
                       Γ , Δ , Δp ⊢ θ1 :sl: Γ1 →
                       Γ , Δ , Δp ⊢ θ2 :sl: Γ2 →
                       Γ , Δ , Δp ⊢ (θ1 ++ θ2) :sl: (Γ1 ∪ Γ2)
  substs-concat-type STAEmpty st2 = st2
  substs-concat-type {Γ = Γ} {Δ = Δ} {Δp = Δp}
                   {θ1 = (d , τ , y) :: θ1} {θ2 = θ2} {Γ2 = Γ2}
                   (STAExtend {Γθ = Γ1} {τ = τ} y#Γ1 st1 wt1) st2 =
    tr (λ qq → Γ , Δ , Δp ⊢ (d , τ , y) :: θ1 ++ θ2 :sl: qq)
       (! (∪-assoc (■ (y , τ)) Γ1 Γ2))
       (STAExtend y#Γ1 (substs-concat-type st1 st2) wt1)

  substs-concat-unbound-in : ∀{x θ1 θ2} →
                             unbound-in-θ x θ1 →
                             unbound-in-θ x θ2 →
                             unbound-in-θ x (θ1 ++ θ2)
  substs-concat-unbound-in UBθEmpty ub2 = ub2
  substs-concat-unbound-in (UBθExtend xubd x≠y ub1) ub2 =
    UBθExtend xubd x≠y (substs-concat-unbound-in ub1 ub2)


  substs-concat-simultaneous : ∀{θ1 θ2} →
                               jointly-simultaneous θ1 θ2 →
                               θ1 simultaneous →
                               θ2 simultaneous →
                               (θ1 ++ θ2) simultaneous
  substs-concat-simultaneous CθEmpty SθEmpty sim2 = sim2
  substs-concat-simultaneous (CθExtend yubθ2 con)
                             (SθExtend yubθ sim1) sim2 =
    SθExtend (substs-concat-unbound-in yubθ yubθ2)
             (substs-concat-simultaneous con sim1 sim2)

  substs-concat-jointly-simultaneous : ∀{θ1 θ2 θ3} →
                             jointly-simultaneous θ1 θ3 →
                             jointly-simultaneous θ2 θ3 →
                             jointly-simultaneous (θ1 ++ θ2) θ3
  substs-concat-jointly-simultaneous CθEmpty con2 = con2
  substs-concat-jointly-simultaneous (CθExtend yub3 con1) con2 =
    CθExtend yub3 (substs-concat-jointly-simultaneous con1 con2)
  
  unbound-in-mat-substs : ∀{x e τ p θ} →
                          unbound-in-e x e →
                          unbound-in-p x p →
                          e ·: τ ▹ p ⊣ θ →
                          unbound-in-θ x θ
  unbound-in-mat-substs ube UBPUnit MUnit = UBθEmpty
  unbound-in-mat-substs ube UBPNum MNum = UBθEmpty
  unbound-in-mat-substs ube (UBPVar x≠y) MVar =
    UBθExtend ube x≠y UBθEmpty
  unbound-in-mat-substs (UBInl ube) (UBPInl ubp) (MInl mat) =
    unbound-in-mat-substs ube ubp mat
  unbound-in-mat-substs (UBInr ube) (UBPInr ubp) (MInr mat) =
    unbound-in-mat-substs ube ubp mat
  unbound-in-mat-substs ube (UBPPair ubp1 ubp2) (MPair mat1 mat2)
    with ube
  ... | UBPair ube1 ube2 =
    substs-concat-unbound-in
      (unbound-in-mat-substs ube1 ubp1 mat1)
      (unbound-in-mat-substs ube2 ubp2 mat2)
  unbound-in-mat-substs ube (UBPPair ubp1 ubp2)
                        (MNotIntroPair ni mat1 mat2) =
    substs-concat-unbound-in
      (unbound-in-mat-substs (UBFst ube) ubp1 mat1)
      (unbound-in-mat-substs (UBSnd ube) ubp2 mat2)
  unbound-in-mat-substs ube UBPWild MWild = UBθEmpty

  
  mat-substs-jointly-simultaneous : ∀{e1 e2 τ1 τ2 p1 p2 θ1 θ2} →
                          binders-disjoint-p p1 p2 →
                          binders-disjoint-p p1 e2 →
                          e1 ·: τ1 ▹ p1 ⊣ θ1 →
                          e2 ·: τ2 ▹ p2 ⊣ θ2 →
                          jointly-simultaneous θ1 θ2
  mat-substs-jointly-simultaneous p1bdp2 p1bde2 MUnit mat2 = CθEmpty
  mat-substs-jointly-simultaneous p1bdp2 p1bde2 MNum mat2 = CθEmpty
  mat-substs-jointly-simultaneous (BDPVar xubp2) (BDPVar xube2) MVar mat2 =
    CθExtend (unbound-in-mat-substs xube2 xubp2 mat2) CθEmpty
  mat-substs-jointly-simultaneous (BDPInl p1bdp2) (BDPInl p1bde2) (MInl mat1) mat2 =
    mat-substs-jointly-simultaneous p1bdp2 p1bde2 mat1 mat2
  mat-substs-jointly-simultaneous (BDPInr p1bdp2) (BDPInr p1bde2) (MInr mat1) mat2 =
    mat-substs-jointly-simultaneous p1bdp2 p1bde2 mat1 mat2
  mat-substs-jointly-simultaneous (BDPPair p1₁bdp2 p1₂bdp2)
                        (BDPPair p1₁bde2 p1₂bde2)
                        (MPair {e1 = e1₁} {e2 = e1₂}
                               {τ1 = τ1₁} {τ2 = τ1₂}
                               {p1 = p1₁} {p2 = p1₂}
                               {θ1 = θ1₁} {θ2 = θ1₂}
                               mat1₁ mat1₂)
                        mat2 =
    substs-concat-jointly-simultaneous
      (mat-substs-jointly-simultaneous p1₁bdp2 p1₁bde2 mat1₁ mat2)
      (mat-substs-jointly-simultaneous p1₂bdp2 p1₂bde2 mat1₂ mat2)
  mat-substs-jointly-simultaneous (BDPPair p1₁bdp2 p1₂bdp2)
                        (BDPPair p1₁bde2 p1₂bde2)
                        (MNotIntroPair {τ1 = τ1₁} {τ2 = τ1₂}
                                       {p1 = p1₁} {p2 = p1₂}
                                       {θ1 = θ1₁} {θ2 = θ1₂}
                                       ni mat1₁ mat1₂)
                        mat2 =
    substs-concat-jointly-simultaneous
      (mat-substs-jointly-simultaneous p1₁bdp2 p1₁bde2 mat1₁ mat2)
      (mat-substs-jointly-simultaneous p1₂bdp2 p1₂bde2 mat1₂ mat2)
  mat-substs-jointly-simultaneous p1bdp2 p1bde2 MWild mat2 = CθEmpty
                          
  mat-substs-simultaneous : ∀{e τ p θ} →
                            binders-unique e →
                            binders-unique-p p →
                            binders-disjoint-p p e →
                            (e ·: τ ▹ p ⊣ θ) →
                            θ simultaneous
  mat-substs-simultaneous bue bup bd MUnit = SθEmpty
  mat-substs-simultaneous bue bup bd MNum = SθEmpty
  mat-substs-simultaneous bue bup bd MVar =
    SθExtend UBθEmpty SθEmpty
  mat-substs-simultaneous (BUInl bue) (BUPInl bup)
                          (BDPInl pbdie) (MInl mat)
    with binders-disjoint-p-sym pbdie
  ... | BDInl ebdp =
    mat-substs-simultaneous bue bup
                            (p-binders-disjoint-sym ebdp)
                            mat
  mat-substs-simultaneous (BUInr bue) (BUPInr bup)
                          (BDPInr pbdie) (MInr mat)
    with binders-disjoint-p-sym pbdie
  ... | BDInr ebdp =
    mat-substs-simultaneous bue bup
                            (p-binders-disjoint-sym ebdp)
                            mat
  mat-substs-simultaneous (BUPair bue1 bue2 e1bde2)
                          (BUPPair bup1 bup2 p1bdp2)
                          (BDPPair p1bde p2bde)
                          (MPair mat1 mat2)
    with binders-disjoint-p-sym p1bde |
         binders-disjoint-p-sym p2bde
  ... | BDPair e1bdp1 e2bdp1 | BDPair e1bdp2 e2bdp2 =
    substs-concat-simultaneous
      (mat-substs-jointly-simultaneous
        p1bdp2
        (p-binders-disjoint-sym e2bdp1)
        mat1 mat2)
      (mat-substs-simultaneous
        bue1 bup1
        (p-binders-disjoint-sym e1bdp1)
        mat1)
      (mat-substs-simultaneous
        bue2 bup2
        (p-binders-disjoint-sym e2bdp2)
        mat2)
  mat-substs-simultaneous bue
                          (BUPPair bup1 bup2 p1bdp2)
                          (BDPPair p1bde p2bde)
                          (MNotIntroPair ni mat1 mat2) =
    substs-concat-simultaneous
      (mat-substs-jointly-simultaneous
        p1bdp2
        (p-binders-disjoint-sym (BDSnd (binders-disjoint-p-sym p1bde)))
        mat1 mat2)
      (mat-substs-simultaneous
        (BUFst bue) bup1
        (p-binders-disjoint-sym (BDFst (binders-disjoint-p-sym p1bde)))
        mat1)
      (mat-substs-simultaneous
        (BUSnd bue) bup2
        (p-binders-disjoint-sym (BDSnd (binders-disjoint-p-sym p2bde)))
        mat2)
  mat-substs-simultaneous bue bup bd MWild = SθEmpty
  
  mat-substs-type : ∀{Γ Δ Δp e τ p ξ Γp θ} →
                    Γ , Δ , Δp ⊢ e :: τ →
                    Δp ⊢ p :: τ [ ξ ]⊣ Γp →
                    Γ ## Γp →
                    (e ·: τ ▹ p ⊣ θ) →
                    Γ , Δ , Δp ⊢ θ :sl: Γp
  mat-substs-type wt PTUnit Γ##Γp MUnit = STAEmpty
  mat-substs-type wt PTNum Γ##Γp MNum = STAEmpty
  mat-substs-type {Γ = Γ} {Δ = Δ} {Δp = Δp}
                  {e = e} {τ = τ}
                  wt PTVar Γ##Γp (MVar {x = x}) =
    tr (λ qq → Γ , Δ , Δp ⊢ (e , τ , x) :: [] :sl: qq)
       (∪-identityʳ (■ (x , τ)))
       (STAExtend (disjoint-singleton-apart (##-sym Γ##Γp)) STAEmpty wt)
  mat-substs-type (TAInl wt) (PTInl pt) Γ##Γp (MInl mat) =
    mat-substs-type wt pt Γ##Γp mat
  mat-substs-type (TAInr wt) (PTInr pt) Γ##Γp (MInr mat) =
    mat-substs-type wt pt Γ##Γp mat
  mat-substs-type {Γ = Γ} wt
                  (PTPair {Γ1 = Γ1} {Γ2 = Γ2} Γ1##Γ2 pt1 pt2)
                  Γ##Γp
                  (MPair mat1 mat2)
    with wt
  ... | TAPair wt1 wt2 =
    substs-concat-type
      (mat-substs-type wt1 pt1
                       (##-sym (union-disjoint-l {Γ1 = Γ1} {Γ2 = Γ2}
                                                 (##-sym Γ##Γp)))
                       mat1)
      (mat-substs-type wt2 pt2
                       (##-sym (union-disjoint-r {Γ1 = Γ1} {Γ2 = Γ2}
                                                 (##-sym Γ##Γp)))
                       mat2)
  mat-substs-type {Γ = Γ} wt 
                  (PTPair {Γ1 = Γ1} {Γ2 = Γ2} Γ1##Γ2 pt1 pt2)
                  Γ##Γp
                  (MNotIntroPair ni mat1 mat2) =
    substs-concat-type
      (mat-substs-type (TAFst wt) pt1
                       (##-sym (union-disjoint-l {Γ1 = Γ1} {Γ2 = Γ2}
                                                 (##-sym Γ##Γp)))
                       mat1)
      (mat-substs-type (TASnd wt) pt2
                       (##-sym (union-disjoint-r {Γ1 = Γ1} {Γ2 = Γ2}
                                                 (##-sym Γ##Γp)))
                       mat2)
  mat-substs-type wt PTWild Γ##Γp MWild = STAEmpty

  substs-type : ∀{Γ Δ Δp θ Γθ e τ} →
                θ simultaneous →
                Γ , Δ , Δp ⊢ θ :sl: Γθ →
                (Γθ ∪ Γ) , Δ , Δp ⊢ e :: τ →
                Γ , Δ , Δp ⊢ apply-substs θ e :: τ
  substs-type SθEmpty STAEmpty wt = wt
  substs-type {Γ = Γ} {Δ = Δ} {Δp = Δp} 
              {θ = (d , τ' , y) :: θ} {e = e} {τ = τ}
              (SθExtend yubθ sim)
              (STAExtend {Γθ = Γθ} {τ = τ'} {y = y} y#Γ wst wtd)
              wt =
    TAAp (TALam y#Γ
                (substs-type {Γθ = Γθ}
                             sim
                             (weaken-θ-∪Γ {Γ' = ■ (y , τ')} frsh wst)
                             (tr (λ qq → qq , Δ , Δp ⊢ e :: τ) eq wt)))
         wtd
    where
      eq : ((Γθ ,, (y , τ')) ∪ Γ) == (Γθ ∪ (Γ ,, (y , τ')))
      eq = ap1 (λ qq → qq ∪ Γ)
               (∪-comm (■ (y , τ')) Γθ
                       (apart-singleton-disjoint
                         (unbound-in-θ-apart-Γθ wst
                                                yubθ))) ·
             ∪-assoc Γθ (■ (y , τ')) Γ
      frsh : ∀{x} →
             dom (■ (y , τ')) x →
             fresh-θ x θ
      frsh x∈■ with dom-singleton-eq x∈■
      ... | refl = binders-fresh-θ wst yubθ y#Γ
