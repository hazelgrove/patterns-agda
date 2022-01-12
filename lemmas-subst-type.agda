open import Nat
open import Prelude
open import binders-disjointness
open import binders-uniqueness
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import exchange
open import freshness
open import freshness-decidable
open import lemmas-binders-disjointness
open import lemmas-contexts
open import lemmas-freshness
open import lemmas-subst-disjointness
open import lemmas-subst-satisfy
open import lemmas-subst-result
open import result-judgements
open import statics-core
open import substitution-env
open import weakening

module lemmas-subst-type where  
  mutual
    subst-type : ∀{Γ Δ x τ1 e1 τ e2} →
                 binders-disjoint e1 e2 →
                 hole-binders-disjoint e1 e2 →
                 e2 final →
                 (Γ ,, (x , τ1)) , Δ ⊢ e1 :: τ →
                 Γ , Δ ⊢ e2 :: τ1 →
                 Γ , Δ ⊢ [ e2 / x ] e1 :: τ
    subst-type bd hbd fin2 TANum wt2 = TANum
    subst-type {x = x} bd hbd fin2 (TAVar {x = y} y∈) wt2
      with natEQ y x
    ... | Inl refl
      with natEQ x x
    ... | Inr x≠x = abort (x≠x refl)
    ... | Inl refl
      with some-inj y∈
    ... | refl = wt2
    subst-type {x = x} bd hbd fin2 (TAVar {x = y} y∈) wt2
        | Inr y≠x
      with natEQ x y
    ... | Inl refl = abort (y≠x refl)
    ... | Inr x≠y = TAVar y∈
    subst-type {Γ = Γ} {x = x} bd hbd bu
               (TALam {x = y} y# wts) wt2
      with natEQ y x
    ... | Inl refl
      with natEQ x x
    ... | Inr x≠x = abort (x≠x refl)
    ... | Inl refl = abort (some-not-none y#)
    subst-type {Γ = Γ} {x = x} (BDLam ub bd) (HBDLam hbd) fin2
               (TALam {x = y} y# wts) wt2
        | Inr y≠x
      with natEQ x y
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
               (TAMatchZPre wts (CTOneRule rt)) wt2 = 
      TAMatchZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                  (CTOneRule (subst-type-r rd2 rhd2 fin2
                                           rt wt2))
    subst-type (BDMatch 1d2 (BDZRules _ (BDRules rd2 postd2)))
               (HBDMatch 1hd2 (HBDZRules _ (HBDRules rhd2 posthd2))) fin2
               (TAMatchZPre wts (CTRules rt rst)) wt2 =
      TAMatchZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                  (CTRules (subst-type-r rd2 rhd2 fin2 rt wt2)
                           (subst-type-rs postd2 posthd2 fin2
                                          rst wt2))
    subst-type (BDMatch 1d2
                            (BDZRules pred2 (BDRules rd2 predpost)))
               (HBDMatch 1hd2
                         (HBDZRules prehd2 (HBDRules rhd2 prehdpost))) fin2
               (TAMatchNZPre wts fin1 pret
                             (CTOneRule rt) ¬red) wt2 =
      TAMatchNZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                   (final-subst-final fin1 fin2)
                   (subst-type-rs pred2 prehd2 fin2 pret wt2)
                   (subst-type-rs (BDRules rd2 BDNoRules)
                                  (HBDRules rhd2 HBDNoRules)
                                  fin2 (CTOneRule rt) wt2)
                   λ{satm → ¬red (final-satormay-subst fin1 satm)}
    subst-type (BDMatch 1d2 (BDZRules pred2 (BDRules rd2 postd2)))
               (HBDMatch 1hd2
                         (HBDZRules prehd2 (HBDRules rhd2 posthd2))) fin2
               (TAMatchNZPre wts fin1 pret
                                 (CTRules rt postt) ¬red) wt2 =
      TAMatchNZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                   (final-subst-final fin1 fin2)
                   (subst-type-rs pred2 prehd2 fin2 pret wt2)
                   (subst-type-rs (BDRules rd2 postd2)
                                  (HBDRules rhd2 posthd2)
                                  fin2 (CTRules rt postt) wt2)
                   λ{satm → ¬red (final-satormay-subst fin1 satm)}
    subst-type (BDPair bd1 bd2) (HBDPair hbd1 hbd2) fin2
               (TAPair wts1 wts2) wt2 =
      TAPair (subst-type bd1 hbd1 fin2 wts1 wt2)
             (subst-type bd2 hbd2 fin2 wts2 wt2)
    subst-type (BDFst bd) (HBDFst hbd) fin2 (TAFst wts) wt2 =
      TAFst (subst-type bd hbd fin2 wts wt2)
    subst-type (BDSnd bd) (HBDSnd hbd) fin2 (TASnd wts) wt2 =
      TASnd (subst-type bd hbd fin2 wts wt2)
    subst-type bd hbd fin2 (TAEHole u∈Δ) wt2 = TAEHole u∈Δ
    subst-type (BDNEHole bd) (HBDNEHole hbd) fin2
               (TANEHole u∈Δ wts) wt2 =
      TANEHole u∈Δ (subst-type bd hbd fin2 wts wt2)


    subst-type-rs : ∀{Γ Δ x τ1 rs τ ξ τ' e2} →
                    binders-disjoint-rs rs e2 →
                    hole-binders-disjoint-rs rs e2 →
                    e2 final →
                    (Γ ,, (x , τ1)) , Δ ⊢ rs ::s τ [ ξ ]=> τ' →
                    Γ , Δ ⊢ e2 :: τ1 →
                    Γ , Δ ⊢ [ e2 / x ]rs rs ::s τ [ ξ ]=> τ'
    subst-type-rs (BDRules rd2 rsd2)
                  (HBDRules rhd2 rshd2) fin2 (CTOneRule rt) wt2 =
      CTOneRule (subst-type-r rd2 rhd2 fin2 rt wt2)
    subst-type-rs (BDRules rd2 rsd2)
                  (HBDRules rhd2 rshd2) fin2 (CTRules rt rst) wt2 =
      CTRules (subst-type-r rd2 rhd2 fin2 rt wt2)
              (subst-type-rs rsd2 rshd2 fin2 rst wt2)
              
    subst-type-r : ∀{Γ Δ x τ1 r τ ξ τ' e2} →
                   binders-disjoint-r r e2 →
                   hole-binders-disjoint-r r e2 →
                   e2 final →
                   (Γ ,, (x , τ1)) , Δ ⊢ r :: τ [ ξ ]=> τ' →
                   Γ , Δ ⊢ e2 :: τ1 →
                   Γ , Δ ⊢ [ e2 / x ]r r :: τ [ ξ ]=> τ'
    subst-type-r {Γ = Γ} {Δ = Δ} {x = x} {τ1 = τ1} {e2 = e2}
                 (BDRule {p = p} pd2 1d2)
                 (HBDRule {p = p} phd2 1hd2) fin2
                 (CTRule {Γp = Γp} {Δp = Δp} pt Γ,##Γp Δ##Δp wts)
                 wt2
      with unbound-in-p-dec x p
    ... | Inr ¬ub =
      abort (¬ub (apart-Γp-unbound-in-p
                    pt
                    (disjoint-singleton-apart
                      (union-disjoint-l Γ,##Γp))))
    ... | Inl ub rewrite (∪-assoc (■ (x , τ1)) Γ Γp) =
      CTRule pt
             (union-disjoint-r {Γ1 = ■ (x , τ1)} {Γ2 = Γ} Γ,##Γp)
             Δ##Δp
             (subst-type 1d2 1hd2 fin2 wts
                         (weaken-ta-Γ∪ frsh
                                       (weaken-ta-Δ∪ hfrsh wt2)))
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
          
        
        hfrsh : ∀{z} →
                dom Δp z →
                hole-fresh z e2
        hfrsh {z = z} z∈Δp =
          hole-binders-fresh wt2
                             (dom-Δp-unbound-in pt z∈Δp phd2)
                             z#Δ
          where
            z#Δ : z # Δ
            z#Δ with Δ z in Δz
            ... | None = refl
            ... | Some τ =
              abort (some-not-none
                      (! Δz · π2 Δ##Δp z z∈Δp))

  subst-env-type : ∀{Γ Δ Γθ e τ θ} →
                   (∀{x} →
                    dom Γ x →
                    unbound-in x e) →
                   binders-unique-env θ →
                   hole-binders-unique-env θ →
                   binders-disjoint-env θ e →
                   hole-binders-disjoint-env θ e → 
                   θ env-final →
                   Γθ , Δ ⊢ e :: τ →
                   Γ , Δ ⊢ θ :s: Γθ →
                   Γ , Δ ⊢ (apply-env θ e) :: τ
  subst-env-type {Γ = Γ} {Δ = Δ} {Γθ = Γθ} {e = e} {τ = τ}
                 ub ebu ehbu BDId HBDId fin wt (STAId Γθ⊆Γ) =
    tr (λ qq → qq , Δ ⊢ e :: τ) eq (weaken-ta-Γ∪ frsh wt)
    where
      eq : Γθ ∪ (Γ ∖ Γθ) == Γ
      eq = funext guts
        where
          guts : (x : Nat) → (Γθ ∪ (Γ ∖ Γθ)) x == Γ x
          guts x with Γθ x in Γθx
          ... | Some τθ = ! (Γθ⊆Γ x τθ Γθx)
          ... | None with Γθ x
          ... | None = refl
          ... | Some _ = abort (some-not-none Γθx)

      frsh : ∀{x} →
             dom (Γ ∖ Γθ) x →
             fresh x e
      frsh (τ' , x∈Γ∖Γθ) =
        binders-fresh wt (ub (τ' , dom-diff-dom-l {Γ1 = Γ} {Γ2 = Γθ} x∈Γ∖Γθ))
                      (dom-diff-apart-r {Γ1 = Γ} {Γ2 = Γθ} x∈Γ∖Γθ)
      
  subst-env-type {Γ = Γ} {Δ = Δ} {Γθ = Γθ} {e = e} {τ = τ}
                 ub
                 (BUSubst bud buθ dbdθ) (HBUSubst hbud hbuθ dhbdθ)
                 (BDSubst {y = y} dbde yube θbde)
                 (HBDSubst {y = y} dhbde θhbde)
                 (FSubst finθ fin) wt
                 (STASubst {τ = τ'} st wt') =
    subst-type (apply-env-binders-disjoint {y = y}
                 (BUSubst bud buθ dbdθ) (BDSubst dbde yube θbde))
               (apply-env-hole-binders-disjoint {y = y}
                 (HBUSubst hbud hbuθ dhbdθ) (HBDSubst dhbde θhbde))
               fin
               (subst-env-type ub'
                               buθ hbuθ θbde θhbde finθ wt st)
               wt'
    where
      ub' : ∀{x} →
            dom (Γ ,, (y , τ')) x →
            unbound-in-e x e
      ub' {x = x} (τx , x∈∪)
        with dom-union-part (■ (y , τ')) Γ x τx x∈∪ 
      ... | Inr x∈Γ = ub (τx , x∈Γ)
      ... | Inl x∈■y
        with dom-singleton-eq (τx , x∈■y)
      ... | refl = yube
