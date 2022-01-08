open import Nat
open import Prelude
open import constraints-core
open import contexts
open import disjointness
open import dynamics-core
open import exchange
open import freshness
open import freshness-decidable
open import lemmas-contexts
open import lemmas-freshness
open import lemmas-subst-satisfy
open import lemmas-subst-result
open import result-judgements
open import statics-core
open import weakening

module lemmas-subst-type where  
  mutual
    subst-type : ∀{Γ Δ x τ1 e1 τ e2} →
                 x # Γ →
                 binders-disjoint e1 e2 →
                 hole-binders-disjoint e1 e2 →
                 e2 final →
                 (Γ ,, (x , τ1)) , Δ ⊢ e1 :: τ →
                 Γ , Δ ⊢ e2 :: τ1 →
                 Γ , Δ ⊢ [ e2 / x ] e1 :: τ
    subst-type x#Γ bd hbd fin2 TANum wt2 = TANum
    subst-type {x = x} x#Γ bd hbd fin2 (TAVar {x = y} y∈) wt2
      with natEQ y x
    ... | Inl refl
      with natEQ x x
    ... | Inr x≠x = abort (x≠x refl)
    ... | Inl refl
      with some-inj y∈
    ... | refl = wt2
    subst-type {x = x} x#Γ bd hbd fin2 (TAVar {x = y} y∈) wt2
        | Inr y≠x
      with natEQ x y
    ... | Inl refl = abort (y≠x refl)
    ... | Inr x≠y = TAVar y∈
    subst-type {Γ = Γ} {x = x} x#Γ bd hbd bu
               (TALam {x = y} y# wts) wt2
      with natEQ y x
    ... | Inl refl
      with natEQ x x
    ... | Inr x≠x = abort (x≠x refl)
    ... | Inl refl = abort (some-not-none y#)
    subst-type {Γ = Γ} {x = x} x#Γ (BDLam bd ub) (HBDLam hbd) fin2
               (TALam {x = y} y# wts) wt2
        | Inr y≠x
      with natEQ x y
    ... | Inl refl = abort (y≠x refl)
    ... | Inr x≠y =
      TALam y#
            (subst-type
              (neq-apart-extend Γ x≠y x#Γ) bd hbd fin2
              (exchange-ta-Γ x≠y wts)
              (weaken-ta-Γ (binders-fresh wt2 ub y#) wt2))
    subst-type x#Γ (BDAp bd1 bd2) (HBDAp hbd1 hbd2) fin2
               (TAAp wts1 wts2) wt2 =
      TAAp (subst-type x#Γ bd1 hbd1 fin2 wts1 wt2)
           (subst-type x#Γ bd2 hbd2 fin2 wts2 wt2)
    subst-type x#Γ (BDInl bd) (HBDInl hbd) fin2 (TAInl wts) wt2 =
      TAInl (subst-type x#Γ bd hbd fin2 wts wt2)
    subst-type x#Γ (BDInr bd) (HBDInr hbd) fin2 (TAInr wts) wt2 =
      TAInr (subst-type x#Γ bd hbd fin2 wts wt2)
    subst-type x#Γ (BDMatch 1d2 (BDZRules _ rd2 _))
               (HBDMatch 1hd2 (HBDZRules _ rhd2 _)) fin2
               (TAMatchZPre wts (CTOneRule rt)) wt2 = 
      TAMatchZPre (subst-type x#Γ 1d2 1hd2 fin2 wts wt2)
                  (CTOneRule (subst-type-r x#Γ rd2 rhd2 fin2
                                           rt wt2))
    subst-type x#Γ (BDMatch 1d2 (BDZRules _ rd2 postd2))
               (HBDMatch 1hd2 (HBDZRules _ rhd2 posthd2)) fin2
               (TAMatchZPre wts (CTRules rt rst)) wt2 =
      TAMatchZPre (subst-type x#Γ 1d2 1hd2 fin2 wts wt2)
                  (CTRules (subst-type-r x#Γ rd2 rhd2 fin2 rt wt2)
                           (subst-type-rs x#Γ postd2 posthd2 fin2
                                          rst wt2))
    subst-type x#Γ (BDMatch 1d2
                            (BDZRules pred2 rd2 predpost))
               (HBDMatch 1hd2
                         (HBDZRules prehd2 rhd2 prehdpost)) fin2
               (TAMatchNZPre wts fin1 pret
                             (CTOneRule rt) ¬red) wt2 =
      TAMatchNZPre (subst-type x#Γ 1d2 1hd2 fin2 wts wt2)
                   (final-subst-final fin1 fin2)
                   (subst-type-rs x#Γ pred2 prehd2 fin2 pret wt2)
                   (subst-type-rs x#Γ (BDRules rd2 BDNoRules)
                                  (HBDRules rhd2 HBDNoRules)
                                  fin2 (CTOneRule rt) wt2)
                   λ{satm → ¬red (final-satormay-subst fin1 satm)}
    subst-type x#Γ (BDMatch 1d2 (BDZRules pred2 rd2 postd2))
               (HBDMatch 1hd2
                         (HBDZRules prehd2 rhd2 posthd2)) fin2
               (TAMatchNZPre wts fin1 pret
                                 (CTRules rt postt) ¬red) wt2 =
      TAMatchNZPre (subst-type x#Γ 1d2 1hd2 fin2 wts wt2)
                   (final-subst-final fin1 fin2)
                   (subst-type-rs x#Γ pred2 prehd2 fin2 pret wt2)
                   (subst-type-rs x#Γ (BDRules rd2 postd2)
                                  (HBDRules rhd2 posthd2)
                                  fin2 (CTRules rt postt) wt2)
                   λ{satm → ¬red (final-satormay-subst fin1 satm)}
    subst-type x#Γ (BDPair bd1 bd2) (HBDPair hbd1 hbd2) fin2
               (TAPair wts1 wts2) wt2 =
      TAPair (subst-type x#Γ bd1 hbd1 fin2 wts1 wt2)
             (subst-type x#Γ bd2 hbd2 fin2 wts2 wt2)
    subst-type x#Γ (BDFst bd) (HBDFst hbd) fin2 (TAFst wts) wt2 =
      TAFst (subst-type x#Γ bd hbd fin2 wts wt2)
    subst-type x#Γ (BDSnd bd) (HBDSnd hbd) fin2 (TASnd wts) wt2 =
      TASnd (subst-type x#Γ bd hbd fin2 wts wt2)
    subst-type x#Γ bd hbd fin2 (TAEHole u∈Δ) wt2 = TAEHole u∈Δ
    subst-type x#Γ (BDNEHole bd) (HBDNEHole hbd) fin2
               (TANEHole u∈Δ wts) wt2 =
      TANEHole u∈Δ (subst-type x#Γ bd hbd fin2 wts wt2)


    subst-type-rs : ∀{Γ Δ x τ1 rs τ ξ τ' e2} →
                    x # Γ →
                    binders-disjoint-rs rs e2 →
                    hole-binders-disjoint-rs rs e2 →
                    e2 final →
                    (Γ ,, (x , τ1)) , Δ ⊢ rs ::s τ [ ξ ]=> τ' →
                    Γ , Δ ⊢ e2 :: τ1 →
                    Γ , Δ ⊢ [ e2 / x ]rs rs ::s τ [ ξ ]=> τ'
    subst-type-rs x#Γ (BDRules rd2 rsd2)
                  (HBDRules rhd2 rshd2) fin2 (CTOneRule rt) wt2 =
      CTOneRule (subst-type-r x#Γ rd2 rhd2 fin2 rt wt2)
    subst-type-rs x#Γ (BDRules rd2 rsd2)
                  (HBDRules rhd2 rshd2) fin2 (CTRules rt rst) wt2 =
      CTRules (subst-type-r x#Γ rd2 rhd2 fin2 rt wt2)
              (subst-type-rs x#Γ rsd2 rshd2 fin2 rst wt2)
              
    subst-type-r : ∀{Γ Δ x τ1 r τ ξ τ' e2} →
                   x # Γ →
                   binders-disjoint-r r e2 →
                   hole-binders-disjoint-r r e2 →
                   e2 final →
                   (Γ ,, (x , τ1)) , Δ ⊢ r :: τ [ ξ ]=> τ' →
                   Γ , Δ ⊢ e2 :: τ1 →
                   Γ , Δ ⊢ [ e2 / x ]r r :: τ [ ξ ]=> τ'
    subst-type-r {Γ = Γ} {Δ = Δ} {x = x} {τ1 = τ1} {e2 = e2} x#Γ
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
             (subst-type (apart-parts Γ Γp x x#Γ
                           (unbound-in-p-apart-Γp pt ub))
                         1d2 1hd2 fin2 wts
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
