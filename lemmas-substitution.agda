open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import exchange
open import freshness
open import lemmas-disjointness
open import lemmas-freshness
open import patterns-core
open import result-judgements
open import statics-core
open import weakening

module lemmas-substitution where
  mutual
    binders-fresh-r : ∀{Γ Δ r τ1 ξ τ2 x} →
                      Γ , Δ ⊢ r :: τ1 [ ξ ]=> τ2 →
                      unbound-in-r x r →
                      x # Γ →
                      fresh-r x r
    binders-fresh-r {Γ = Γ} {x = x}
                    (CTRule {Γp = Γp} pt Γ##Γp Δ##Δp wt)
                    (UBRule xubp xube) x#Γ =        
      FRule xubp
            (binders-fresh wt xube
                           (apart-parts Γ Γp x x#Γ
                                        (unbound-in-p-apart pt xubp)))

    binders-fresh-rs : ∀{Γ Δ rs τ1 ξ τ2 x} →
                       Γ , Δ ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                       unbound-in-rs x rs →
                       x # Γ →
                       fresh-rs x rs
    binders-fresh-rs (CTOneRule rt) (UBRules xubr _) x#Γ = 
      FRules (binders-fresh-r rt xubr x#Γ) FNoRules
    binders-fresh-rs (CTRules rt rst)
                     (UBRules xubr xubrs) x#Γ =
      FRules (binders-fresh-r rt xubr x#Γ)
             (binders-fresh-rs rst xubrs x#Γ)
    
    binders-fresh : ∀{Γ Δ e τ x} →
                    Γ , Δ ⊢ e :: τ →
                    unbound-in x e →
                    x # Γ →
                    fresh x e
    binders-fresh TANum UBNum x#Γ = FNum
    binders-fresh (TAVar {x = y} y∈Γ) UBVar x#Γ =
      FVar (λ{ refl → somenotnone ((! y∈Γ) · x#Γ) })
    binders-fresh {Γ = Γ} (TALam {x = y} y#Γ wt)
                  (UBLam x≠y xub) x#Γ =
      FLam x≠y (binders-fresh wt xub (apart-extend1 Γ x≠y x#Γ))
    binders-fresh (TAAp wt1 wt2) (UBAp ub1 ub2) x#Γ =
      FAp (binders-fresh wt1 ub1 x#Γ) (binders-fresh wt2 ub2 x#Γ)
    binders-fresh (TAInl wt) (UNInl ub) x#Γ =
      FInl (binders-fresh wt ub x#Γ)
    binders-fresh (TAInr wt) (UBInr ub) x#Γ =
      FInr (binders-fresh wt ub x#Γ)
    binders-fresh (TAMatchZPre {r = p => d} wt (CTOneRule rt))
                  (UBMatch xube (UBZRules UBNoRules ubr _)) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules FNoRules
                      (binders-fresh-r rt ubr x#Γ)
                      FNoRules)
    binders-fresh (TAMatchZPre {r = p => d} wt (CTRules rt rst))
                  (UBMatch xube (UBZRules _ ubr xubrs)) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules FNoRules
                      (binders-fresh-r rt ubr x#Γ)
                      (binders-fresh-rs rst xubrs x#Γ))
    binders-fresh (TAMatchNZPre wt fin pret (CTOneRule rt) ¬red)
                  (UBMatch xube (UBZRules xubpre xubr xubpost)) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules (binders-fresh-rs pret xubpre x#Γ)
                      (binders-fresh-r rt xubr x#Γ)
                      FNoRules)
    binders-fresh (TAMatchNZPre wt fin pret (CTRules rt postt) ¬red)
                  (UBMatch xube (UBZRules xubpre xubr xubpost)) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules (binders-fresh-rs pret xubpre x#Γ)
                      (binders-fresh-r rt xubr x#Γ)
                      (binders-fresh-rs postt xubpost x#Γ))
    binders-fresh (TAPair wt1 wt2) (UBPair ub1 ub2) x#Γ =
      FPair (binders-fresh wt1 ub1 x#Γ)
            (binders-fresh wt2 ub2 x#Γ)
    binders-fresh (TAFst wt) (UBFst ub) x#Γ =
      FFst (binders-fresh wt ub x#Γ)
    binders-fresh (TASnd wt) (UBSnd ub) x#Γ =
      FSnd (binders-fresh wt ub x#Γ)
    binders-fresh (TAEHole x) UBEHole x#Γ = FEHole
    binders-fresh (TANEHole x wt) (UBNEHole ub) x#Γ =
      FNEHole (binders-fresh wt ub x#Γ)
      
  mutual
    subst-type-r : ∀{Γ Δ x τ1 r τ ξ τ' e2} →
                   x # Γ →
                   binders-disjoint-r r e2 →
                   binders-unique e2 →
                   (Γ ,, (x , τ1)) , Δ ⊢ r :: τ [ ξ ]=> τ' →
                   Γ , Δ ⊢ e2 :: τ1 →
                   Γ , Δ ⊢ [ e2 / x ]r r :: τ [ ξ ]=> τ'
    subst-type-r {Γ = Γ} {x = x} {τ1 = τ1} x#Γ
                 (BDRule {p = p} pd2 1d2) bu
                 (CTRule {Γp = Γp} pt Γ,##Γp Δ##Δp wts) wt2
      with unbound-in-p-dec x p
    ... | Inr ¬ub =
      abort (¬ub (apart-unbound-in-p
                    pt
                    (lem-disj-sing-apart (disjoint-union1 Γ,##Γp))))
    ... | Inl ub rewrite ! (lem-extend-union Γ Γp x τ1) =
      CTRule pt (disjoint-union2 {Γ1 = ■ (x , τ1)} {Γ2 = Γ} Γ,##Γp) Δ##Δp
             (subst-type (apart-parts Γ Γp x x#Γ
                                      (unbound-in-p-apart pt ub))
                         1d2 bu wts
                         {!wt2!})
                                             
    subst-type-rs : ∀{Γ Δ x τ1 rs τ ξ τ' e2} →
                    x # Γ →
                    binders-disjoint-rs rs e2 →
                    binders-unique e2 →
                    (Γ ,, (x , τ1)) , Δ ⊢ rs ::s τ [ ξ ]=> τ' →
                    Γ , Δ ⊢ e2 :: τ1 →
                    Γ , Δ ⊢ [ e2 / x ]rs rs ::s τ [ ξ ]=> τ'
    subst-type-rs = {!!}
    
    subst-type : ∀{Γ Δ x τ1 e1 τ e2} →
                 x # Γ →
                 binders-disjoint e1 e2 →
                 binders-unique e2 →
                 (Γ ,, (x , τ1)) , Δ ⊢ e1 :: τ →
                 Γ , Δ ⊢ e2 :: τ1 →
                 Γ , Δ ⊢ [ e2 / x ] e1 :: τ
    subst-type x#Γ bd bu TANum wt2 = TANum
    subst-type {x = x} x#Γ bd bu (TAVar {x = y} y∈) wt2
      with natEQ y x
    ... | Inl refl
      with natEQ x x
    ... | Inr x≠x = abort (x≠x refl)
    ... | Inl refl
      with someinj y∈
    ... | refl = wt2
    subst-type {x = x} x#Γ bd bu (TAVar {x = y} y∈) wt2
        | Inr y≠x
      with natEQ x y
    ... | Inl refl = abort (y≠x refl)
    ... | Inr x≠y = TAVar y∈
    subst-type {Γ = Γ} {x = x} x#Γ bd bu (TALam {x = y} y# wts) wt2
      with natEQ y x
    ... | Inl refl
      with natEQ x x
    ... | Inr x≠x = abort (x≠x refl)
    ... | Inl refl = abort (somenotnone y#)
    subst-type {Γ = Γ} {x = x} x#Γ (BDLam bd ub) bu (TALam {x = y} y# wts) wt2
        | Inr y≠x
      with natEQ x y
    ... | Inl refl = abort (y≠x refl)
    ... | Inr x≠y =
      TALam y#
            (subst-type (apart-extend1 Γ x≠y x#Γ) bd bu
                        (exchange-ta-Γ x≠y wts)
                        (weaken-ta-Γ (binders-fresh wt2 ub y#) wt2))
    subst-type x#Γ (BDAp bd1 bd2) bu (TAAp wts1 wts2) wt2 =
      TAAp (subst-type x#Γ bd1 bu wts1 wt2)
           (subst-type x#Γ bd2 bu wts2 wt2)
    subst-type x#Γ (BDInl bd) bu (TAInl wts) wt2 =
      TAInl (subst-type x#Γ bd bu wts wt2)
    subst-type x#Γ (BDInr bd) bu (TAInr wts) wt2 =
      TAInr (subst-type x#Γ bd bu wts wt2)
    subst-type x#Γ (BDMatch 1d2 (BDZRules _ rd2 _)) bu
               (TAMatchZPre wts (CTOneRule rt)) wt2 = 
      TAMatchZPre (subst-type x#Γ 1d2 bu wts wt2)
                  (CTOneRule (subst-type-r x#Γ rd2 bu rt wt2))
    subst-type x#Γ (BDMatch 1d2 (BDZRules _ rd2 postd2)) bu
               (TAMatchZPre wts (CTRules rt rst)) wt2 =
      TAMatchZPre (subst-type x#Γ 1d2 bu wts wt2)
                  (CTRules (subst-type-r x#Γ rd2 bu rt wt2)
                           (subst-type-rs x#Γ postd2 bu rst wt2))
    subst-type x#Γ (BDMatch 1d2 (BDZRules pred2 rd2 predpost)) bu
                   (TAMatchNZPre wts fin pret (CTOneRule rt) ¬red) wt2 =
      TAMatchNZPre (subst-type x#Γ 1d2 bu wts wt2)
                   {!fin!}
                   (subst-type-rs x#Γ pred2 bu pret wt2)
                   (subst-type-rs x#Γ (BDRules rd2 BDNoRules) bu (CTOneRule rt) wt2)
                   {!!}
    subst-type x#Γ (BDMatch 1d2 (BDZRules pred2 rd2 postd2)) bu
                   (TAMatchNZPre wts fin pret (CTRules rt postt) ¬red) wt2 =
      TAMatchNZPre (subst-type x#Γ 1d2 bu wts wt2)
                   {!!}
                   (subst-type-rs x#Γ pred2 bu pret wt2)
                   (subst-type-rs x#Γ (BDRules rd2 postd2) bu (CTRules rt postt) wt2)
                   {!!}
    subst-type x#Γ (BDPair bd1 bd2) bu (TAPair wts1 wts2) wt2 =
      TAPair (subst-type x#Γ bd1 bu wts1 wt2)
             (subst-type x#Γ bd2 bu wts2 wt2)
    subst-type x#Γ (BDFst bd) bu (TAFst wts) wt2 =
      TAFst (subst-type x#Γ bd bu wts wt2)
    subst-type x#Γ (BDSnd bd) bu (TASnd wts) wt2 =
      TASnd (subst-type x#Γ bd bu wts wt2)
    subst-type x#Γ bd bu (TAEHole u∈Δ) wt2 = TAEHole u∈Δ
    subst-type x#Γ (BDNEHole bd) bu (TANEHole u∈Δ wts) wt2 =
      TANEHole u∈Δ (subst-type x#Γ bd bu wts wt2)


