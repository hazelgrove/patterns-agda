open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import exchange
open import freshness
open import lemmas-disjointness
open import lemmas-freshness
open import patterns-core
open import statics-core
open import result-judgements

module weakening where
  mutual
    weaken-ta-Γ : ∀{Γ x τ' Δ e τ} →
                  fresh x e →
                  Γ , Δ ⊢ e :: τ →
                  (Γ ,, (x , τ')) , Δ ⊢ e :: τ
    weaken-ta-Γ frsh TANum = TANum
    weaken-ta-Γ {Γ = Γ} {x = x} {τ' = τ'} (FVar y≠x) (TAVar {x = y} {τ = τ} y∈Γ) =
      TAVar (x∈∪r (■ (x , τ')) Γ y τ y∈Γ (apart-singleton (flip y≠x)))
    weaken-ta-Γ {Γ = Γ} {Δ = Δ} {e = ·λ y ·[ τ1 ] e}
                (FLam x≠y frsh) (TALam {τ2 = τ2} apt wt) =
      TALam (apart-extend1 Γ (flip x≠y) apt)
            (tr (λ qq → qq , Δ ⊢ e :: τ2) (swap Γ (flip x≠y)) (weaken-ta-Γ frsh wt))
    weaken-ta-Γ (FAp frsh1 frsh2) (TAAp wt1 wt2) =
      TAAp (weaken-ta-Γ frsh1 wt1) (weaken-ta-Γ frsh2 wt2)
    weaken-ta-Γ (FInl frsh) (TAInl wt) = TAInl (weaken-ta-Γ frsh wt)
    weaken-ta-Γ (FInr frsh) (TAInr wt) = TAInr (weaken-ta-Γ frsh wt)
    weaken-ta-Γ (FMatch frsh (FZRules FNoRules rfrsh rsfrsh))
                (TAMatchZPre wt rst) =
      TAMatchZPre (weaken-ta-Γ frsh wt)
                  (weaken-rules-Γ (FRules rfrsh rsfrsh) rst)
    weaken-ta-Γ (FMatch frsh (FZRules prefrsh rfrsh postfrsh))
                (TAMatchNZPre wt fin pre post ¬red) =
      TAMatchNZPre (weaken-ta-Γ frsh wt) fin (weaken-rules-Γ prefrsh pre)
                   (weaken-rules-Γ (FRules rfrsh postfrsh) post) ¬red
    weaken-ta-Γ (FPair frsh1 frsh2) (TAPair wt1 wt2) =
      TAPair (weaken-ta-Γ frsh1 wt1) (weaken-ta-Γ frsh2 wt2)
    weaken-ta-Γ (FFst frsh) (TAFst wt) = TAFst (weaken-ta-Γ frsh wt)
    weaken-ta-Γ (FSnd frsh) (TASnd wt) = TASnd (weaken-ta-Γ frsh wt)
    weaken-ta-Γ frsh (TAEHole u∈Δ) = TAEHole u∈Δ
    weaken-ta-Γ (FNEHole frsh) (TANEHole u∈Δ wt) =
      TANEHole u∈Δ (weaken-ta-Γ frsh wt)

    weaken-rule-Γ : ∀{Γ x τ Δ r τ1 ξ τ2} →
                    fresh-r x r →
                    Γ , Δ ⊢ r :: τ1 [ ξ ]=> τ2 →
                    (Γ ,, (x , τ)), Δ ⊢ r :: τ1 [ ξ ]=> τ2
    weaken-rule-Γ {Γ = Γ} {x = u} {τ = τ} {Δ = Δ} {τ2 = τ2}
                  (FRule ubp frsh)
                  (CTRule {e = e} {Γp = Γp} {Δp = Δp} pt disj disjh wt) =
      CTRule pt
             (disjoint-parts
               (lem-apart-sing-disj (unbound-in-p-apart ubp pt)) disj)
             disjh
             (tr (λ x → x , (Δ ∪ Δp) ⊢ e :: τ2) (lem-extend-union Γ Γp u τ)
                 (weaken-ta-Γ frsh wt))
    
    weaken-rules-Γ : ∀{Γ x τ Δ rs τ1 ξ τ2} →
                     fresh-hrs x rs →
                     Γ , Δ ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                     (Γ ,, (x , τ)) , Δ ⊢ rs ::s τ1 [ ξ ]=> τ2
    weaken-rules-Γ (FRules rfrsh rsfrsh) (CTOneRule rt) =
      CTOneRule (weaken-rule-Γ rfrsh rt)
    weaken-rules-Γ (FRules rfrsh rsfrsh) (CTRules rt rst) =
      CTRules (weaken-rule-Γ rfrsh rt) (weaken-rules-Γ rsfrsh rst)
    
  mutual
    weaken-ta-Δ : ∀{Γ Δ u τ' e τ} →
                  hole-fresh u e →
                  Γ , Δ ⊢ e :: τ →
                  Γ , (Δ ,, (u , τ')) ⊢ e :: τ
    weaken-ta-Δ frsh TANum = TANum
    weaken-ta-Δ frsh (TAVar x) = TAVar x
    weaken-ta-Δ (HFLam frsh) (TALam apt wt) =
      TALam apt (weaken-ta-Δ frsh wt)
    weaken-ta-Δ (HFAp frsh1 frsh2) (TAAp wt1 wt2) =
      TAAp (weaken-ta-Δ frsh1 wt1) (weaken-ta-Δ frsh2 wt2)
    weaken-ta-Δ (HFInl frsh) (TAInl wt) = TAInl (weaken-ta-Δ frsh wt)
    weaken-ta-Δ (HFInr frsh) (TAInr wt) = TAInr (weaken-ta-Δ frsh wt)
    weaken-ta-Δ (HFMatch frsh (HFZRules HFNoRules rfrsh rsfrsh))
                (TAMatchZPre wt rst) =
      TAMatchZPre (weaken-ta-Δ frsh wt)
                  (weaken-rules-Δ (HFRules rfrsh rsfrsh) rst)
    weaken-ta-Δ (HFMatch frsh (HFZRules prefrsh rfrsh postfrsh))
                (TAMatchNZPre wt fin pre post ¬red) =
      TAMatchNZPre (weaken-ta-Δ frsh wt) fin (weaken-rules-Δ prefrsh pre)
                   (weaken-rules-Δ (HFRules rfrsh postfrsh) post) ¬red
    weaken-ta-Δ (HFPair frsh frsh₁) (TAPair wt1 wt2) =
      TAPair (weaken-ta-Δ frsh wt1) (weaken-ta-Δ frsh₁ wt2)
    weaken-ta-Δ (HFFst frsh) (TAFst wt) = TAFst (weaken-ta-Δ frsh wt)
    weaken-ta-Δ (HFSnd frsh) (TASnd wt) = TASnd (weaken-ta-Δ frsh wt)
    weaken-ta-Δ {Δ = Δ} {u = u} {τ' = τ'} {τ = τ} (HFHole {u' = u'} u≠u') (TAEHole x) =
      TAEHole (x∈∪r (■ (u , τ')) Δ u' τ x (apart-singleton (flip u≠u')))
    weaken-ta-Δ {Δ = Δ} {u = u} {τ' = τ'} {τ = τ} (HFNEHole {u' = u'} u≠u' frsh)
                (TANEHole x wt) =
      TANEHole (x∈∪r (■ (u , τ')) Δ u' τ x (apart-singleton (flip u≠u')))
               (weaken-ta-Δ frsh wt)

    weaken-rule-Δ : ∀{Γ Δ u τ r τ1 ξ τ2} →
                    hole-fresh-r u r →
                    Γ , Δ ⊢ r :: τ1 [ ξ ]=> τ2 →
                    Γ , (Δ ,, (u , τ)) ⊢ r :: τ1 [ ξ ]=> τ2
    weaken-rule-Δ {Γ = Γ} {Δ = Δ} {u = u} {τ = τ} {τ2 = τ2}
                  (HFRule hubp frsh)
                  (CTRule {e = e} {Γp = Γp} {Δp = Δp} pt disjp disjph wt) = 
      CTRule pt disjp
             (disjoint-parts
               (lem-apart-sing-disj (hole-unbound-in-p-apart hubp pt))
               disjph)
             (tr (λ x → (Γ ∪ Γp) , x ⊢ e :: τ2) (lem-extend-union Δ Δp u τ)
                 (weaken-ta-Δ frsh wt))
    
    weaken-rules-Δ : ∀{Γ Δ u τ rs τ1 ξ τ2} →
                     hole-fresh-hrs u rs →
                     Γ , Δ ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                     Γ , (Δ ,, (u , τ)) ⊢ rs ::s τ1 [ ξ ]=> τ2
    weaken-rules-Δ (HFRules rfrsh rsfrsh) (CTOneRule rt) =
      CTOneRule (weaken-rule-Δ rfrsh rt)
    weaken-rules-Δ (HFRules rfrsh rsfrsh) (CTRules rt rst) =
      CTRules (weaken-rule-Δ rfrsh rt) (weaken-rules-Δ rsfrsh rst)
