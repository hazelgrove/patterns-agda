open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import lemmas-contexts
open import patterns-core
open import result-judgements
open import statics-core

module type-assignment-unicity where  
  mutual
    expr-type-unicity : ∀{Γ Δ Δp e τ τ'} →
                        Γ , Δ , Δp ⊢ e :: τ →
                        Γ , Δ , Δp ⊢ e :: τ' →
                        τ == τ'
    expr-type-unicity TAUnit TAUnit = refl
    expr-type-unicity TANum TANum = refl
    expr-type-unicity {Γ = Γ} (TAVar wt) (TAVar wt') =
      ctx-unicity {Γ = Γ} wt wt'
    expr-type-unicity (TALam apt wt) (TALam apt' wt')
      with expr-type-unicity wt wt'
    ... | refl = refl
    expr-type-unicity (TAAp wt1 wt2) (TAAp wt1' wt2')
      with expr-type-unicity wt1 wt1'
    ... | refl = refl
    expr-type-unicity (TAInl wt) (TAInl wt')
      with expr-type-unicity wt wt'
    ... | refl = refl
    expr-type-unicity (TAInr wt) (TAInr wt')
      with expr-type-unicity wt wt'
    ... | refl = refl
    expr-type-unicity (TAMatchZPre wt rst) (TAMatchZPre wt' rst')
      with expr-type-unicity wt wt'
    ... | refl
      with rules-unicity rst rst'
    ... | refl , refl = refl
    expr-type-unicity (TAMatchNZPre wt fin pre post ¬satm)
                      (TAMatchNZPre wt' fin' pre' post' ¬satm')
      with expr-type-unicity wt wt'
    ... | refl
      with rules-unicity pre pre'
    ... | refl , refl = refl
    expr-type-unicity (TAPair wt1 wt2) (TAPair wt1' wt2')
      with expr-type-unicity wt1 wt1' | expr-type-unicity wt2 wt2'
    ... | refl | refl = refl
    expr-type-unicity (TAFst wt) (TAFst wt')
      with expr-type-unicity wt wt'
    ... | refl = refl
    expr-type-unicity (TASnd wt) (TASnd wt')
      with expr-type-unicity wt wt'
    ... | refl = refl
    expr-type-unicity {Δ = Δ} (TAEHole x∈Δ st) (TAEHole x∈Δ' st')
      with ctx-unicity {Γ = Δ} x∈Δ x∈Δ'
    ... | refl = refl
    expr-type-unicity {Δ = Δ} (TANEHole x∈Δ st wt) (TANEHole x∈Δ' st' wt')
      with ctx-unicity {Γ = Δ} x∈Δ x∈Δ'
    ... | refl = refl
    
    -- variable and hole patterns may be assigned any type,
    -- so unicity does not actually hold for patterns, and thus
    -- also does not hole for rules. However, if we assume a
    -- given type for the pattern, then unicity holds for all
    -- other arguments
    rules-unicity : ∀{Γ Δ Δp rs τ1 ξrs ξrs' τ2 τ2'} →
                    Γ , Δ , Δp ⊢ rs ::s τ1 [ ξrs ]=> τ2 →
                    Γ , Δ , Δp ⊢ rs ::s τ1 [ ξrs' ]=> τ2' →
                    (ξrs == ξrs') × (τ2 == τ2')
    rules-unicity (RTOneRule wt) (RTOneRule wt')
      with rule-unicity wt wt'
    ... | refl , refl = refl , refl
    rules-unicity (RTRules wt wts) (RTRules wt' wts')
      with rule-unicity wt wt'
    ... | refl , refl
      with rules-unicity wts wts'
    ... | refl , refl = refl , refl
                       
    rule-unicity : ∀{Γ Δ Δp r τ1 ξ ξ' τ2 τ2'} →
                   Γ , Δ , Δp ⊢ r :: τ1 [ ξ ]=> τ2 →
                   Γ , Δ , Δp ⊢ r :: τ1 [ ξ' ]=> τ2' →
                   (ξ == ξ') × (τ2 == τ2')
    rule-unicity (RTRule pt Γ##Γp wt1) (RTRule pt' Γ##Γp' wt1')
      with pattern-unicity pt pt'
    ... | refl , refl
      with expr-type-unicity wt1 wt1'
    ... | refl = refl , refl

    pattern-unicity : ∀{Δp p τ ξ ξ' Γ Γ'} →
                      Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                      Δp ⊢ p :: τ [ ξ' ]⊣ Γ' →
                      (ξ == ξ') × (Γ == Γ')
    pattern-unicity PTUnit PTUnit = refl , refl
    pattern-unicity PTVar PTVar = refl , refl
    pattern-unicity PTNum PTNum = refl , refl
    pattern-unicity (PTInl pt) (PTInl pt')
      with pattern-unicity pt pt'
    ... | refl , refl = refl , refl
    pattern-unicity (PTInr pt) (PTInr pt')
      with pattern-unicity pt pt'
    ... | refl , refl  = refl , refl
    pattern-unicity (PTPair disj pt1 pt2) (PTPair disj' pt1' pt2')
      with pattern-unicity pt1 pt1' | pattern-unicity pt2 pt2'
    ... | refl , refl | refl , refl = refl , refl
    pattern-unicity (PTEHole w∈Δ) (PTEHole w∈Δ') = refl , refl
    pattern-unicity (PTNEHole w∈Δ pt) (PTNEHole w∈Δ' pt')
      with pattern-unicity pt pt'
    ... | refl , refl = refl , refl
    pattern-unicity PTWild PTWild = refl , refl

  -- unicity for the rules typing without target judgements
  rules-no-target-unicity : ∀{Δp rs τ1 ξrs ξrs'} →
                            Δp ⊢ rs ::s τ1 [ ξrs ] →
                            Δp ⊢ rs ::s τ1 [ ξrs' ] →
                            ξrs == ξrs'
  rules-no-target-unicity (RTOneRule pt) (RTOneRule pt')
    with pattern-unicity pt pt'
  ... | refl , refl = refl
  rules-no-target-unicity (RTRules pt rst) (RTRules pt' rst')
    with pattern-unicity pt pt'
  ... | refl , refl
    with rules-no-target-unicity rst rst'
  ... | refl = refl
  
  -- the two rule typing judgements produce the same types
  rules-target-no-target-unicity : ∀{Γ Δ Δp rs τ1 ξrs ξrs' τ2} →
                                   Γ , Δ , Δp ⊢ rs ::s τ1 [ ξrs ]=> τ2 →
                                   Δp ⊢ rs ::s τ1 [ ξrs' ] →
                                   ξrs == ξrs'
  rules-target-no-target-unicity (RTOneRule (RTRule pt Γ##Γp wt))
                                 (RTOneRule pt')
    with pattern-unicity pt pt'
  ... | refl , refl = refl
  rules-target-no-target-unicity (RTRules (RTRule pt Γ##Γp wt) rst)
                                 (RTRules pt' rst')
    with pattern-unicity pt pt'
  ... | refl , refl 
    with rules-target-no-target-unicity rst rst'
  ... | refl = refl
