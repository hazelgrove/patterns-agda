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
    expr-type-unicity : ∀{Γ Δ e τ τ'} →
                        Γ , Δ ⊢ e :: τ →
                        Γ , Δ ⊢ e :: τ' →
                        τ == τ'
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
    expr-type-unicity {Δ = Δ} (TAEHole x) (TAEHole x') =
      ctx-unicity {Γ = Δ} x x'
    expr-type-unicity {Δ = Δ} (TANEHole x wt) (TANEHole x' wt') =
      ctx-unicity {Γ = Δ} x x'

    -- variable and hole patterns may be assigned any type,
    -- so unicity does not actually hold for patterns. However,
    -- if we assume a given type for the pattern, then unicity
    -- holds for all other aspects
    pattern-unicity : ∀{p τ ξ ξ' Γ Γ' Δ Δ'} →
                      p :: τ [ ξ ]⊣ Γ , Δ →
                      p :: τ [ ξ' ]⊣ Γ' , Δ' →
                      (ξ == ξ') × (Γ == Γ') × (Δ == Δ')
    pattern-unicity PTVar PTVar = refl , refl , refl
    pattern-unicity PTNum PTNum = refl , refl , refl
    pattern-unicity (PTInl pt) (PTInl pt')
      with pattern-unicity pt pt'
    ... | refl , refl , refl = refl , refl , refl
    pattern-unicity (PTInr pt) (PTInr pt')
      with pattern-unicity pt pt'
    ... | refl , refl , refl  = refl , refl , refl
    pattern-unicity (PTPair dis dish pt1 pt2) (PTPair dis' dish' pt1' pt2')
      with pattern-unicity pt1 pt1' | pattern-unicity pt2 pt2'
    ... | refl , refl , refl | refl , refl , refl = refl , refl , refl
    pattern-unicity PTEHole PTEHole = refl , refl , refl
    pattern-unicity (PTNEHole pt apt) (PTNEHole pt' apt')
      with pattern-unicity pt pt'
    ... | refl , refl , refl = refl , refl , refl
    pattern-unicity PTWild PTWild = refl , refl , refl
    
    rule-unicity : ∀{Γ Δ r τ1 ξ ξ' τ2 τ2'} →
                   Γ , Δ ⊢ r :: τ1 [ ξ ]=> τ2 →
                   Γ , Δ ⊢ r :: τ1 [ ξ' ]=> τ2' →
                   (ξ == ξ') × (τ2 == τ2')
    rule-unicity (CTRule pt dis dish wt) (CTRule pt' dis' dish' wt')
      with pattern-unicity pt pt'
    ... | refl , refl , refl
      with expr-type-unicity wt wt'
    ... | refl = refl , refl
    
    rules-unicity : ∀{Γ Δ rs τ1 ξrs ξrs' τ2 τ2'} →
                    Γ , Δ ⊢ rs ::s τ1 [ ξrs ]=> τ2 →
                    Γ , Δ ⊢ rs ::s τ1 [ ξrs' ]=> τ2' →
                    (ξrs == ξrs') × (τ2 == τ2')
    rules-unicity (CTOneRule wt) (CTOneRule wt')
      with rule-unicity wt wt'
    ... | refl , refl = refl , refl
    rules-unicity (CTRules wt wts) (CTRules wt' wts')
      with rule-unicity wt wt'
    ... | refl , refl
      with rules-unicity wts wts'
    ... | refl , refl = refl , refl
