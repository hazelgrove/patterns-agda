open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import binders-disjointness
open import binders-uniqueness
open import dynamics-core
open import finality
open import lemmas-contexts
open import lemmas-or-append
open import lemmas-patterns
open import lemmas-satisfy
open import lemmas-subst-type
open import matching-coherence
open import patterns-core
open import statics-core
open import result-judgements

module preservation where
  preservation : ∀{Δ Δp e1 τ e2} →
                 binders-unique e1 →
                 hole-binders-unique e1 →
                 ∅ , Δ , Δp ⊢ e1 :: τ →
                 e1 ↦ e2 →
                 ∅ , Δ , Δp ⊢ e2 :: τ
  preservation (BUAp bu1 bu2 bd) (HBUAp hbu1 hbu2 hbd)
               (TAAp wt1 wt2) (ITApFun stp) = 
    TAAp (preservation bu1 hbu1 wt1 stp) wt2
  preservation (BUAp bu1 bu2 bd) (HBUAp hbu1 hbu2 hbd)
               (TAAp wt1 wt2) (ITApArg eval stp) =
    TAAp wt1 (preservation bu2 hbu2 wt2 stp)
  preservation (BUAp bu1 bu2 (BDLam ub bd))
               (HBUAp hbu1 hbu2 (HBDLam hbd))
               (TAAp (TALam x#Γ wt1) wt2) (ITAp fin) =
    subst-type bd hbd fin wt1 wt2
  preservation (BUInl bu) (HBUInl hbu) (TAInl wt) (ITInl stp) =
    TAInl (preservation bu hbu wt stp)
  preservation (BUInr bu) (HBUInr hbu) (TAInr wt) (ITInr stp) =
    TAInr (preservation bu hbu wt stp)
  preservation (BUMatch bu burs bdrs)
               (HBUMatch hbu hburs hbdrs)
               (TAMatchZPre wt rst) (ITExpMatch stp) =
    TAMatchZPre (preservation bu hbu wt stp) rst
  preservation {Δ = Δ} {Δp = Δp} {τ = τ}
               (BUMatch bu
                        (BUZRules _ (BURules (BURule bup _ _) _ _) _)
                        (BDZRules _ (BDRules (BDRule pbde _) _)))
               (HBUMatch hbu hburs hbdrs)
               (TAMatchZPre wt
                            (CTOneRule (CTRule {e = e} {Γp = Γp}
                                               pt Γ##Γp wt')))
               (ITSuccMatch fin mat) =
    substs-type (mat-substs-simultaneous bu bup pbde mat)
                (mat-substs-type wt pt Γ##Γp mat)
                (tr (λ qq → qq , Δ , Δp ⊢ e :: τ)
                    (! (∪-identityʳ Γp))
                    wt')
  preservation {Δ = Δ} {Δp = Δp} {τ = τ}
               (BUMatch bu
                        (BUZRules _ (BURules (BURule bup _ _) _ _) _)
                        (BDZRules _ (BDRules (BDRule pbde _) _)))
               (HBUMatch hbu hburs hbdrs)
               (TAMatchZPre wt
                            (CTRules (CTRule {e = e} {Γp = Γp}
                                             pt Γ##Γp wt')
                                     rst))
               (ITSuccMatch fin mat) =
    substs-type (mat-substs-simultaneous bu bup pbde mat)
                (mat-substs-type wt pt Γ##Γp mat)
                (tr (λ qq → qq , Δ , Δp ⊢ e :: τ)
                    (! (∪-identityʳ Γp))
                    wt')
  preservation (BUMatch bu burs bdrs)
               (HBUMatch hbu hburs hbdrs)
               (TAMatchZPre wt
                            (CTRules (CTRule pt Γ##Γp wt')
                                     rst))
               (ITFailMatch fin nmat ERZPre) =
    TAMatchNZPre wt fin
                 (CTOneRule (CTRule pt Γ##Γp wt')) rst
                 (notmat-not-satormay fin wt pt nmat)
  preservation (BUMatch bu burs bdrs)
               (HBUMatch hbu hburs hbdrs)
               (TAMatchNZPre wt fin pret postt ¬red)
               (ITExpMatch stp) =
    abort (final-step-not fin stp)
  preservation {Δ = Δ} {Δp = Δp} {τ = τ}
               (BUMatch bu
                        (BUZRules _ (BURules (BURule bup _ _) _ _) _)
                        (BDZRules _ (BDRules (BDRule pbde _) _)))
               (HBUMatch hbu hburs hbdrs)
               (TAMatchNZPre wt fin pre
                             (CTOneRule (CTRule {e = e} {Γp = Γp}
                                                pt Γ##Γp wt'))
                             ¬red)
               (ITSuccMatch fin₁ mat) =
    substs-type (mat-substs-simultaneous bu bup pbde mat)
                (mat-substs-type wt pt Γ##Γp mat)
                (tr (λ qq → qq , Δ , Δp ⊢ e :: τ)
                    (! (∪-identityʳ Γp))
                    wt')
  preservation {Δ = Δ} {Δp = Δp} {τ = τ}
               (BUMatch bu
                        (BUZRules _ (BURules (BURule bup _ _) _ _) _)
                        (BDZRules _ (BDRules (BDRule pbde _) _)))
               (HBUMatch hbu hburs hbdrs)
               (TAMatchNZPre wt fin pre
                             (CTRules (CTRule {e = e} {Γp = Γp}
                                              pt Γ##Γp wt')
                                      rst)
                             ¬red)
               (ITSuccMatch fin₁ mat) =
    substs-type (mat-substs-simultaneous bu bup pbde mat)
                (mat-substs-type wt pt Γ##Γp mat)
                (tr (λ qq → qq , Δ , Δp ⊢ e :: τ)
                    (! (∪-identityʳ Γp))
                    wt')
  preservation (BUMatch bu burs bdrs)
               (HBUMatch hbu hburs hbdrs)
               (TAMatchNZPre {e = e} {ξpre = ξpre} wt fin pret
                             (CTRules {ξr = ξr} {ξrs = ξrs}
                                      (CTRule pt Γ##Γp wt')
                                      postt)
                             ¬red)
               (ITFailMatch fin₁ nmat (ERNZPre er)) =
    TAMatchNZPre wt fin
                 (rs-constr-append (ERNZPre er) pret
                                   (CTRule pt Γ##Γp wt'))
                 postt ¬red'
    where
      -- need to add ξr to the end of the chain of ∨s in ξpre
      ¬red' : e ⊧̇†? (ξpre ∨+ ξr) → ⊥
      ¬red' satm with or-satormay (satormay-∨+-satormay-∨ satm)
      ... | Inl satmpre = ¬red satmpre
      ... | Inr satmr =
        notmat-not-satormay fin wt pt nmat satmr
  preservation (BUPair bu1 bu2 bd) (HBUPair hbu1 hbu2 hbd)
               (TAPair wt1 wt2) (ITPairL stp) =
    TAPair (preservation bu1 hbu1 wt1 stp) wt2
  preservation (BUPair bu1 bu2 bd) (HBUPair hbu1 hbu2 hbd)
               (TAPair wt1 wt2) (ITPairR val1 stp) =
    TAPair wt1 (preservation bu2 hbu2 wt2 stp)
  preservation (BUFst bu) (HBUFst hbu) (TAFst wt)
               (ITFst stp) =
    TAFst (preservation bu hbu wt stp)
  preservation (BUFst bu) (HBUFst hbu)
               (TAFst wt) (ITFstPair fin)
    with wt
  ... | TAPair wt1 wt2 = wt1
  preservation (BUSnd bu) (HBUSnd hbu) (TASnd wt)
               (ITSnd stp) = 
    TASnd (preservation bu hbu wt stp)
  preservation (BUSnd bu) (HBUSnd hbu)
               (TASnd wt) (ITSndPair fin)
    with wt
  ... | TAPair wt1 wt2 = wt2
  preservation (BUNEHole buσ bue σbde) (HBUNEHole hbuσ hbue σhbde)
               (TANEHole u∈Δ wst wt) (ITNEHole stp) =
    TANEHole u∈Δ wst (preservation bue hbue wt stp)
  
