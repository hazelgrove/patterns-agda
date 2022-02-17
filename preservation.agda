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
open import lemmas-subst-exhaustive
open import lemmas-subst-type
open import matching-coherence
open import patterns-core
open import result-judgements
open import statics-core
open import type-assignment-unicity

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
                            (RTOneRule (RTRule {e = e} {Γp = Γp}
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
                            (RTRules (RTRule {e = e} {Γp = Γp}
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
                            (RTRules (RTRule pt Γ##Γp wt')
                                     rst))
               (ITFailMatch fin nmat ERZPre) =
    TAMatchNZPre wt fin
                 (RTOneRule (RTRule pt Γ##Γp wt')) rst
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
                             (RTOneRule (RTRule {e = e} {Γp = Γp}
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
                             (RTRules (RTRule {e = e} {Γp = Γp}
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
               (TAMatchNZPre {e = e} {ξpre = ξpre} wt fin
                             pret
                             (RTRules {ξr = ξr} {ξrs = ξrs}
                                      (RTRule pt Γ##Γp wt')
                                      postt)
                             ¬red)
               (ITFailMatch fin₁ nmat (ERNZPre er)) =
    TAMatchNZPre wt fin
                 (rules-erase-constr (ERNZPre er)
                                     pret
                                     (RTOneRule (RTRule pt Γ##Γp wt')))
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
  

  exhaustive-targets-erase : ∀{Δp rs-pre r rs-post rss} →
                             erase-r (rs-pre / r / rs-post) rss →
                             Δp ⊢ rs-pre exhaustive-targets →
                             Δp ⊢ (r / rs-post) exhaustive-targets →
                             Δp ⊢ rss exhaustive-targets
  exhaustive-targets-erase ERZPre expret exrestt = exrestt
  exhaustive-targets-erase {rs-pre = (p => e) / rs}
                           (ERNZPre er) (EXRules exe exrs) exrestt =
    EXRules exe (exhaustive-targets-erase er exrs exrestt)
  
  exhaustive-preservation : ∀{Δp e1 e2} →
                            binders-unique e1 →
                            hole-binders-unique e1 →
                            Δp ⊢ e1 exhaustive →
                            e1 ↦ e2 →
                            Δp ⊢ e2 exhaustive
  exhaustive-preservation (BUAp bu1 bu2 bd) (HBUAp hbu1 hbu2 hbd)
                          (EXAp ex1 ex2) (ITApFun stp) =
    EXAp (exhaustive-preservation bu1 hbu1 ex1 stp) ex2
  exhaustive-preservation (BUAp bu1 bu2 bd) (HBUAp hbu1 hbu2 hbd)
                          (EXAp ex1 ex2) (ITApArg fin stp) =
    EXAp ex1 (exhaustive-preservation bu2 hbu2 ex2 stp)
  exhaustive-preservation (BUAp bu1 bu2 bd) (HBUAp hbu1 hbu2 hbd)
                          (EXAp (EXLam ex1) ex2) (ITAp fin) =
    subst-exhaustive ex1 ex2
  exhaustive-preservation (BUPair bu1 bu2 bd) (HBUPair hbu1 hbu2 hbd)
                          (EXPair ex1 ex2) (ITPairL stp) =
    EXPair (exhaustive-preservation bu1 hbu1 ex1 stp) ex2
  exhaustive-preservation (BUPair bu1 bu2 bd) (HBUPair hbu1 hbu2 hbd)
                          (EXPair ex1 ex2) (ITPairR fin stp) =
    EXPair ex1 (exhaustive-preservation bu2 hbu2 ex2 stp)
  exhaustive-preservation (BUFst bu) (HBUFst hbu)
                          (EXFst ex1) (ITFst stp) =
    EXFst (exhaustive-preservation bu hbu ex1 stp)
  exhaustive-preservation (BUFst bu) (HBUFst hbu)
                          (EXFst (EXPair ex1 ex2)) (ITFstPair fin) = ex1
  exhaustive-preservation (BUSnd bu) (HBUSnd hbu)
                          (EXSnd ex1) (ITSnd stp) =
    EXSnd (exhaustive-preservation bu hbu ex1 stp)
  exhaustive-preservation (BUSnd bu) (HBUSnd hbu)
                          (EXSnd (EXPair ex1 ex2)) (ITSndPair fin) = ex2
  exhaustive-preservation (BUInl bu) (HBUInl hbu)
                          (EXInl ex1) (ITInl stp) =
    EXInl (exhaustive-preservation bu hbu ex1 stp)
  exhaustive-preservation (BUInr bu) (HBUInr hbu)
                          (EXInr ex1) (ITInr stp) =
    EXInr (exhaustive-preservation bu hbu ex1 stp)
  exhaustive-preservation (BUMatch bue buzrs bd) (HBUMatch hbue hbuzrs hbd)
                          (EXMatchZPre ex rst ent exts) (ITExpMatch stp) =
    EXMatchZPre (exhaustive-preservation bue hbue ex stp)
                rst
                ent
                exts
  exhaustive-preservation (BUMatch bue buzrs bd) (HBUMatch hbue hbuzrs hbd)
                          (EXMatchZPre ex rst ent (EXRules exet exrst))
                          (ITSuccMatch fin mat) =
    substs-exhaustive (mat-substs-exhaustive ex mat)
                      exet
  exhaustive-preservation (BUMatch bue buzrs bd) (HBUMatch hbue hbuzrs hbd)
                          (EXMatchZPre ex (RTRules pt rst) ent (EXRules exe exrs))
                          (ITFailMatch fin nmat ERZPre) =
    EXMatchNZPre ex (RTOneRule pt) rst ent (EXRules exe EXNoRules) exrs
  exhaustive-preservation (BUMatch bue buzrs bd) (HBUMatch hbue hbuzrs hbd)
                          (EXMatchNZPre ex pret restt ent expret exrestt)
                          (ITExpMatch stp) =
    EXMatchNZPre (exhaustive-preservation bue hbue ex stp)
                 pret restt ent expret exrestt
  exhaustive-preservation (BUMatch bue buzrs bd) (HBUMatch hbue hbuzrs hbd)
                          (EXMatchNZPre ex pret restt ent exprett
                                        (EXRules exet expostt))
                          (ITSuccMatch fin mat) =
    substs-exhaustive (mat-substs-exhaustive ex mat) exet
  exhaustive-preservation (BUMatch bue buzrs bd) (HBUMatch hbue hbuzrs hbd)
                          (EXMatchNZPre {ξpre = ξpre} {ξrest = ξr ∨ ξrs}
                                        ex pret
                                        (RTRules pt postt)
                                        (PotEntails {τ = τ}
                                                    CTTruth
                                                    (CTOr ctpre (CTOr ctr ctrs))
                                                    ent)
                                        expret
                                        (EXRules exet expostt))
                          (ITFailMatch fin nmat er) =
    EXMatchNZPre ex
                 (rules-erase-constr-no-target er pret (RTOneRule pt))
                 postt
                 (PotEntails CTTruth (CTOr (∨+-type ctpre ctr) ctrs) ent')
                 (exhaustive-targets-erase er expret (EXRules exet EXNoRules))
                 expostt
    where
      ent' : ∀{Δ Δp e} →
             ∅ , Δ , Δp ⊢ e :: τ →
             e final →
             e ⊧̇†? ·⊤ →
             e ⊧̇†? ((ξpre ∨+ ξr) ∨ ξrs)
      ent' wt fin satt
        with or-satormay (ent wt fin satt)
      ... | Inl satpre =
        satormay-or-l (satormay-∨-satormay-∨+ (satormay-or-l satpre))
      ... | Inr satrest
        with or-satormay satrest
      ... | Inl satr =
        satormay-or-l (satormay-∨-satormay-∨+ (satormay-or-r satr))
      ... | Inr satrs =
        satormay-or-r satrs
  exhaustive-preservation (BUNEHole buσ bu bd) (HBUNEHole hbuσ hbu hbd)
                          (EXNEHole exσ ex1) (ITNEHole stp) =
    EXNEHole exσ (exhaustive-preservation bu hbu ex1 stp)
