open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import lemmas-or-append
open import lemmas-patterns
open import lemmas-satisfy
open import lemmas-values
open import matching-coherence
open import matching-determinism
open import patterns-core
open import result-judgements
open import statics-core
open import type-assignment-unicity

module progress where
  -- every expression is either final or takes a step
  progress : ∀{Δ Δp e τ} →
             ∅ , Δ , Δp ⊢ e :: τ →
             Δp ⊢ e exhaustive →
             (e final) +
               Σ[ e' ∈ ihexp ](e ↦ e')
  progress TAUnit ex = Inl (FVal VUnit)
  progress TANum ex = Inl (FVal VNum)
  progress (TAVar ()) ex
  progress (TALam x#Γ wt) ex = Inl (FVal VLam)
  progress (TAAp wt1 wt2) (EXAp ex1 ex2)
   with progress wt1 ex1 | progress wt2 ex2
  ... | Inr (_ , stp1) | p2 = Inr (_ , ITApFun stp1)
  ... | Inl (FIndet ind1) | Inl fin2 =
    Inl (FIndet (IAp ind1 fin2))
  ... | Inl (FIndet ind1) | Inr (_ , stp2) =
    Inr (_ , ITApArg (FIndet ind1) stp2 )
  ... | Inl (FVal VLam) | Inl fin2 =
    Inr (_ , ITAp fin2)
  ... | Inl (FVal VLam) | Inr (_ , stp2) =
    Inr (_ , ITApArg (FVal VLam) stp2)
  progress (TAInl wt) (EXInl ex)
    with progress wt ex
  ... | Inl fin = Inl (final-inl fin)
  ... | Inr (_ , stp) = Inr (_ , ITInl stp)
  progress (TAInr wt) (EXInr ex)
    with progress wt ex
  ... | Inl fin = Inl (final-inr fin)
  ... | Inr (_ , stp) = Inr (_ , ITInr stp)
  progress (TAMatchZPre wt (RTOneRule (RTRule pt Γ##Γp wt')))
           (EXMatchZPre exe (RTOneRule pt')
                        (PotEntails CTTruth ct ent)
                        ext)
    with progress wt exe
  ... | Inr (_ , stp) = Inr (_ , ITExpMatch stp)
  ... | Inl fin
    with matching-exhaust fin wt pt
  ... | Match (_ , mat) =
    Inr (_ , ITSuccMatch fin mat)
  ... | MayMatch mmat =
    Inl (FIndet (IMatch fin mmat))
  ... | NotMatch nmat
    with pattern-unicity pt pt'
  ... | refl , refl
    with ent wt fin (CSMSSat CSTruth)
  ... | satm =
    abort (notmat-not-satormay fin wt pt nmat satm)
  progress (TAMatchZPre wt
                        (RTRules {rs = r' / rs'}
                                 (RTRule pt Γ##Γp wt')
                                 rst))
           (EXMatchZPre exe (RTRules pt' rst')
                        (PotEntails CTTruth ct ent)
                        ext)
    with progress wt exe
  ... | Inr (_ , stp) = Inr (_ , ITExpMatch stp)
  ... | Inl fin
    with matching-exhaust fin wt pt
  ... | Match (_ , mat) =
    Inr (_ , ITSuccMatch fin mat)
  ... | MayMatch mmat =
    Inl (FIndet (IMatch fin mmat))
  ... | NotMatch nmat
    with pattern-unicity pt pt'
  ... | refl , refl
    with or-satormay (ent wt fin (CSMSSat CSTruth))
  ... | Inl satmr =
    abort (notmat-not-satormay fin wt pt nmat satmr)
  ... | Inr satmrs =
    Inr (_ , ITFailMatch fin nmat ERZPre)
  progress (TAMatchNZPre wt fin pret
                         (RTOneRule (RTRule pt Γ##Γp wt'))
                         ¬red)
           (EXMatchNZPre exe pret' (RTOneRule pt')
                         (PotEntails CTTruth ct ent)
                         expret exrestt)
    with progress wt exe
  ... | Inr (_ , stp) = Inr (_ , (ITExpMatch stp))
  ... | Inl fin
    with matching-exhaust fin wt pt
  ... | Match (_ , mat) =
    Inr (_ , ITSuccMatch fin mat)
  ... | MayMatch mmat =
    Inl (FIndet (IMatch fin mmat))
  ... | NotMatch nmat
    with pattern-unicity pt pt'
  ... | refl , refl
    with rules-target-no-target-unicity pret pret'
  ... | refl
    with or-satormay (ent wt fin (CSMSSat CSTruth))
  ... | Inl satmpre =
    abort (¬red satmpre)
  ... | Inr satmrest =
    abort (notmat-not-satormay fin wt pt nmat satmrest)
  progress (TAMatchNZPre wt fin pret
                         (RTRules {rs = r' / rs'}
                                  (RTRule pt Γ##Γp wt') rst)
                         ¬red)
           (EXMatchNZPre exe pret' (RTRules pt' rst')
                         (PotEntails CTTruth ct ent)
                         expret exrestt)
    with progress wt exe
  ... | Inr (_ , stp) = Inr (_ , (ITExpMatch stp))
  ... | Inl fin
    with matching-exhaust fin wt pt
  ... | Match (_ , mat) =
    Inr (_ , ITSuccMatch fin mat)
  ... | MayMatch mmat =
    Inl (FIndet (IMatch fin mmat))
  ... | NotMatch nmat =
    Inr (_ , ITFailMatch fin nmat (rel◆er _))
  progress (TAPair wt1 wt2) (EXPair ex1 ex2)
    with progress wt1 ex1
  ... | Inr (_ , stp1) = Inr (_ , ITPairL stp1)
  ... | Inl fin1
    with progress wt2 ex2
  ... | Inr (_ , stp2) = Inr (_ , ITPairR fin1 stp2)
  ... | Inl fin2 = Inl (final-pair fin1 fin2)
  progress (TAFst wt) (EXFst ex)
    with progress wt ex
  ... | Inr (_ , stp) = Inr (_ , ITFst stp)
  ... | Inl (FVal (VPair val1 val2)) =
    Inr (_ , ITFstPair (FVal (VPair val1 val2)))
  ... | Inl (FIndet (IPairL ind1 val2)) =
    Inr (_ , ITFstPair (FIndet (IPairL ind1 val2)))
  ... | Inl (FIndet (IPairR val1 ind2)) =
    Inr (_ , ITFstPair (FIndet (IPairR val1 ind2)))
  ... | Inl (FIndet (IPair ind1 ind2)) =
    Inr (_ , ITFstPair (FIndet (IPair ind1 ind2)))
  ... | Inl (FIndet (IAp ind1 fin2)) =
    Inl (FIndet (IFst (λ e1 e2 ()) (IAp ind1 fin2)))
  ... | Inl (FIndet (IMatch fin mmat)) =
    Inl (FIndet (IFst (λ e1 e2 ()) (IMatch fin mmat)))
  ... | Inl (FIndet (IFst npr ind)) =
    Inl (FIndet (IFst (λ e1 e2 ()) (IFst npr ind)))
  ... | Inl (FIndet (ISnd np ind)) =
    Inl (FIndet (IFst (λ e1 e2 ()) (ISnd np ind)))
  ... | Inl (FIndet IEHole) =
    Inl (FIndet (IFst (λ e1 e2 ()) IEHole))
  ... | Inl (FIndet (INEHole fin)) =
    Inl (FIndet (IFst (λ e1 e2 ()) (INEHole fin)))
  progress (TASnd wt) (EXSnd ex)
    with progress wt ex
  ... | Inr (_ , stp) = Inr (_ , ITSnd stp)
  ... | Inl (FVal (VPair val1 val2)) =
    Inr (_ , ITSndPair (FVal (VPair val1 val2)))
  ... | Inl (FIndet (IPairL ind1 val2)) =
    Inr (_ , ITSndPair (FIndet (IPairL ind1 val2)))
  ... | Inl (FIndet (IPairR val1 ind2)) =
    Inr (_ , ITSndPair (FIndet (IPairR val1 ind2)))
  ... | Inl (FIndet (IPair ind1 ind2)) =
    Inr (_ , ITSndPair (FIndet (IPair ind1 ind2)))
  ... | Inl (FIndet (IAp ind1 fin2)) =
    Inl (FIndet (ISnd (λ e1 e2 ()) (IAp ind1 fin2)))
  ... | Inl (FIndet (IMatch fin mmat)) =
    Inl (FIndet (ISnd (λ e1 e2 ()) (IMatch fin mmat)))
  ... | Inl (FIndet (IFst npr ind)) =
    Inl (FIndet (ISnd (λ e1 e2 ()) (IFst npr ind)))
  ... | Inl (FIndet (ISnd np ind)) =
    Inl (FIndet (ISnd (λ e1 e2 ()) (ISnd np ind)))
  ... | Inl (FIndet IEHole) =
    Inl (FIndet (ISnd (λ e1 e2 ()) IEHole))
  ... | Inl (FIndet (INEHole fin)) =
    Inl (FIndet (ISnd (λ e1 e2 ()) (INEHole fin)))
  progress (TAEHole u∈Δ wst) (EXEHole exσ) =
    Inl (FIndet IEHole)
  progress (TANEHole u∈Δ wst wt) (EXNEHole exσ ex)
    with progress wt ex
  ... | Inl fin = Inl (FIndet (INEHole fin))
  ... | Inr (_ , stp) = Inr (_ , ITNEHole stp)
