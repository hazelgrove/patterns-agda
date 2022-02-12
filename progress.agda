open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import lemmas-satisfy
open import lemmas-values
open import matching-determinism
open import patterns-core
open import result-judgements
open import statics-core

module progress where
  
  progress : ∀{Δ Δp e τ} →
             ∅ , Δp , Δ ⊢ e :: τ →
             e all-exhaustive →
             (e final) +
               Σ[ e' ∈ ihexp ](e ↦ e')
  progress TANum ex = Inl (FVal VNum)
  progress (TALam x#Γ wt) ex = Inl (FVal VLam)
  progress (TAAp wt1 wt2) (AEXAp ex1 ex2)
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
  progress (TAInl wt) (AEXInl ex)
    with progress wt ex
  ... | Inl fin = Inl (final-inl fin)
  ... | Inr (_ , stp) = Inr (_ , ITInl stp)
  progress (TAInr wt) (AEXInr ex)
    with progress wt ex
  ... | Inl fin = Inl (final-inr fin)
  ... | Inr (_ , stp) = Inr (_ , ITInr stp)
  progress (TAMatchZPre wt
                        (CTOneRule (CTRule pt
                                           Γ##Γp
                                           wt')))
           (AEXMatch exe er
                     (EXRules rst (PotEntails CTTruth ct ent))
                     exrsb)
    with progress wt exe
  ... | Inr (_ , stp) = Inr (_ , (ITExpMatch stp))
  ... | Inl fin
    with matching-exhaust fin wt pt
  ... | Match (_ , mat) =
    Inr (_ , ITSuccMatch fin mat)
  ... | MayMatch mmat =
    Inl (FIndet (IMatch fin mmat))
  ... | NotMatch nmat
    with ent {!!} {!!} {!!}
  ... | qq = {!!}
  progress (TAMatchZPre wt
                        (CTRules (CTRule pt
                                         Γ##Γp
                                         wt')
                                 rst))
           (AEXMatch ex er exrs exrsb) =
    {!!}
  progress (TAMatchNZPre wt fin pret postt ¬red)
           (AEXMatch ex er exrs exrsb)
    with progress wt ex
  ... | Inr (_ , stp) = Inr (_ , (ITExpMatch stp))
  ... | Inl fin =
    {!!}
  progress (TAPair wt1 wt2) (AEXPair ex1 ex2)
    with progress wt1 ex1
  ... | Inr (_ , stp1) = Inr (_ , ITPairL stp1)
  ... | Inl fin1
    with progress wt2 ex2
  ... | Inr (_ , stp2) = Inr (_ , ITPairR fin1 stp2)
  ... | Inl fin2 = Inl (final-pair fin1 fin2)
  progress (TAFst wt) (AEXFst ex)
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
  progress (TASnd wt) (AEXSnd ex)
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
  progress (TAEHole u∈Δ) AEXEHole = Inl (FIndet IEHole)
  progress (TANEHole u∈Δ wt) (AEXNEHole ex)
    with progress wt ex
  ... | Inl fin = Inl (FIndet (INEHole fin))
  ... | Inr (_ , stp) = Inr (_ , ITNEHole stp)
