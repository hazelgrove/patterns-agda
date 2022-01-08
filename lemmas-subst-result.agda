open import Nat
open import Prelude
open import core
open import dynamics-core
open import freshness
open import freshness-decidable
open import lemmas-subst-matching
open import lemmas-subst-value
open import patterns-core
open import result-judgements

module lemmas-subst-result where
  mutual
    indet-subst-final : ∀{x e1 e2} →
                        e1 indet →
                        e2 final →
                        ([ e2 / x ] e1) indet
    indet-subst-final (IAp ind1₁ fin1₂) fin2 =
      IAp (indet-subst-final ind1₁ fin2)
          (final-subst-final fin1₂ fin2)
    indet-subst-final (IInl ind1) fin2 =
      IInl (indet-subst-final ind1 fin2)
    indet-subst-final (IInr ind1) fin2 =
      IInr (indet-subst-final ind1 fin2)
    indet-subst-final {x = x}
                      (IMatch {pr = pr} fin1 mmat)
                      fin2
      with unbound-in-p-dec x pr
    ... | Inl ub =
      IMatch (final-subst-final fin1 fin2)
             (subst-maymat mmat)
    ... | Inr ¬ub =
      IMatch (final-subst-final fin1 fin2)
             (subst-maymat mmat)
    indet-subst-final (IPairL ind1₁ val1₂) fin2
      with subst-val val1₂
    ... | sval1₂ =
      IPairL (indet-subst-final ind1₁ fin2) sval1₂
    indet-subst-final (IPairR val1₁ ind1₂) fin2
      with subst-val val1₁
    ... | sval1₁ =
      IPairR sval1₁ (indet-subst-final ind1₂ fin2)
    indet-subst-final (IPair ind1₁ ind1₂) fin2 =
      IPair (indet-subst-final ind1₁ fin2)
            (indet-subst-final ind1₂ fin2)
    indet-subst-final (IFst ind1) fin2 =
      IFst (indet-subst-final ind1 fin2)
    indet-subst-final (ISnd ind1) fin2 =
      ISnd (indet-subst-final ind1 fin2)
    indet-subst-final IEHole fin2 = IEHole
    indet-subst-final (INEHole fin1) fin2 =
      INEHole (final-subst-final fin1 fin2)
    
    
    final-subst-final : ∀{x e1 e2} →
                        e1 final →
                        e2 final →
                        ([ e2 / x ] e1) final
    final-subst-final (FVal val1) fin2 =
      FVal (subst-val val1)
    final-subst-final (FIndet ind1) fin2 =
      FIndet (indet-subst-final ind1 fin2)
                 
