open import Prelude
open import core
open import patterns-core
open import value-result-judgements

module dynamic-result-judgements where
  open value-result-judgements public
  mutual
    -- e is indeterminate
    data _indet : (e : ihexp) → Set where
      IAp     : ∀{e1 e2} →
                e1 indet →
                e2 final →
                (e1 ∘ e2) indet
      IInl    : ∀{e τ} →
                e indet →
                (inl τ e) indet
      IInr    : ∀{e τ} →
                e indet →
                (inr τ e) indet
      IMatch  : ∀{e rs-pre pr er rs-post} →
                e final →
                e ?▹ pr →
                (match e (rs-pre / (pr => er) / rs-post)) indet
      IPairL  : ∀{e1 e2} →
                e1 indet →
                e2 val →
                ⟨ e1 , e2 ⟩ indet
      IPairR  : ∀{e1 e2} →
                e1 val →
                e2 indet →
                ⟨ e1 , e2 ⟩ indet
      IPair   : ∀{e1 e2} →
                e1 indet →
                e2 indet →
                ⟨ e1 , e2 ⟩ indet
      IFst    : ∀{e} →
                e indet →
                (fst e) indet
      ISnd    : ∀{e} →
                e indet →
                (snd e) indet
      IEHole  : ∀{u} →
                ⦇-⦈[ u ] indet
      INEHole : ∀{e u} →
                e final →
                ⦇⌜ e ⌟⦈[ u ] indet
                
    -- e is final
    data _final : (e : ihexp) → Set where
      FVal   : ∀{e} →
               e val →
               e final
      FIndet : ∀{e} →
               e indet →
               e final

    inl-final : ∀{e τ} → (inl τ e) final → e final
    inl-final (FVal (VInl eval)) = FVal eval
    inl-final (FIndet (IInl eind)) = FIndet eind

    inr-final : ∀{e τ} → (inr τ e) final → e final
    inr-final (FVal (VInr eval)) = FVal eval
    inr-final (FIndet (IInr eind)) = FIndet eind

    pair-final : ∀{e1 e2} → ⟨ e1 , e2 ⟩ final → e1 final × e2 final
    pair-final (FVal (VPair val1 val2)) = FVal val1 , FVal val2
    pair-final (FIndet (IPairL ind1 val2)) = FIndet ind1 , FVal val2
    pair-final (FIndet (IPairR val1 ind2)) = FVal val1 , FIndet ind2
    pair-final (FIndet (IPair ind1 ind2)) = FIndet ind1 , FIndet ind2
    
    final-notintro-indet : ∀{e} →
                           e final →
                           e notintro →
                           e indet
    final-notintro-indet (FVal ()) NVAp
    final-notintro-indet (FVal ()) NVMatch
    final-notintro-indet (FVal ()) NVFst
    final-notintro-indet (FVal ()) NVSnd
    final-notintro-indet (FVal ()) NVEHole
    final-notintro-indet (FVal ()) NVNEHole
    final-notintro-indet (FIndet ind) ni = ind
