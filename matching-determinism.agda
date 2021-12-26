open import Nat
open import Prelude
open import contexts
open import core
open import patterns-core
open import result-judgements
open import statics-core
open import substitution-env

module matching-determinism where
  -- result of the matching determinism theorem
  data DetMatch (e : ihexp) (p : pattrn) : Set where
       Match    : (Σ[ θ ∈ env ] e ▹ p ⊣ θ) →
                  (e ?▹ p → ⊥) →
                  (e ⊥▹ p → ⊥) →
                  DetMatch e p
       MayMatch : ((Σ[ θ ∈ env ] e ▹ p ⊣ θ) → ⊥) →
                  (e ?▹ p) →
                  (e ⊥▹ p → ⊥) →
                  DetMatch e p
       NotMatch : ((Σ[ θ ∈ env ] e ▹ p ⊣ θ) → ⊥) →
                  (e ?▹ p → ⊥) →
                  (e ⊥▹ p) →
                  DetMatch e p
       
  matching-det : ∀{e Δe τ p ξ Γ Δ} →
                 e final →
                 ∅ , Δe ⊢ e :: τ →
                 p :: τ [ ξ ]⊣ Γ , Δ →
                 DetMatch e p
  matching-det {e = e} {p = p} fin wt (PTVar {x = x}) =
    Match mat ¬mmat ¬nmat
    where
      mat : Σ[ θ ∈ env ] e ▹ p ⊣ θ
      mat = Subst e x (Id (λ _ → None)) , MVar
      ¬mmat : e ?▹ p → ⊥
      ¬mmat (MMNotIntro ni ())
      ¬nmat : e ⊥▹ p → ⊥
      ¬nmat ()
  matching-det fin wt PTNum = {!!}
  matching-det fin wt (PTInl pt) = {!!}
  matching-det fin wt (PTInr pt) = {!!}
  matching-det fin wt (PTPair disj disjh pt1 pt2) = {!!}
  matching-det fin wt PTEHole = {!!}
  matching-det fin wt (PTNEHole pt apt) = {!!}
  matching-det fin wt PTWild = {!!}
