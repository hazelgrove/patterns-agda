open import Bool
open import Prelude
open import core
open import value-judgements

module notintro-decidable where
  notintro-bool : ihexp → Bool
  notintro-bool (e1 ∘ e2) = true
  notintro-bool (fst e) = true
  notintro-bool (snd e) = true
  notintro-bool (match e rs) = true
  notintro-bool ⦇-⦈[ u ] = true
  notintro-bool ⦇⌜ e ⌟⦈[ u ] = true
  notintro-bool (N n) = false
  notintro-bool (X x) = false
  notintro-bool (·λ x ·[ u ] e) = false
  notintro-bool (inl τ e) = false
  notintro-bool (inr τ e) = false
  notintro-bool ⟨ e1 , e2 ⟩ = false

  notintro-sound : ∀{e} →
                   e notintro →
                   notintro-bool e == true
  notintro-sound NVAp = refl
  notintro-sound NVMatch = refl
  notintro-sound NVFst = refl
  notintro-sound NVSnd = refl
  notintro-sound NVEHole = refl
  notintro-sound NVNEHole = refl
  
  notintro-complete : ∀{e} →
                      notintro-bool e == true →
                      e notintro
  notintro-complete {e = e1 ∘ e2} nieq = NVAp
  notintro-complete {e = match e rs} nieq = NVMatch
  notintro-complete {e = fst e} nieq = NVFst
  notintro-complete {e = snd e} nieq = NVSnd
  notintro-complete {e = ⦇-⦈[ u ]} nieq = NVEHole
  notintro-complete {e = ⦇⌜ e ⌟⦈[ u ]} nieq = NVNEHole
  
  notintro-dec : (e : ihexp) →
                 (e notintro) + (e notintro → ⊥)
  notintro-dec e with notintro-bool e in eq
  ... | false = Inr (λ ni → false-neq-true eq (notintro-sound ni))
  ... | true = Inl (notintro-complete eq)

 
