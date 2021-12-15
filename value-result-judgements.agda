open import Bool
open import Prelude
open import core

module value-result-judgements where
  -- these judgements declare that an expression is a value, or can syntactically
  -- be determined to not be a value.
  -- these judgements are placed into their own module separate from the
  -- final, indet, etc. judgements in order to break some dependency cycles

  -- e is a value
  data _val : (e : ihexp) → Set where
    VNum  : ∀{n} →
            (N n) val
    VLam  : ∀{x τ e} →
            (·λ x ·[ τ ] e) val
    VInl  : ∀{e τ} →
            e val →
            (inl τ e) val
    VInr  : ∀{e τ} →
            e val →
            (inr τ e) val
    VPair : ∀{e1 e2} →
            e1 val →
            e2 val →
            ⟨ e1 , e2 ⟩ val
 
  -- e cannot be a value statically
  data _notintro : (e : ihexp) → Set where
    NVAp     : ∀{e1 e2} →
               (e1 ∘ e2) notintro
    NVMatch  : ∀{e rs} →
               (match e rs) notintro
    NVFst    : ∀{e} →
               (fst e) notintro
    NVSnd    : ∀{e} →
               (snd e) notintro
    NVEHole  : ∀{u} →
               ⦇-⦈[ u ] notintro
    NVNEHole : ∀{e u} →
               ⦇⌜ e ⌟⦈[ u ] notintro

  

  
