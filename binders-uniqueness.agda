open import Prelude
open import Nat
open import binders-disjointness
open import core
open import freshness
open import patterns-core
open import substitution-env

module binders-uniqueness where
  mutual
    data binders-unique-p : pattrn → Set where
      BUPNum    : ∀{n} →
                  binders-unique-p (N n)
      BUPVar    : ∀{x} →
                  binders-unique-p (X x)
      BUPInl    : ∀{p} →
                  binders-unique-p p →
                  binders-unique-p (inl p)
      BUPInr    : ∀{p} →
                  binders-unique-p p →
                  binders-unique-p (inr p)
      BUPPair   : ∀{p1 p2} →
                  binders-unique-p p1 →
                  binders-unique-p p2 →
                  binders-disjoint-p p1 p2 →
                  binders-unique-p ⟨ p1 , p2 ⟩
      BUPWild   : binders-unique-p wild
      BUPEHole  : ∀{w} →
                  binders-unique-p ⦇-⦈[ w ]
      BUPNEHole : ∀{p w τ} →
                  binders-unique-p p →
                  binders-unique-p ⦇⌜ p ⌟⦈[ w , τ ]

    data binders-unique-r : rule → Set where
      BURule : ∀{p e} →
               binders-unique-p p →
               binders-unique e →
               binders-disjoint-p p e →
               binders-unique-r (p => e)

    data binders-unique-rs : rules → Set where
      BUNoRules : binders-unique-rs nil
      BURules   : ∀{r rs} →
                  binders-unique-r r →
                  binders-unique-rs rs →
                  binders-disjoint-r r rs →
                  binders-unique-rs (r / rs)

    data binders-unique-zrs : zrules → Set where
      BUZRules : ∀{rs-pre r rs-post} →
                 binders-unique-rs rs-pre →
                 binders-unique-rs (r / rs-post) →
                 binders-disjoint-rs rs-pre (r / rs-post) →
                 binders-unique-zrs (rs-pre / r / rs-post)
                 
    data binders-unique : ihexp → Set where
      BUNum    : ∀{n} →
                 binders-unique (N n)
      BUVar    : ∀{x} →
                 binders-unique (X x)
      BULam    : ∀{x τ e} →
                 binders-unique e →
                 unbound-in x e →
                 binders-unique (·λ x ·[ τ ] e)
      BUEHole  : ∀{u} →
                 binders-unique ⦇-⦈[ u ]
      BUNEHole : ∀{u e} →
                 binders-unique e →
                 binders-unique ⦇⌜ e ⌟⦈[ u ]
      BUAp     : ∀{e1 e2} →
                 binders-unique e1 →
                 binders-unique e2 →
                 binders-disjoint e1 e2 →
                 binders-unique (e1 ∘ e2)
      BUInl    : ∀{e τ} →
                 binders-unique e →
                 binders-unique (inl τ e)
      BUInr    : ∀{e τ} →
                 binders-unique e →
                 binders-unique (inr τ e)
      BUMatch  : ∀{e rs} →
                 binders-unique e →
                 binders-unique-zrs rs →
                 binders-disjoint-zrs rs e →
                 binders-unique (match e rs)
      BUPair   : ∀{e1 e2} →
                 binders-unique e1 →
                 binders-unique e2 →
                 binders-disjoint e1 e2 →
                 binders-unique ⟨ e1 , e2 ⟩
      BUFst    : ∀{e} →
                 binders-unique e →
                 binders-unique (fst e)
      BUSnd    : ∀{e} →
                 binders-unique e →
                 binders-unique (snd e)

  data binders-unique-env : env → Set where
    BUId    : ∀{Γ} →
              binders-unique-env (Id Γ)
    BUSubst : ∀{d y θ} →
              binders-unique d →
              binders-unique-env θ →
              binders-disjoint-env θ d →
              binders-unique-env (Subst d y θ)
              
  mutual
    data hole-binders-unique-p : pattrn → Set where
      HBUPNum    : ∀{n} →
                   hole-binders-unique-p (N n)
      HBUPVar    : ∀{x} →
                   hole-binders-unique-p (X x)
      HBUPInl    : ∀{p} →
                   hole-binders-unique-p p →
                   hole-binders-unique-p (inl p)
      HBUPInr    : ∀{p} →
                   hole-binders-unique-p p →
                   hole-binders-unique-p (inr p)
      HBUPPair   : ∀{p1 p2} →
                   hole-binders-unique-p p1 →
                   hole-binders-unique-p p2 →
                   hole-binders-disjoint-p p1 p2 →
                   hole-binders-unique-p ⟨ p1 , p2 ⟩
      HBUPWild   : hole-binders-unique-p wild
      HBUPEHole  : ∀{w} →
                   hole-binders-unique-p ⦇-⦈[ w ]
      HBUPNEHole : ∀{p w τ} →
                   hole-binders-unique-p p →
                   hole-unbound-in-p w p →
                   hole-binders-unique-p ⦇⌜ p ⌟⦈[ w , τ ]

    data hole-binders-unique-r : rule → Set where
      HBURule : ∀{p e} →
                hole-binders-unique-p p →
                hole-binders-unique e →
                hole-binders-disjoint-p p e →
                hole-binders-unique-r (p => e)

    data hole-binders-unique-rs : rules → Set where
      HBUNoRules : hole-binders-unique-rs nil
      HBURules   : ∀{r rs} →
                   hole-binders-unique-r r →
                   hole-binders-unique-rs rs →
                   hole-binders-disjoint-r r rs →
                   hole-binders-unique-rs (r / rs)

    data hole-binders-unique-zrs : zrules → Set where
      HBUZRules : ∀{rs-pre r rs-post} →
                  hole-binders-unique-rs rs-pre →
                  hole-binders-unique-rs (r / rs-post) →
                  hole-binders-disjoint-rs rs-pre (r / rs-post) →
                  hole-binders-unique-zrs (rs-pre / r / rs-post)
                 
    data hole-binders-unique : ihexp → Set where
      HBUNum    : ∀{n} →
                  hole-binders-unique (N n)
      HBUVar    : ∀{x} →
                  hole-binders-unique (X x)
      HBULam    : ∀{x τ e} →
                  hole-binders-unique e →
                  hole-binders-unique (·λ x ·[ τ ] e)
      HBUEHole  : ∀{u} →
                  hole-binders-unique ⦇-⦈[ u ]
      HBUNEHole : ∀{u e} →
                  hole-binders-unique e →
                  hole-binders-unique ⦇⌜ e ⌟⦈[ u ]
      HBUAp     : ∀{e1 e2} →
                  hole-binders-unique e1 →
                  hole-binders-unique e2 →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-unique (e1 ∘ e2)
      HBUInl    : ∀{e τ} →
                  hole-binders-unique e →
                  hole-binders-unique (inl τ e)
      HBUInr    : ∀{e τ} →
                  hole-binders-unique e →
                  hole-binders-unique (inr τ e)
      HBUMatch  : ∀{e rs} →
                  hole-binders-unique e →
                  hole-binders-unique-zrs rs →
                  hole-binders-disjoint-zrs rs e →
                  hole-binders-unique (match e rs)
      HBUPair   : ∀{e1 e2} →
                  hole-binders-unique e1 →
                  hole-binders-unique e2 →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-unique ⟨ e1 , e2 ⟩
      HBUFst    : ∀{e} →
                  hole-binders-unique e →
                  hole-binders-unique (fst e)
      HBUSnd    : ∀{e} →
                  hole-binders-unique e →
                  hole-binders-unique (snd e)

  data hole-binders-unique-env : env → Set where
    HBUId    : ∀{Γ} →
               hole-binders-unique-env (Id Γ)
    HBUSubst : ∀{d y θ} →
               hole-binders-unique d →
               hole-binders-unique-env θ →
               hole-binders-disjoint-env θ d →
               hole-binders-unique-env (Subst d y θ)
