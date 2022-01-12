open import Nat
open import Prelude
open import contexts
open import core

module freshness where
  -- types T where we can determine if a Nat is unbound in T.
  -- we use this as a type-class so that the disjointness
  -- judgements can be generic
  record UnboundIn {a : Level} (T : Set a) : Set (lsuc a) where
    field
      unbound-in : Nat → T → Set
      
  open UnboundIn {{...}} public
  
  -- the variable name x is not bound in e
  mutual
    data unbound-in-p : Nat → pattrn → Set where
      UBPNum    : ∀{x n} →
                  unbound-in-p x (N n)
      UBPVar    : ∀{x y} →
                  x ≠ y →
                  unbound-in-p x (X y)
      UBPInl    : ∀{x p} →
                  unbound-in-p x p →
                  unbound-in-p x (inl p)
      UBPInr    : ∀{x p} →
                  unbound-in-p x p →
                  unbound-in-p x (inr p)
      UBPPair   : ∀{x p1 p2} →
                  unbound-in-p x p1 →
                  unbound-in-p x p2 →
                  unbound-in-p x ⟨ p1 , p2 ⟩
      UBPWild   : ∀{x} →
                  unbound-in-p x wild
      UBPEHole  : ∀{x u} →
                  unbound-in-p x ⦇-⦈[ u ]
      UBPNEHole : ∀{x p w τ} →
                  unbound-in-p x p →
                  unbound-in-p x ⦇⌜ p ⌟⦈[ w , τ ]

    data unbound-in-r : Nat → rule → Set where
      UBRule : ∀{x p e} →
               unbound-in-p x p →
               unbound-in-e x e →
               unbound-in-r x (p => e)

    data unbound-in-rs : Nat → rules → Set where
      UBNoRules : ∀{x} →
                  unbound-in-rs x nil
      UBRules   : ∀{x r rs} →
                  unbound-in-r x r →
                  unbound-in-rs x rs →
                  unbound-in-rs x (r / rs)

    data unbound-in-zrs : Nat → zrules → Set where
      UBZRules : ∀{x rs-pre r rs-post} →
                 unbound-in-rs x rs-pre →
                 unbound-in-rs x (r / rs-post) →
                 unbound-in-zrs x (rs-pre / r / rs-post)
                
    data unbound-in-e : Nat → ihexp → Set where
      UBNum    : ∀{x n} →
                 unbound-in-e x (N n)
      UBVar    : ∀{x y} →
                 unbound-in-e x (X y)
      UBLam    : ∀{x y τ e} →
                 x ≠ y →
                 unbound-in-e x e →
                 unbound-in-e x (·λ y ·[ τ ] e)
      UBAp     : ∀{x e1 e2} →
                 unbound-in-e x e1 →
                 unbound-in-e x e2 →
                 unbound-in-e x (e1 ∘ e2)
      UBInl    : ∀{x e τ} →
                 unbound-in-e x e →
                 unbound-in-e x (inl τ e)
      UBInr    : ∀{x e τ} →
                 unbound-in-e x e →
                 unbound-in-e x (inr τ e)
      UBMatch  : ∀{x e rs} →
                 unbound-in-e x e →
                 unbound-in-zrs x rs →
                 unbound-in-e x (match e rs)
      UBPair   : ∀{x e1 e2} →
                 unbound-in-e x e1 →
                 unbound-in-e x e2 →
                 unbound-in-e x ⟨ e1 , e2 ⟩
      UBFst    : ∀{x e} →
                 unbound-in-e x e →
                 unbound-in-e x (fst e)
      UBSnd    : ∀{x e} →
                 unbound-in-e x e →
                 unbound-in-e x (snd e)
      UBEHole  : ∀{x u} →
                 unbound-in-e x (⦇-⦈[ u  ])
      UBNEHole : ∀{x e u} →
                 unbound-in-e x e →
                 unbound-in-e x (⦇⌜ e ⌟⦈[ u ])

  instance
    PattrnUB : UnboundIn pattrn
    PattrnUB = record { unbound-in = unbound-in-p }

  instance
    RuleUB : UnboundIn rule
    RuleUB = record { unbound-in = unbound-in-r }

  instance
    RulesUB : UnboundIn rules
    RulesUB = record { unbound-in = unbound-in-rs }

  instance
    ZRulesUB : UnboundIn zrules
    ZRulesUB = record { unbound-in = unbound-in-zrs }

  instance
    IHExpUB : UnboundIn ihexp
    IHExpUB = record { unbound-in = unbound-in-e }
    
  -- the variable name x is fresh in the term e
  mutual
    data fresh-r : Nat → rule → Set where
      FRule : ∀{x p e} →
              unbound-in-p x p →
              fresh x e →
              fresh-r x (p => e)

    data fresh-rs : Nat → rules → Set where
      FNoRules : ∀{x} →
                 fresh-rs x nil
      FRules   : ∀{x r rs} →
                 fresh-r x r →
                 fresh-rs x rs →
                 fresh-rs x (r / rs)

    data fresh-zrs : Nat → zrules → Set where
      FZRules : ∀{x rs-pre r rs-post} →
                fresh-rs x rs-pre →
                fresh-rs x (r / rs-post) →
                fresh-zrs x (rs-pre / r / rs-post)
                
    data fresh : Nat → ihexp → Set where
      FNum    : ∀{x n} →
                fresh x (N n)
      FVar    : ∀{x y} →
                x ≠ y →
                fresh x (X y)
      FLam    : ∀{x y τ e} →
                x ≠ y →
                fresh x e →
                fresh x (·λ y ·[ τ ] e)
      FAp     : ∀{x e1 e2} →
                fresh x e1 →
                fresh x e2 →
                fresh x (e1 ∘ e2)
      FInl    : ∀{x e τ} →
                fresh x e →
                fresh x (inl τ e)
      FInr    : ∀{x e τ} →
                fresh x e →
                fresh x (inr τ e)
      FMatch  : ∀{x e rs} →
                fresh x e →
                fresh-zrs x rs →
                fresh x (match e rs)
      FPair   : ∀{x e1 e2} →
                fresh x e1 →
                fresh x e2 →
                fresh x ⟨ e1 , e2 ⟩
      FFst    : ∀{x e} →
                fresh x e →
                fresh x (fst e)
      FSnd    : ∀{x e} →
                fresh x e →
                fresh x (snd e)
      FEHole   : ∀{x u} →
                fresh x (⦇-⦈[ u  ])
      FNEHole : ∀{x e u} →
                fresh x e →
                fresh x (⦇⌜ e ⌟⦈[ u ])

  -- types T where we can determine if a Nat is unbound in T.
  -- we use this as a type-class so that the disjointness
  -- judgements can be generic
  record HoleUnboundIn {a : Level} (T : Set a) : Set (lsuc a) where
    field
      hole-unbound-in : Nat → T → Set
      
  open HoleUnboundIn {{...}} public
  
  mutual
    -- the hole name u is not bound in e
    data hole-unbound-in-p : Nat → pattrn → Set where
      HUBPNum    : ∀{u n} →
                   hole-unbound-in-p u (N n)
      HUBPVar    : ∀{u x} →
                   hole-unbound-in-p u (X x)
      HUBPInl    : ∀{u p} →
                   hole-unbound-in-p u p →
                   hole-unbound-in-p u (inl p)
      HUBPInr    : ∀{u p} →
                   hole-unbound-in-p u p →
                   hole-unbound-in-p u (inr p)
      HUBPPair   : ∀{u p1 p2} →
                   hole-unbound-in-p u p1 →
                   hole-unbound-in-p u p2 →
                   hole-unbound-in-p u ⟨ p1 , p2 ⟩
      HUBPWild   : ∀{u} →
                   hole-unbound-in-p u wild
      HUBPEHole  : ∀{u u'} →
                   u ≠ u' →
                   hole-unbound-in-p u ⦇-⦈[ u' ]
      HUBPNEHole : ∀{u p u' τ} →
                   u ≠ u' →
                   hole-unbound-in-p u p →
                   hole-unbound-in-p u ⦇⌜ p ⌟⦈[ u' , τ ]
    
    data hole-unbound-in-r : Nat → rule → Set where
      HUBRule : ∀{u p e} →
                hole-unbound-in-p u p →
                hole-unbound-in-e u e →
                hole-unbound-in-r u (p => e)

    data hole-unbound-in-rs : Nat → rules → Set where
      HUBNoRules : ∀{u} →
                   hole-unbound-in-rs u nil
      HUBRules   : ∀{u r rs} →
                   hole-unbound-in-r u r →
                   hole-unbound-in-rs u rs →
                   hole-unbound-in-rs u (r / rs)

    data hole-unbound-in-zrs : Nat → zrules → Set where
      HUBZRules : ∀{u rs-pre r rs-post} →
                  hole-unbound-in-rs u rs-pre →
                  hole-unbound-in-rs u (r / rs-post) →
                  hole-unbound-in-zrs u (rs-pre / r / rs-post)
                
    data hole-unbound-in-e : Nat → ihexp → Set where
      HUBNum    : ∀{u n} →
                  hole-unbound-in-e u (N n)
      HUBVar    : ∀{u x} →
                  hole-unbound-in-e u (X x)
      HUBLam    : ∀{u x τ e} →
                  hole-unbound-in-e u e →
                  hole-unbound-in-e u (·λ x ·[ τ ] e)
      HUBAp     : ∀{u e1 e2} →
                  hole-unbound-in-e u e1 →
                  hole-unbound-in-e u e2 →
                  hole-unbound-in-e u (e1 ∘ e2)
      HUBInl    : ∀{u e τ} →
                  hole-unbound-in-e u e →
                  hole-unbound-in-e u (inl τ e)
      HUBInr    : ∀{u e τ} →
                  hole-unbound-in-e u e →
                  hole-unbound-in-e u (inr τ e)
      HUBMatch  : ∀{u e rs} →
                  hole-unbound-in-e u e →
                  hole-unbound-in-zrs u rs →
                  hole-unbound-in-e u (match e rs)
      HUBPair   : ∀{u e1 e2} →
                  hole-unbound-in-e u e1 →
                  hole-unbound-in-e u e2 →
                  hole-unbound-in-e u ⟨ e1 , e2 ⟩
      HUBFst    : ∀{u e} →
                  hole-unbound-in-e u e →
                  hole-unbound-in-e u (fst e)
      HUBSnd    : ∀{u e} →
                  hole-unbound-in-e u e →
                  hole-unbound-in-e u (snd e)
      HUBEHole  : ∀{u u'} →
                  hole-unbound-in-e u (⦇-⦈[ u' ])
      HUBNEHole : ∀{u e u'} →
                  hole-unbound-in-e u e →
                  hole-unbound-in-e u (⦇⌜ e ⌟⦈[ u' ])

  instance
    PattrnHUB : HoleUnboundIn pattrn
    PattrnHUB = record { hole-unbound-in = hole-unbound-in-p }

  instance
    RuleHUB : HoleUnboundIn rule
    RuleHUB = record { hole-unbound-in = hole-unbound-in-r }

  instance
    RulesHUB : HoleUnboundIn rules
    RulesHUB = record { hole-unbound-in = hole-unbound-in-rs }

  instance
    ZRulesHUB : HoleUnboundIn zrules
    ZRulesHUB = record { hole-unbound-in = hole-unbound-in-zrs }

  instance
    IHExpHUB : HoleUnboundIn ihexp
    IHExpHUB = record { hole-unbound-in = hole-unbound-in-e }
    
  mutual
    -- the hole name u is fresh in e
    data hole-fresh-r : Nat → rule → Set where
      HFRule : ∀{u p e} →
               hole-unbound-in-p u p →
               hole-fresh u e →
               hole-fresh-r u (p => e)

    data hole-fresh-rs : Nat → rules → Set where
      HFNoRules : ∀{u} →
                  hole-fresh-rs u nil
      HFRules   : ∀{u r rs} →
                  hole-fresh-r u r →
                  hole-fresh-rs u rs →
                  hole-fresh-rs u (r / rs)

    data hole-fresh-zrs : Nat → zrules → Set where
      HFZRules : ∀{u rs-pre r rs-post} →
                 hole-fresh-rs u rs-pre →
                 hole-fresh-rs u (r / rs-post) →
                 hole-fresh-zrs u (rs-pre / r / rs-post)
                
    data hole-fresh : Nat → ihexp → Set where
      HFNum    : ∀{u n} →
                 hole-fresh u (N n)
      HFVar    : ∀{u x} →
                 hole-fresh u (X x)
      HFLam    : ∀{u x τ e} →
                 hole-fresh u e →
                 hole-fresh u (·λ x ·[ τ ] e)
      HFAp     : ∀{u e1 e2} →
                 hole-fresh u e1 →
                 hole-fresh u e2 →
                 hole-fresh u (e1 ∘ e2)
      HFInl    : ∀{u e τ} →
                 hole-fresh u e →
                 hole-fresh u (inl τ e)
      HFInr    : ∀{u e τ} →
                 hole-fresh u e →
                 hole-fresh u (inr τ e)
      HFMatch  : ∀{u e rs} →
                 hole-fresh u e →
                 hole-fresh-zrs u rs →
                 hole-fresh u (match e rs)
      HFPair   : ∀{u e1 e2} →
                 hole-fresh u e1 →
                 hole-fresh u e2 →
                 hole-fresh u ⟨ e1 , e2 ⟩
      HFFst    : ∀{u e} →
                 hole-fresh u e →
                 hole-fresh u (fst e)
      HFSnd    : ∀{u e} →
                 hole-fresh u e →
                 hole-fresh u (snd e)
      HFEHole   : ∀{u u'} →
                 u ≠ u' →
                 hole-fresh u (⦇-⦈[ u' ])
      HFNEHole : ∀{u e u'} →
                 u ≠ u' →
                 hole-fresh u e →
                 hole-fresh u (⦇⌜ e ⌟⦈[ u' ])

