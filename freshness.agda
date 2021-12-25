open import Nat
open import Prelude
open import core

module freshness where
  -- the variable name x is not bound in p 
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
    UBPNEHole : ∀{x p u τ} →
                unbound-in-p x p →
                unbound-in-p x ⦇⌜ p ⌟⦈[ u , τ ]

  unbound-in-p-dec : (x : Nat) →
                     (p : pattrn) →
                     (unbound-in-p x p) + (unbound-in-p x p → ⊥)
  unbound-in-p-dec x (N n) = Inl UBPNum
  unbound-in-p-dec x (X y)
    with natEQ x y
  ... | Inl refl = Inr (λ{(UBPVar x≠x) → x≠x refl})
  ... | Inr x≠y = Inl (UBPVar x≠y)
  unbound-in-p-dec x (inl p)
    with unbound-in-p-dec x p
  ... | Inl ubp = Inl (UBPInl ubp)
  ... | Inr ¬ubp = Inr (λ{(UBPInl ubp) → ¬ubp ubp})
  unbound-in-p-dec x (inr p)
    with unbound-in-p-dec x p
  ... | Inl ubp = Inl (UBPInr ubp)
  ... | Inr ¬ubp = Inr (λ{(UBPInr ubp) → ¬ubp ubp})
  unbound-in-p-dec x ⟨ p1 , p2 ⟩
    with unbound-in-p-dec x p1
  ... | Inr ¬ubp1 = Inr λ{(UBPPair ubp1 ubp2) → ¬ubp1 ubp1}
  ... | Inl ubp1
    with unbound-in-p-dec x p2
  ... | Inr ¬ubp2 = Inr λ{(UBPPair ubp1 ubp2) → ¬ubp2 ubp2}
  ... | Inl ubp2 = Inl (UBPPair ubp1 ubp2)
  unbound-in-p-dec x wild = Inl UBPWild
  unbound-in-p-dec x ⦇-⦈[ w ] = Inl UBPEHole
  unbound-in-p-dec x ⦇⌜ p ⌟⦈[ w , τ ]
    with unbound-in-p-dec x p
  ... | Inl ubp = Inl (UBPNEHole ubp)
  ... | Inr ¬ubp = Inr (λ{(UBPNEHole ubp) → ¬ubp ubp})
  
  -- the variable name x is fresh in the term e
  mutual
    data fresh-r : Nat → rule → Set where
      FRule : ∀{x p e} →
              unbound-in-p x p →
              fresh x e →
              fresh-r x (p => e)

    data fresh-hrs : Nat → hrules → Set where
      FNoRules : ∀{x} →
                 fresh-hrs x nil
      FRules   : ∀{x r rs} →
                 fresh-r x r →
                 fresh-hrs x rs →
                 fresh-hrs x (r / rs)

    data fresh-zrs : Nat → zrules → Set where
      FZRules : ∀{x rs-pre r rs-post} →
                fresh-hrs x rs-pre →
                fresh-r x r →
                fresh-hrs x rs-post →
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
      FHole   : ∀{x u} →
                fresh x (⦇-⦈[ u  ])
      FNEHole : ∀{x e u} →
                fresh x e →
                fresh x (⦇⌜ e ⌟⦈[ u ])

  -- the hole name u is not bound in p
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
  mutual
    -- the hole name u is fresh in e
    data hole-fresh-r : Nat → rule → Set where
      HFRule : ∀{u p e} →
               hole-unbound-in-p u p →
               hole-fresh u e →
               hole-fresh-r u (p => e)

    data hole-fresh-hrs : Nat → hrules → Set where
      HFNoRules : ∀{u} →
                  hole-fresh-hrs u nil
      HFRules   : ∀{u r rs} →
                  hole-fresh-r u r →
                  hole-fresh-hrs u rs →
                  hole-fresh-hrs u (r / rs)

    data hole-fresh-zrs : Nat → zrules → Set where
      HFZRules : ∀{u rs-pre r rs-post} →
                 hole-fresh-hrs u rs-pre →
                 hole-fresh-r u r →
                 hole-fresh-hrs u rs-post →
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
      HFHole   : ∀{u u'} →
                 u ≠ u' →
                 hole-fresh u (⦇-⦈[ u' ])
      HFNEHole : ∀{u e u'} →
                 u ≠ u' →
                 hole-fresh u e →
                 hole-fresh u (⦇⌜ e ⌟⦈[ u' ])
