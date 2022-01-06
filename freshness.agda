open import Nat
open import Prelude
open import core

module freshness where
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
              unbound-in x e →
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
                unbound-in-r x r →
                unbound-in-rs x rs-post →
                unbound-in-zrs x (rs-pre / r / rs-post)
                
    data unbound-in : Nat → ihexp → Set where
      UBNum    : ∀{x n} →
                 unbound-in x (N n)
      UBVar    : ∀{x y} →
                 unbound-in x (X y)
      UBLam    : ∀{x y τ e} →
                 x ≠ y →
                 unbound-in x e →
                 unbound-in x (·λ y ·[ τ ] e)
      UBAp     : ∀{x e1 e2} →
                 unbound-in x e1 →
                 unbound-in x e2 →
                 unbound-in x (e1 ∘ e2)
      UNInl    : ∀{x e τ} →
                 unbound-in x e →
                 unbound-in x (inl τ e)
      UBInr    : ∀{x e τ} →
                 unbound-in x e →
                 unbound-in x (inr τ e)
      UBMatch  : ∀{x e rs} →
                 unbound-in x e →
                 unbound-in-zrs x rs →
                 unbound-in x (match e rs)
      UBPair   : ∀{x e1 e2} →
                 unbound-in x e1 →
                 unbound-in x e2 →
                 unbound-in x ⟨ e1 , e2 ⟩
      UBFst    : ∀{x e} →
                 unbound-in x e →
                 unbound-in x (fst e)
      UBSnd    : ∀{x e} →
                 unbound-in x e →
                 unbound-in x (snd e)
      UBEHole  : ∀{x u} →
                 unbound-in x (⦇-⦈[ u  ])
      UBNEHole : ∀{x e u} →
                 unbound-in x e →
                 unbound-in x (⦇⌜ e ⌟⦈[ u ])

     
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
                fresh-r x r →
                fresh-rs x rs-post →
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
                 hole-fresh-r u r →
                 hole-fresh-rs u rs-post →
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

  -- e1 and e2 do not share any binders
  mutual
    data binders-disjoint-p : pattrn → ihexp → Set where
      BDPNum    : ∀{n e} →
                  binders-disjoint-p (N n) e
      BDPVar    : ∀{x e} →
                  unbound-in x e →
                  binders-disjoint-p (X x) e
      BDPInl    : ∀{p e} →
                  binders-disjoint-p p e →
                  binders-disjoint-p (inl p) e
      BDPInr    : ∀{p e} →
                  binders-disjoint-p p e →
                  binders-disjoint-p (inr p) e
      BDPPair   : ∀{p1 p2 e} →
                  binders-disjoint-p p1 e →
                  binders-disjoint-p p2 e →
                  binders-disjoint-p ⟨ p1 , p2 ⟩ e
      BDPWild   : ∀{e} →
                  binders-disjoint-p wild e
      BDPEHole  : ∀{u e} →
                  binders-disjoint-p ⦇-⦈[ u ] e
      BDPNEHole : ∀{p w τ e} →
                  binders-disjoint-p p e →
                  binders-disjoint-p ⦇⌜ p ⌟⦈[ w , τ ] e
      
    data binders-disjoint-r : rule → ihexp → Set where
      BDRule : ∀{p e1 e2} →
               binders-disjoint-p p e2 →
               binders-disjoint e1 e2 →
               binders-disjoint-r (p => e1) e2
               
    data binders-disjoint-rs : rules → ihexp → Set where
      BDNoRules : ∀{e} →
                  binders-disjoint-rs nil e
      BDRules   : ∀{r rs e} →
                  binders-disjoint-r r e →
                  binders-disjoint-rs rs e →
                  binders-disjoint-rs (r / rs) e
                  
    data binders-disjoint-zrs : zrules → ihexp → Set where
      BDZRules : ∀{rs-pre r rs-post e} →
                 binders-disjoint-rs rs-pre e →
                 binders-disjoint-r r e →
                 binders-disjoint-rs rs-post e →
                 binders-disjoint-zrs (rs-pre / r / rs-post) e
      
    data binders-disjoint : ihexp → ihexp → Set where
      BDNum    : ∀{n e} →
                 binders-disjoint (N n) e
      BDVar    : ∀{x e} →
                 binders-disjoint (X x) e
      BDLam    : ∀{x τ e1 e2} →
                 binders-disjoint e1 e2 →
                 unbound-in x e2 →
                 binders-disjoint (·λ x ·[ τ ] e1) e2
      BDAp     : ∀{e1 e2 e3} →
                 binders-disjoint e1 e3 →
                 binders-disjoint e2 e3 →
                 binders-disjoint (e1 ∘ e2) e3
      BDInl    : ∀{e1 e2 τ} →
                 binders-disjoint e1 e2 →
                 binders-disjoint (inl τ e1) e2
      BDInr    : ∀{e1 e2 τ} →
                 binders-disjoint e1 e2 →
                 binders-disjoint (inr τ e1) e2
      BDMatch  : ∀{e1 rs e2} →
                 binders-disjoint e1 e2 →
                 binders-disjoint-zrs rs e2 →
                 binders-disjoint (match e1 rs) e2
      BDPair   : ∀{e1 e2 e3} →
                 binders-disjoint e1 e3 →
                 binders-disjoint e2 e3 →
                 binders-disjoint ⟨ e1 , e2 ⟩ e3
      BDFst    : ∀{e1 e2} →
                 binders-disjoint e1 e2 →
                 binders-disjoint (fst e1) e2
      BDSnd    : ∀{e1 e2} →
                 binders-disjoint e1 e2 →
                 binders-disjoint (snd e1) e2
      BDEHole  : ∀{u e} →
                 binders-disjoint ⦇-⦈[ u ] e
      BDNEHole : ∀{u e1 e2} →
                 binders-disjoint e1 e2 →
                 binders-disjoint ⦇⌜ e1 ⌟⦈[ u ] e2

  -- a bit hacky, but easier than recreating all previous
  -- judgements with rules rather than an expression
  data p-binders-disjoint-p : pattrn → pattrn → Set where
    PBDPattern : ∀{p1 p2} →
                 binders-disjoint-p p1
                   (match (N 0) (nil / (p2 => (N 0)) / nil)) →
                 p-binders-disjoint-p p1 p2
  
  data rs-binders-disjoint-r : rule → rules → Set where
    RSBDRule : ∀{r rs} →
               binders-disjoint-r r
                 (match (N 0) (rs / ((N 0) => (N 0)) / nil)) →
               rs-binders-disjoint-r r rs

  data rs-binders-disjoint-rs : rules → rules → Set where
    RSBDRules : ∀{rs1 rs2} →
                binders-disjoint-rs rs1
                 (match (N 0) (rs2 / ((N 0) => (N 0)) / nil)) →
               rs-binders-disjoint-rs rs1 rs2
                  
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
                  p-binders-disjoint-p p1 p2 →
                  binders-unique-p ⟨ p1 , p2 ⟩
      BUPWild   : binders-unique-p wild
      BUPEHole  : ∀{u} →
                  binders-unique-p ⦇-⦈[ u ]
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
                  rs-binders-disjoint-r r rs →
                  binders-unique-rs (r / rs)

    data binders-unique-zrs : zrules → Set where
      BUZRules : ∀{rs-pre r rs-post} →
                 binders-unique-rs rs-pre →
                 binders-unique-r r →
                 binders-unique-rs rs-post →
                 rs-binders-disjoint-r r rs-pre →
                 rs-binders-disjoint-r r rs-post →
                 rs-binders-disjoint-rs rs-pre rs-post →
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

