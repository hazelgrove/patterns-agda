open import Nat
open import Prelude
open import core
open import freshness

module binder-disjointness where
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
      BDPEHole  : ∀{w e} →
                  binders-disjoint-p ⦇-⦈[ w ] e
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
                 binders-disjoint-rs (r / rs-post) e →
                 binders-disjoint-zrs (rs-pre / r / rs-post) e
      
    data binders-disjoint : ihexp → ihexp → Set where
      BDNum    : ∀{n e} →
                 binders-disjoint (N n) e
      BDVar    : ∀{x e} →
                 binders-disjoint (X x) e
      BDLam    : ∀{x τ e1 e2} →
                 unbound-in x e2 →
                 binders-disjoint e1 e2 →
                 binders-disjoint (·λ x ·[ τ ] e1) e2
      BDAp     : ∀{e1 e2 e3} →
                 binders-disjoint e1 e3 →
                 binders-disjoint e2 e3 →
                 binders-disjoint (e1 ∘ e2) e3
      BDInl    : ∀{e1 τ e2} →
                 binders-disjoint e1 e2 →
                 binders-disjoint (inl τ e1) e2
      BDInr    : ∀{e1 τ e2} →
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

  data p-binders-disjoint-p : pattrn → pattrn → Set where
    PBDPNum    : ∀{n p} →
                 p-binders-disjoint-p (N n) p
    PBDPVar    : ∀{x p} →
                 unbound-in-p x p →
                 p-binders-disjoint-p (X x) p
    PBDPInl    : ∀{p1 p2} →
                 p-binders-disjoint-p p1 p2 →
                 p-binders-disjoint-p (inl p1) p2
    PBDPInr    : ∀{p1 p2} →
                 p-binders-disjoint-p p1 p2 →
                 p-binders-disjoint-p (inr p1) p2
    PBDPPair   : ∀{p1 p2 p3} →
                 p-binders-disjoint-p p1 p3 →
                 p-binders-disjoint-p p2 p3 →
                 p-binders-disjoint-p ⟨ p1 , p2 ⟩ p3
    PBDPWild   : ∀{p} →
                 p-binders-disjoint-p wild p
    PBDPEHole  : ∀{w p} →
                 p-binders-disjoint-p ⦇-⦈[ w ] p
    PBDPNEHole : ∀{p1 w τ p2} →
                 p-binders-disjoint-p p1 p2 →
                 p-binders-disjoint-p ⦇⌜ p1 ⌟⦈[ w , τ ] p2

  -- a bit hacky, but easier than recreating all previous
  -- judgements with rules rather than an expression
  mutual
    data rs-binders-disjoint-p : pattrn → rules → Set where
      RBDPNum    : ∀{n rs} →
                   rs-binders-disjoint-p (N n) rs
      RBDPVar    : ∀{x rs} →
                   unbound-in-rs x rs →
                   rs-binders-disjoint-p (X x) rs
      RBDPInl    : ∀{p rs} →
                   rs-binders-disjoint-p p rs →
                   rs-binders-disjoint-p (inl p) rs
      RBDPInr    : ∀{p rs} →
                   rs-binders-disjoint-p p rs →
                   rs-binders-disjoint-p (inr p) rs
      RBDPPair   : ∀{p1 p2 rs} →
                   rs-binders-disjoint-p p1 rs →
                   rs-binders-disjoint-p p2 rs →
                   rs-binders-disjoint-p ⟨ p1 , p2 ⟩ rs
      RBDPWild   : ∀{rs} →
                   rs-binders-disjoint-p wild rs
      RBDPEHole  : ∀{w rs} →
                   rs-binders-disjoint-p ⦇-⦈[ w ] rs
      RBDPNEHole : ∀{p w τ rs} →
                   rs-binders-disjoint-p p rs →
                   rs-binders-disjoint-p ⦇⌜ p ⌟⦈[ w , τ ] rs
      
    data rs-binders-disjoint-r : rule → rules → Set where
      RBDRule : ∀{p e rs} →
                rs-binders-disjoint-p p rs →
                rs-binders-disjoint e rs →
                rs-binders-disjoint-r (p => e) rs
               
    data rs-binders-disjoint-rs : rules → rules → Set where
      RBDNoRules : ∀{rs} →
                   rs-binders-disjoint-rs nil rs
      RBDRules   : ∀{r rs1 rs2} →
                   rs-binders-disjoint-r r rs2 →
                   rs-binders-disjoint-rs rs1 rs2 →
                   rs-binders-disjoint-rs (r / rs1) rs2

    data rs-binders-disjoint-zrs : zrules → rules → Set where
      RBDZRules : ∀{rs-pre r rs-post rs} →
                  rs-binders-disjoint-rs rs-pre rs →
                  rs-binders-disjoint-rs (r / rs-post) rs →
                  rs-binders-disjoint-zrs (rs-pre / r / rs-post) rs
                 
    data rs-binders-disjoint : ihexp → rules → Set where
      RBDNum    : ∀{n rs} →
                  rs-binders-disjoint (N n) rs
      RBDVar    : ∀{x rs} →
                  rs-binders-disjoint (X x) rs
      RBDLam    : ∀{x τ e rs} →
                  unbound-in-rs x rs →
                  rs-binders-disjoint e rs →
                  rs-binders-disjoint (·λ x ·[ τ ] e) rs
      RBDAp     : ∀{e1 e2 rs} →
                  rs-binders-disjoint e1 rs →
                  rs-binders-disjoint e2 rs →
                  rs-binders-disjoint (e1 ∘ e2) rs
      RBDInl    : ∀{e τ rs} →
                  rs-binders-disjoint e rs →
                  rs-binders-disjoint (inl τ e) rs
      RBDInr    : ∀{e τ rs} →
                  rs-binders-disjoint e rs →
                  rs-binders-disjoint (inr τ e) rs
      RBDMatch  : ∀{e zrs rs} →
                  rs-binders-disjoint e rs →
                  rs-binders-disjoint-zrs zrs rs →
                  rs-binders-disjoint (match e zrs) rs
      RBDPair   : ∀{e1 e2 rs} →
                  rs-binders-disjoint e1 rs →
                  rs-binders-disjoint e2 rs →
                  rs-binders-disjoint ⟨ e1 , e2 ⟩ rs
      RBDFst    : ∀{e rs} →
                  rs-binders-disjoint e rs →
                  rs-binders-disjoint (fst e) rs
      RBDSnd    : ∀{e rs} →
                  rs-binders-disjoint e rs →
                  rs-binders-disjoint (snd e) rs
      RBDEHole  : ∀{u rs} →
                  rs-binders-disjoint ⦇-⦈[ u ] rs
      RBDNEHole : ∀{u e rs} →
                  rs-binders-disjoint e rs →
                  rs-binders-disjoint ⦇⌜ e ⌟⦈[ u ] rs
                 
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
                 binders-unique-rs (r / rs-post) →
                 rs-binders-disjoint-rs rs-pre (r / rs-post) →
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


  mutual
    data hole-binders-disjoint-p : pattrn → ihexp → Set where
      HBDPNum    : ∀{n e} →
                   hole-binders-disjoint-p (N n) e
      HBDPVar    : ∀{x e} →
                   hole-binders-disjoint-p (X x) e
      HBDPInl    : ∀{p e} →
                   hole-binders-disjoint-p p e →
                   hole-binders-disjoint-p (inl p) e
      HBDPInr    : ∀{p e} →
                   hole-binders-disjoint-p p e →
                   hole-binders-disjoint-p (inr p) e
      HBDPPair   : ∀{p1 p2 e} →
                   hole-binders-disjoint-p p1 e →
                   hole-binders-disjoint-p p2 e →
                   hole-binders-disjoint-p ⟨ p1 , p2 ⟩ e
      HBDPWild   : ∀{e} →
                   hole-binders-disjoint-p wild e
      HBDPEHole  : ∀{w e} →
                   hole-unbound-in w e →
                   hole-binders-disjoint-p ⦇-⦈[ w ] e
      HBDPNEHole : ∀{p w τ e} →
                   hole-unbound-in w e →
                   hole-binders-disjoint-p p e →
                   hole-binders-disjoint-p ⦇⌜ p ⌟⦈[ w , τ ] e
      
    data hole-binders-disjoint-r : rule → ihexp → Set where
      HBDRule : ∀{p e1 e2} →
                hole-binders-disjoint-p p e2 →
                hole-binders-disjoint e1 e2 →
                hole-binders-disjoint-r (p => e1) e2
                
    data hole-binders-disjoint-rs : rules → ihexp → Set where
      HBDNoRules : ∀{e} →
                   hole-binders-disjoint-rs nil e
      HBDRules   : ∀{r rs e} →
                   hole-binders-disjoint-r r e →
                   hole-binders-disjoint-rs rs e →
                   hole-binders-disjoint-rs (r / rs) e
                  
    data hole-binders-disjoint-zrs : zrules → ihexp → Set where
      HBDZRules : ∀{rs-pre r rs-post e} →
                  hole-binders-disjoint-rs rs-pre e →
                  hole-binders-disjoint-rs (r / rs-post) e →
                  hole-binders-disjoint-zrs (rs-pre / r / rs-post) e
      
    data hole-binders-disjoint : ihexp → ihexp → Set where
      HBDNum    : ∀{n e} →
                  hole-binders-disjoint (N n) e
      HBDVar    : ∀{x e} →
                  hole-binders-disjoint (X x) e
      HBDLam    : ∀{x τ e1 e2} →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-disjoint (·λ x ·[ τ ] e1) e2
      HBDAp     : ∀{e1 e2 e3} →
                  hole-binders-disjoint e1 e3 →
                  hole-binders-disjoint e2 e3 →
                  hole-binders-disjoint (e1 ∘ e2) e3
      HBDInl    : ∀{e1 τ e2} →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-disjoint (inl τ e1) e2
      HBDInr    : ∀{e1 τ e2} →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-disjoint (inr τ e1) e2
      HBDMatch  : ∀{e1 rs e2} →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-disjoint-zrs rs e2 →
                  hole-binders-disjoint (match e1 rs) e2
      HBDPair   : ∀{e1 e2 e3} →
                  hole-binders-disjoint e1 e3 →
                  hole-binders-disjoint e2 e3 →
                  hole-binders-disjoint ⟨ e1 , e2 ⟩ e3
      HBDFst    : ∀{e1 e2} →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-disjoint (fst e1) e2
      HBDSnd    : ∀{e1 e2} →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-disjoint (snd e1) e2
      HBDEHole  : ∀{u e} →
                  hole-binders-disjoint ⦇-⦈[ u ] e
      HBDNEHole : ∀{u e1 e2} →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-disjoint ⦇⌜ e1 ⌟⦈[ u ] e2
