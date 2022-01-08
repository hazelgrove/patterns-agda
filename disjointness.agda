open import Nat
open import Prelude
open import core
open import freshness

module disjointness where
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
                  hole-binders-disjoint-r r e →
                  hole-binders-disjoint-rs rs-post e →
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
      HBDInl    : ∀{e1 e2 τ} →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-disjoint (inl τ e1) e2
      HBDInr    : ∀{e1 e2 τ} →
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
