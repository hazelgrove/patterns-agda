open import Nat
open import Prelude
open import contexts
open import core
open import binders-disjointness
open import freshness
open import lemmas-contexts

module hole-binders-disjoint-symmetric where
  -- these lemmas build up to proving that the
  -- hole-binders-disjoint judgement is symmetric.
  -- all of them are entirely mechanical, but horribly tedious
  mutual
    lem-hbd-lam : {e : ihexp} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                  hole-binders-disjoint e (·λ x ·[ τ1 ] e1) →
                  hole-binders-disjoint e e1
    lem-hbd-lam HBDNum = HBDNum
    lem-hbd-lam HBDVar = HBDVar
    lem-hbd-lam (HBDLam bd) = HBDLam (lem-hbd-lam bd)
    lem-hbd-lam (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-lam bd1) (lem-hbd-lam bd2)
    lem-hbd-lam (HBDInl bd) = HBDInl (lem-hbd-lam bd)
    lem-hbd-lam (HBDInr bd) = HBDInr (lem-hbd-lam bd)
    lem-hbd-lam (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-lam bd)
               (HBDZRules (lem-hbd-lam-rs bdpre)
                          (lem-hbd-lam-rs bdpost))
    lem-hbd-lam (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-lam bd1) (lem-hbd-lam bd2)
    lem-hbd-lam (HBDFst bd) = HBDFst (lem-hbd-lam bd)
    lem-hbd-lam (HBDSnd bd) = HBDSnd (lem-hbd-lam bd)
    lem-hbd-lam HBDEHole = HBDEHole
    lem-hbd-lam (HBDNEHole bd) = HBDNEHole (lem-hbd-lam bd)

    lem-hbd-lam-rs : {rs : rules} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                     hole-binders-disjoint-rs rs (·λ x ·[ τ1 ] e1) →
                     hole-binders-disjoint-rs rs e1  
    lem-hbd-lam-rs HBDNoRules = HBDNoRules
    lem-hbd-lam-rs (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-lam-r bdr) (lem-hbd-lam-rs bdrs)

    lem-hbd-lam-r : {r : rule} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-r r (·λ x ·[ τ1 ] e1) →
                    hole-binders-disjoint-r r e1
    lem-hbd-lam-r (HBDRule bdp bd) =
      HBDRule (lem-hbd-lam-p bdp) (lem-hbd-lam bd)

    lem-hbd-lam-p : {p : pattrn} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-p p (·λ x ·[ τ1 ] e1) →
                    hole-binders-disjoint-p p e1
    lem-hbd-lam-p HBDPNum = HBDPNum
    lem-hbd-lam-p HBDPVar = HBDPVar
    lem-hbd-lam-p (HBDPInl bd) = HBDPInl (lem-hbd-lam-p bd)
    lem-hbd-lam-p (HBDPInr bd) = HBDPInr (lem-hbd-lam-p bd)
    lem-hbd-lam-p (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-lam-p bd1) (lem-hbd-lam-p bd2)
    lem-hbd-lam-p HBDPWild = HBDPWild
    lem-hbd-lam-p (HBDPEHole (HUBLam ub)) = HBDPEHole ub
    lem-hbd-lam-p (HBDPNEHole (HUBLam ub) bd) =
      HBDPNEHole ub (lem-hbd-lam-p bd)
    
  mutual
    lem-hbd-ap : {e : ihexp} {e1 e2 : ihexp} →
                 hole-binders-disjoint e (e1 ∘ e2) →
                 hole-binders-disjoint e e1 ×
                   hole-binders-disjoint e e2
    lem-hbd-ap HBDNum = HBDNum , HBDNum
    lem-hbd-ap HBDVar = HBDVar , HBDVar
    lem-hbd-ap (HBDLam bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDLam bd1 , HBDLam bd2
    lem-hbd-ap (HBDAp bd1 bd2)
      with lem-hbd-ap bd1 | lem-hbd-ap bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDAp bd1₁ bd2₁ , HBDAp bd1₂ bd2₂
    lem-hbd-ap (HBDInl bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDInl bd1 , HBDInl bd2
    lem-hbd-ap (HBDInr bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDInr bd1 , HBDInr bd2
    lem-hbd-ap (HBDMatch bd (HBDZRules pret postt))
      with lem-hbd-ap bd |
           lem-hbd-ap-rs pret |
           lem-hbd-ap-rs postt
    ... | bd1 , bd2 
        |  bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      HBDMatch bd1 (HBDZRules bdpre1 bdpost1) ,
      HBDMatch bd2 (HBDZRules bdpre2 bdpost2)
    lem-hbd-ap (HBDPair bd1 bd2)
      with lem-hbd-ap bd1 | lem-hbd-ap bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPair bd1₁ bd2₁ , HBDPair bd1₂ bd2₂
    lem-hbd-ap (HBDFst bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDFst bd1 , HBDFst bd2
    lem-hbd-ap (HBDSnd bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDSnd bd1 , HBDSnd bd2
    lem-hbd-ap HBDEHole = HBDEHole , HBDEHole
    lem-hbd-ap (HBDNEHole bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDNEHole bd1 , HBDNEHole bd2

    lem-hbd-ap-rs : {rs : rules} {e1 e2 : ihexp} →
                    hole-binders-disjoint-rs rs (e1 ∘ e2) →
                    hole-binders-disjoint-rs rs e1 ×
                      hole-binders-disjoint-rs rs e2
    lem-hbd-ap-rs HBDNoRules = HBDNoRules , HBDNoRules
    lem-hbd-ap-rs (HBDRules bdr bdrs)
      with lem-hbd-ap-r bdr | lem-hbd-ap-rs bdrs
    ... | bdr1 , bdr2 | bd1 , bd2 =
      HBDRules bdr1 bd1 , HBDRules bdr2 bd2
      
    lem-hbd-ap-r : {r : rule} {e1 e2 : ihexp} →
                   hole-binders-disjoint-r r (e1 ∘ e2) →
                   hole-binders-disjoint-r r e1 ×
                     hole-binders-disjoint-r r e2
    lem-hbd-ap-r (HBDRule pt bd)
      with lem-hbd-ap-p pt | lem-hbd-ap bd
    ... | pt1 , pt2 | bd1 , bd2 =
      HBDRule pt1 bd1 , HBDRule pt2 bd2

    lem-hbd-ap-p : {p : pattrn} {e1 e2 : ihexp} →
                   hole-binders-disjoint-p p (e1 ∘ e2) →
                   hole-binders-disjoint-p p e1 ×
                     hole-binders-disjoint-p p e2
    lem-hbd-ap-p HBDPNum = HBDPNum , HBDPNum
    lem-hbd-ap-p HBDPVar = HBDPVar , HBDPVar
    lem-hbd-ap-p (HBDPInl bd)
      with lem-hbd-ap-p bd
    ... | bd1 , bd2 = HBDPInl bd1 , HBDPInl bd2
    lem-hbd-ap-p (HBDPInr bd)
      with lem-hbd-ap-p bd
    ... | bd1 , bd2 = HBDPInr bd1 , HBDPInr bd2
    lem-hbd-ap-p (HBDPPair bd1 bd2)
      with lem-hbd-ap-p bd1 | lem-hbd-ap-p bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPPair bd1₁ bd2₁ , HBDPPair bd1₂ bd2₂
    lem-hbd-ap-p HBDPWild = HBDPWild , HBDPWild
    lem-hbd-ap-p (HBDPEHole (HUBAp ub1 ub2)) =
      HBDPEHole ub1 , HBDPEHole ub2
    lem-hbd-ap-p (HBDPNEHole (HUBAp ub1 ub2) bd)
      with lem-hbd-ap-p bd
    ... | bd1 , bd2 = HBDPNEHole ub1 bd1 , HBDPNEHole ub2 bd2

  mutual
    lem-hbd-inl : {e : ihexp} {τ : htyp} {e1 : ihexp} →
                  hole-binders-disjoint e (inl τ e1) →
                  hole-binders-disjoint e e1
    lem-hbd-inl HBDNum = HBDNum
    lem-hbd-inl HBDVar = HBDVar
    lem-hbd-inl (HBDLam bd) = HBDLam (lem-hbd-inl bd)
    lem-hbd-inl (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-inl bd1) (lem-hbd-inl bd2)
    lem-hbd-inl (HBDInl bd) = HBDInl (lem-hbd-inl bd)
    lem-hbd-inl (HBDInr bd) = HBDInr (lem-hbd-inl bd)
    lem-hbd-inl (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-inl bd)
              (HBDZRules (lem-hbd-inl-rs bdpre)
                        (lem-hbd-inl-rs bdpost))
    lem-hbd-inl (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-inl bd1) (lem-hbd-inl bd2)
    lem-hbd-inl (HBDFst bd) = HBDFst (lem-hbd-inl bd)
    lem-hbd-inl (HBDSnd bd) = HBDSnd (lem-hbd-inl bd)
    lem-hbd-inl HBDEHole = HBDEHole
    lem-hbd-inl (HBDNEHole bd) = HBDNEHole (lem-hbd-inl bd)

    lem-hbd-inl-rs : {rs : rules} {τ : htyp} {e1 : ihexp} →
                     hole-binders-disjoint-rs rs (inl τ e1) →
                     hole-binders-disjoint-rs rs e1
    lem-hbd-inl-rs HBDNoRules = HBDNoRules
    lem-hbd-inl-rs (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-inl-r bdr) (lem-hbd-inl-rs bdrs)

    lem-hbd-inl-r : {r : rule} {τ : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-r r (inl τ e1) →
                    hole-binders-disjoint-r r e1
    lem-hbd-inl-r (HBDRule bdp bd) =
      HBDRule (lem-hbd-inl-p bdp) (lem-hbd-inl bd)

    lem-hbd-inl-p : {p : pattrn} {τ : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-p p (inl τ e1) →
                    hole-binders-disjoint-p p e1
    lem-hbd-inl-p HBDPNum = HBDPNum
    lem-hbd-inl-p HBDPVar = HBDPVar
    lem-hbd-inl-p (HBDPInl bd) = HBDPInl (lem-hbd-inl-p bd)
    lem-hbd-inl-p (HBDPInr bd) = HBDPInr (lem-hbd-inl-p bd)
    lem-hbd-inl-p (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-inl-p bd1) (lem-hbd-inl-p bd2)
    lem-hbd-inl-p HBDPWild = HBDPWild
    lem-hbd-inl-p (HBDPEHole (HUBInl ub)) = HBDPEHole ub
    lem-hbd-inl-p (HBDPNEHole (HUBInl ub) bd) =
      HBDPNEHole ub (lem-hbd-inl-p bd)
    
  mutual
    lem-hbd-inr : {e : ihexp} {τ : htyp} {e1 : ihexp} →
                  hole-binders-disjoint e (inr τ e1) →
                  hole-binders-disjoint e e1
    lem-hbd-inr HBDNum = HBDNum
    lem-hbd-inr HBDVar = HBDVar
    lem-hbd-inr (HBDLam bd) = HBDLam (lem-hbd-inr bd)
    lem-hbd-inr (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-inr bd1) (lem-hbd-inr bd2)
    lem-hbd-inr (HBDInl bd) = HBDInl (lem-hbd-inr bd)
    lem-hbd-inr (HBDInr bd) = HBDInr (lem-hbd-inr bd)
    lem-hbd-inr (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-inr bd)
              (HBDZRules (lem-hbd-inr-rs bdpre)
                        (lem-hbd-inr-rs bdpost))
    lem-hbd-inr (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-inr bd1) (lem-hbd-inr bd2)
    lem-hbd-inr (HBDFst bd) = HBDFst (lem-hbd-inr bd)
    lem-hbd-inr (HBDSnd bd) = HBDSnd (lem-hbd-inr bd)
    lem-hbd-inr HBDEHole = HBDEHole
    lem-hbd-inr (HBDNEHole bd) = HBDNEHole (lem-hbd-inr bd)

    lem-hbd-inr-rs : {rs : rules} {τ : htyp} {e1 : ihexp} →
                     hole-binders-disjoint-rs rs (inr τ e1) →
                     hole-binders-disjoint-rs rs e1
    lem-hbd-inr-rs HBDNoRules = HBDNoRules
    lem-hbd-inr-rs (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-inr-r bdr) (lem-hbd-inr-rs bdrs)

    lem-hbd-inr-r : {r : rule} {τ : htyp} {e1 : ihexp}  →
                    hole-binders-disjoint-r r (inr τ e1) →
                    hole-binders-disjoint-r r e1
    lem-hbd-inr-r (HBDRule bdp bd) =
      HBDRule (lem-hbd-inr-p bdp) (lem-hbd-inr bd)

    lem-hbd-inr-p : {p : pattrn} {τ : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-p p (inr τ e1) →
                    hole-binders-disjoint-p p e1
    lem-hbd-inr-p HBDPNum = HBDPNum
    lem-hbd-inr-p HBDPVar = HBDPVar
    lem-hbd-inr-p (HBDPInl bd) = HBDPInl (lem-hbd-inr-p bd)
    lem-hbd-inr-p (HBDPInr bd) = HBDPInr (lem-hbd-inr-p bd)
    lem-hbd-inr-p (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-inr-p bd1) (lem-hbd-inr-p bd2)
    lem-hbd-inr-p HBDPWild = HBDPWild
    lem-hbd-inr-p (HBDPEHole (HUBInr ub)) = HBDPEHole ub
    lem-hbd-inr-p (HBDPNEHole (HUBInr ub) bd) =
      HBDPNEHole ub (lem-hbd-inr-p bd)
    
  mutual
    lem-hbd-match : {e : ihexp} {e1 : ihexp}
                    {rs-pre : rules} {r : rule} {rs-post : rules} →
                    hole-binders-disjoint e
                      (match e1 (rs-pre / r / rs-post)) →
                    hole-binders-disjoint e e1 ×
                      hole-binders-disjoint e rs-pre ×
                        hole-binders-disjoint e r ×
                          hole-binders-disjoint e rs-post
    lem-hbd-match HBDNum = HBDNum , HBDNum , HBDNum , HBDNum
    lem-hbd-match HBDVar = HBDVar , HBDVar , HBDVar , HBDVar
    lem-hbd-match (HBDLam bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDLam bd' , HBDLam bdpre , HBDLam bdr , HBDLam bdpost
    lem-hbd-match (HBDAp bd1 bd2)
      with lem-hbd-match bd1 | lem-hbd-match bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1 |
          bd2' , bdpre2 , bdr2 , bdpost2 =
      HBDAp bd1' bd2' ,
      HBDAp bdpre1 bdpre2 ,
      HBDAp bdr1 bdr2 ,
      HBDAp bdpost1 bdpost2 
    lem-hbd-match (HBDInl bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDInl bd' , HBDInl bdpre , HBDInl bdr , HBDInl bdpost
    lem-hbd-match (HBDInr bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDInr bd' , HBDInr bdpre , HBDInr bdr , HBDInr bdpost
    lem-hbd-match (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-hbd-match bd |
           lem-hbd-match-rs bdpre |
           lem-hbd-match-rs bdpost
    ... | bd' , bdpre , bdr , bdpost
        | bdpre' , bdprepre , bdprer , bdprepost
        | bdpost' , bdpostpre , bdpostr , bdpostpost =
      HBDMatch bd' (HBDZRules bdpre' bdpost') ,
      HBDMatch bdpre (HBDZRules bdprepre bdpostpre) ,
      HBDMatch bdr (HBDZRules bdprer bdpostr) ,
      HBDMatch bdpost (HBDZRules bdprepost bdpostpost)
    lem-hbd-match (HBDPair bd1 bd2)
      with lem-hbd-match bd1 | lem-hbd-match bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1 |
          bd2' , bdpre2 , bdr2 , bdpost2 =
      HBDPair bd1' bd2' ,
      HBDPair bdpre1 bdpre2 ,
      HBDPair bdr1 bdr2 ,
      HBDPair bdpost1 bdpost2 
    lem-hbd-match (HBDFst bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDFst bd' , HBDFst bdpre , HBDFst bdr , HBDFst bdpost
    lem-hbd-match (HBDSnd bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDSnd bd' , HBDSnd bdpre , HBDSnd bdr , HBDSnd bdpost
    lem-hbd-match HBDEHole =
      HBDEHole , HBDEHole , HBDEHole , HBDEHole
    lem-hbd-match (HBDNEHole bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDNEHole bd' , HBDNEHole bdpre ,
      HBDNEHole bdr , HBDNEHole bdpost

    lem-hbd-match-rs : {rs : rules} {e1 : ihexp}
                       {rs-pre : rules} {r : rule} {rs-post : rules} →
                       hole-binders-disjoint-rs rs
                         (match e1 (rs-pre / r / rs-post)) →
                       hole-binders-disjoint-rs rs e1 ×
                         hole-binders-disjoint-rs rs rs-pre ×
                           hole-binders-disjoint-rs rs r ×
                             hole-binders-disjoint-rs rs rs-post
    lem-hbd-match-rs HBDNoRules =
      HBDNoRules , HBDNoRules , HBDNoRules , HBDNoRules 
    lem-hbd-match-rs (HBDRules bdr bdrs)
      with lem-hbd-match-r bdr | lem-hbd-match-rs bdrs
    ... | bdr' , bdrpre , bdrr , bdrpost
        | bdrs' , bdrspre , bdrsr , bdrspost =
      HBDRules bdr' bdrs' ,
      HBDRules bdrpre bdrspre ,
      HBDRules bdrr bdrsr ,
      HBDRules bdrpost bdrspost

    lem-hbd-match-r : {r : rule} {e1 : ihexp}
                      {rs-pre : rules} {r1 : rule} {rs-post : rules} →
                      hole-binders-disjoint-r r
                        (match e1 (rs-pre / r1 / rs-post)) →
                      hole-binders-disjoint-r r e1 ×
                        hole-binders-disjoint-r r rs-pre ×
                          hole-binders-disjoint-r r r1 ×
                            hole-binders-disjoint-r r rs-post
    lem-hbd-match-r (HBDRule bdp bd)
      with lem-hbd-match-p bdp | lem-hbd-match bd
    ... | bdp' , bdppre , bdpr , bdppost
        | bd' , bdpre , bdr , bdpost =
      HBDRule bdp' bd' ,
      HBDRule bdppre bdpre ,
      HBDRule bdpr bdr ,
      HBDRule bdppost bdpost
  
    lem-hbd-match-p : {p : pattrn} {e1 : ihexp}
                      {rs-pre : rules} {r1 : rule} {rs-post : rules} →
                      hole-binders-disjoint-p p
                        (match e1 (rs-pre / r1 / rs-post)) →
                      hole-binders-disjoint-p p e1 ×
                        hole-binders-disjoint-p p rs-pre ×
                          hole-binders-disjoint-p p r1 ×
                            hole-binders-disjoint-p p rs-post
    lem-hbd-match-p HBDPNum = HBDPNum , HBDPNum , HBDPNum , HBDPNum
    lem-hbd-match-p HBDPVar =
      HBDPVar , HBDPVar , HBDPVar , HBDPVar
    lem-hbd-match-p (HBDPInl bd)
      with lem-hbd-match-p bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDPInl bd' , HBDPInl bdpre , HBDPInl bdr , HBDPInl bdpost
    lem-hbd-match-p (HBDPInr bd)
      with lem-hbd-match-p bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDPInr bd' , HBDPInr bdpre , HBDPInr bdr , HBDPInr bdpost
    lem-hbd-match-p (HBDPPair bd1 bd2)
      with lem-hbd-match-p bd1 | lem-hbd-match-p bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1
        | bd2' , bdpre2 , bdr2 , bdpost2 =
      HBDPPair bd1' bd2' ,
      HBDPPair bdpre1 bdpre2 ,
      HBDPPair bdr1 bdr2 ,
      HBDPPair bdpost1 bdpost2
    lem-hbd-match-p HBDPWild =
      HBDPWild , HBDPWild , HBDPWild , HBDPWild
    lem-hbd-match-p (HBDPEHole
                      (HUBMatch ub
                        (HUBZRules ubpre (HUBRules ubr ubpost)))) =
      HBDPEHole ub , HBDPEHole ubpre , HBDPEHole ubr , HBDPEHole ubpost
    lem-hbd-match-p (HBDPNEHole
                      (HUBMatch ub
                        (HUBZRules ubpre (HUBRules ubr ubpost))) bd)
      with lem-hbd-match-p bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDPNEHole ub bd' , HBDPNEHole ubpre bdpre ,
      HBDPNEHole ubr bdr , HBDPNEHole ubpost bdpost
    
  mutual
    lem-hbd-pair : {e : ihexp} {e1 e2 : ihexp} →
                   hole-binders-disjoint e ⟨ e1 , e2 ⟩ →
                   (hole-binders-disjoint e e1) ×
                     (hole-binders-disjoint e e2)
    lem-hbd-pair HBDNum = HBDNum , HBDNum
    lem-hbd-pair HBDVar = HBDVar , HBDVar
    lem-hbd-pair (HBDLam bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDLam bd1 , HBDLam bd2
    lem-hbd-pair (HBDAp bd1 bd2)
      with lem-hbd-pair bd1 | lem-hbd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDAp bd1₁ bd2₁ , HBDAp bd1₂ bd2₂
    lem-hbd-pair (HBDInl bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDInl bd1 , HBDInl bd2
    lem-hbd-pair (HBDInr bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDInr bd1 , HBDInr bd2
    lem-hbd-pair (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-hbd-pair bd |
           lem-hbd-pair-rs bdpre |
           lem-hbd-pair-rs bdpost
    ... | bd1 , bd2
        | bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      HBDMatch bd1 (HBDZRules bdpre1 bdpost1) ,
      HBDMatch bd2 (HBDZRules bdpre2 bdpost2)
    lem-hbd-pair (HBDPair bd1 bd2)
      with lem-hbd-pair bd1 | lem-hbd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPair bd1₁ bd2₁ , HBDPair bd1₂ bd2₂
    lem-hbd-pair (HBDFst bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDFst bd1 , HBDFst bd2
    lem-hbd-pair (HBDSnd bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDSnd bd1 , HBDSnd bd2
    lem-hbd-pair HBDEHole = HBDEHole , HBDEHole
    lem-hbd-pair (HBDNEHole bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDNEHole bd1 , HBDNEHole bd2

    lem-hbd-pair-rs : {rs : rules} {e1 e2 : ihexp} →
                      hole-binders-disjoint-rs rs ⟨ e1 , e2 ⟩ →
                      (hole-binders-disjoint-rs rs e1) ×
                        (hole-binders-disjoint-rs rs e2)
    lem-hbd-pair-rs HBDNoRules = HBDNoRules , HBDNoRules
    lem-hbd-pair-rs (HBDRules bdr bdrs)
      with lem-hbd-pair-r bdr | lem-hbd-pair-rs bdrs
    ... | bdr1 , bdr2 | bdrs1 , bdrs2 =
      HBDRules bdr1 bdrs1 , HBDRules bdr2 bdrs2

    lem-hbd-pair-r : {r : rule} {e1 e2 : ihexp} →
                     hole-binders-disjoint-r r ⟨ e1 , e2 ⟩ →
                     (hole-binders-disjoint-r r e1) ×
                       (hole-binders-disjoint-r r e2)
    lem-hbd-pair-r (HBDRule bdp bd)
      with lem-hbd-pair-p bdp | lem-hbd-pair bd
    ... | bdp' , ubp | bd' , ub =
      HBDRule bdp' bd' , HBDRule ubp ub

    lem-hbd-pair-p : {p : pattrn} {e1 e2 : ihexp} →
                     hole-binders-disjoint-p p ⟨ e1 , e2 ⟩ →
                     (hole-binders-disjoint-p p e1) ×
                       (hole-binders-disjoint-p p e2)
    lem-hbd-pair-p HBDPNum = HBDPNum , HBDPNum
    lem-hbd-pair-p HBDPVar = HBDPVar , HBDPVar
    lem-hbd-pair-p (HBDPInl bd)
      with lem-hbd-pair-p bd
    ... | bd1 , bd2 = HBDPInl bd1 , HBDPInl bd2
    lem-hbd-pair-p (HBDPInr bd)
      with lem-hbd-pair-p bd
    ... | bd1 , bd2 = HBDPInr bd1 , HBDPInr bd2
    lem-hbd-pair-p (HBDPPair bd1 bd2)
      with lem-hbd-pair-p bd1 | lem-hbd-pair-p bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPPair bd1₁ bd2₁ , HBDPPair bd1₂ bd2₂
    lem-hbd-pair-p HBDPWild = HBDPWild , HBDPWild
    lem-hbd-pair-p (HBDPEHole (HUBPair ub1 ub2))=
      HBDPEHole ub1 , HBDPEHole ub2
    lem-hbd-pair-p (HBDPNEHole (HUBPair ub1 ub2) bd)
      with lem-hbd-pair-p bd
    ... | bd1 , bd2 = HBDPNEHole ub1 bd1 , HBDPNEHole ub2 bd2
    
  mutual
    lem-hbd-fst : {e : ihexp} {e1 : ihexp} →
                  hole-binders-disjoint e (fst e1) →
                  hole-binders-disjoint e e1
    lem-hbd-fst HBDNum = HBDNum
    lem-hbd-fst HBDVar = HBDVar
    lem-hbd-fst (HBDLam bd) = HBDLam (lem-hbd-fst bd)
    lem-hbd-fst (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-fst bd1) (lem-hbd-fst bd2)
    lem-hbd-fst (HBDInl bd) = HBDInl (lem-hbd-fst bd)
    lem-hbd-fst (HBDInr bd) = HBDInr (lem-hbd-fst bd)
    lem-hbd-fst (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-fst bd)
              (HBDZRules (lem-hbd-fst-rs bdpre)
                        (lem-hbd-fst-rs bdpost))
    lem-hbd-fst (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-fst bd1) (lem-hbd-fst bd2)
    lem-hbd-fst (HBDFst bd) = HBDFst (lem-hbd-fst bd)
    lem-hbd-fst (HBDSnd bd) = HBDSnd (lem-hbd-fst bd)
    lem-hbd-fst HBDEHole = HBDEHole
    lem-hbd-fst (HBDNEHole bd) = HBDNEHole (lem-hbd-fst bd)

    lem-hbd-fst-rs : {rs : rules} {e1 : ihexp} →
                     hole-binders-disjoint-rs rs (fst e1) →
                     hole-binders-disjoint-rs rs e1
    lem-hbd-fst-rs HBDNoRules = HBDNoRules
    lem-hbd-fst-rs (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-fst-r bdr) (lem-hbd-fst-rs bdrs)

    lem-hbd-fst-r : {r : rule} {e1 : ihexp} →
                    hole-binders-disjoint-r r (fst e1) →
                    hole-binders-disjoint-r r e1
    lem-hbd-fst-r (HBDRule bdp bd) =
      HBDRule (lem-hbd-fst-p bdp) (lem-hbd-fst bd)

    lem-hbd-fst-p : {p : pattrn} {e1 : ihexp} →
                    hole-binders-disjoint-p p (fst e1) →
                    hole-binders-disjoint-p p e1
    lem-hbd-fst-p HBDPNum = HBDPNum
    lem-hbd-fst-p HBDPVar = HBDPVar
    lem-hbd-fst-p (HBDPInl bd) = HBDPInl (lem-hbd-fst-p bd)
    lem-hbd-fst-p (HBDPInr bd) = HBDPInr (lem-hbd-fst-p bd)
    lem-hbd-fst-p (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-fst-p bd1) (lem-hbd-fst-p bd2)
    lem-hbd-fst-p HBDPWild = HBDPWild
    lem-hbd-fst-p (HBDPEHole (HUBFst ub)) = HBDPEHole ub
    lem-hbd-fst-p (HBDPNEHole (HUBFst ub) bd) =
      HBDPNEHole ub (lem-hbd-fst-p bd)
    
  mutual
    lem-hbd-snd : {e : ihexp} {e1 : ihexp} →
                  hole-binders-disjoint e (snd e1) →
                  hole-binders-disjoint e e1
    lem-hbd-snd HBDNum = HBDNum
    lem-hbd-snd HBDVar = HBDVar
    lem-hbd-snd (HBDLam bd) = HBDLam (lem-hbd-snd bd)
    lem-hbd-snd (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-snd bd1) (lem-hbd-snd bd2)
    lem-hbd-snd (HBDInl bd) = HBDInl (lem-hbd-snd bd)
    lem-hbd-snd (HBDInr bd) = HBDInr (lem-hbd-snd bd)
    lem-hbd-snd (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-snd bd)
              (HBDZRules (lem-hbd-snd-rs bdpre)
                        (lem-hbd-snd-rs bdpost))
    lem-hbd-snd (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-snd bd1) (lem-hbd-snd bd2)
    lem-hbd-snd (HBDFst bd) = HBDFst (lem-hbd-snd bd)
    lem-hbd-snd (HBDSnd bd) = HBDSnd (lem-hbd-snd bd)
    lem-hbd-snd HBDEHole = HBDEHole
    lem-hbd-snd (HBDNEHole bd) = HBDNEHole (lem-hbd-snd bd)

    lem-hbd-snd-rs : {rs : rules} {e1 : ihexp} →
                     hole-binders-disjoint-rs rs (snd e1) →
                     hole-binders-disjoint-rs rs e1
    lem-hbd-snd-rs HBDNoRules = HBDNoRules
    lem-hbd-snd-rs (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-snd-r bdr) (lem-hbd-snd-rs bdrs)

    lem-hbd-snd-r : {r : rule} {e1 : ihexp} →
                    hole-binders-disjoint-r r (snd e1) →
                    hole-binders-disjoint-r r e1
    lem-hbd-snd-r (HBDRule bdp bd) =
      HBDRule (lem-hbd-snd-p bdp) (lem-hbd-snd bd)

    lem-hbd-snd-p : {p : pattrn} {e1 : ihexp} →
                    hole-binders-disjoint-p p (snd e1) →
                    hole-binders-disjoint-p p e1
    lem-hbd-snd-p HBDPNum = HBDPNum
    lem-hbd-snd-p HBDPVar = HBDPVar
    lem-hbd-snd-p (HBDPInl bd) = HBDPInl (lem-hbd-snd-p bd)
    lem-hbd-snd-p (HBDPInr bd) = HBDPInr (lem-hbd-snd-p bd)
    lem-hbd-snd-p (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-snd-p bd1) (lem-hbd-snd-p bd2)
    lem-hbd-snd-p HBDPWild = HBDPWild
    lem-hbd-snd-p (HBDPEHole (HUBSnd ub)) = HBDPEHole ub
    lem-hbd-snd-p (HBDPNEHole (HUBSnd ub) bd) =
      HBDPNEHole ub (lem-hbd-snd-p bd)

  mutual
    lem-hbd-nehole : {e : ihexp} {e1 : ihexp} {u : Nat} →
                     hole-binders-disjoint e ⦇⌜ e1 ⌟⦈[ u ] →
                     hole-binders-disjoint e e1
    lem-hbd-nehole HBDNum = HBDNum
    lem-hbd-nehole HBDVar = HBDVar
    lem-hbd-nehole (HBDLam bd) =
      HBDLam (lem-hbd-nehole bd)
    lem-hbd-nehole (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-nehole bd1) (lem-hbd-nehole bd2)
    lem-hbd-nehole (HBDInl bd) = HBDInl (lem-hbd-nehole bd)
    lem-hbd-nehole (HBDInr bd) = HBDInr (lem-hbd-nehole bd)
    lem-hbd-nehole (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-nehole bd)
              (HBDZRules (lem-hbd-nehole-rs bdpre)
                        (lem-hbd-nehole-rs bdpost))
    lem-hbd-nehole (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-nehole bd1) (lem-hbd-nehole bd2)
    lem-hbd-nehole (HBDFst bd) = HBDFst (lem-hbd-nehole bd)
    lem-hbd-nehole (HBDSnd bd) = HBDSnd (lem-hbd-nehole bd)
    lem-hbd-nehole HBDEHole = HBDEHole
    lem-hbd-nehole (HBDNEHole bd) =
      HBDNEHole (lem-hbd-nehole bd)

    lem-hbd-nehole-rs : {rs : rules} {e1 : ihexp} {u : Nat} →
                        hole-binders-disjoint-rs rs ⦇⌜ e1 ⌟⦈[ u ] →
                        hole-binders-disjoint-rs rs e1
    lem-hbd-nehole-rs HBDNoRules = HBDNoRules
    lem-hbd-nehole-rs (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-nehole-r bdr) (lem-hbd-nehole-rs bdrs)

    lem-hbd-nehole-r : {r : rule} {e1 : ihexp} {u : Nat} →
                       hole-binders-disjoint-r r ⦇⌜ e1 ⌟⦈[ u ] →
                       hole-binders-disjoint-r r e1
    lem-hbd-nehole-r (HBDRule bdp bd) =
      HBDRule (lem-hbd-nehole-p bdp) (lem-hbd-nehole bd)

    lem-hbd-nehole-p : {p : pattrn} {e1 : ihexp} {u : Nat} →
                       hole-binders-disjoint-p p ⦇⌜ e1 ⌟⦈[ u ] →
                       hole-binders-disjoint-p p e1
    lem-hbd-nehole-p HBDPNum = HBDPNum
    lem-hbd-nehole-p HBDPVar = HBDPVar
    lem-hbd-nehole-p (HBDPInl bd) = HBDPInl (lem-hbd-nehole-p bd)
    lem-hbd-nehole-p (HBDPInr bd) = HBDPInr (lem-hbd-nehole-p bd)
    lem-hbd-nehole-p (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-nehole-p bd1) (lem-hbd-nehole-p bd2)
    lem-hbd-nehole-p HBDPWild = HBDPWild
    lem-hbd-nehole-p (HBDPEHole (HUBNEHole ub)) = HBDPEHole ub
    lem-hbd-nehole-p (HBDPNEHole (HUBNEHole ub) bd) =
      HBDPNEHole ub (lem-hbd-nehole-p bd)
      
  mutual
    lem-rs-hbd : {e : ihexp} {r : rule} {rs : rules} →
                 hole-binders-disjoint e (r / rs) →
                 hole-binders-disjoint e r ×
                   hole-binders-disjoint e rs
    lem-rs-hbd HBDNum = HBDNum , HBDNum
    lem-rs-hbd HBDVar = HBDVar , HBDVar
    lem-rs-hbd (HBDLam bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs = HBDLam bdr , HBDLam bdrs
    lem-rs-hbd (HBDAp bd1 bd2)
      with lem-rs-hbd bd1 | lem-rs-hbd bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2 =
      HBDAp bdr1 bdr2 , HBDAp bdrs1 bdrs2
    lem-rs-hbd (HBDInl bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs = HBDInl bdr , HBDInl bdrs
    lem-rs-hbd (HBDInr bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs = HBDInr bdr , HBDInr bdrs
    lem-rs-hbd (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-rs-hbd bd |
           lem-rs-hbd-rs bdpre |
           lem-rs-hbd-rs bdpost
    ... | bdr , bdrs
        | bdprer , bdprers
        | bdpostr , bdpostrs =
      HBDMatch bdr (HBDZRules bdprer bdpostr) ,
      HBDMatch bdrs (HBDZRules bdprers bdpostrs)
    lem-rs-hbd (HBDPair bd1 bd2)
      with lem-rs-hbd bd1 | lem-rs-hbd bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2 =
      HBDPair bdr1 bdr2 , HBDPair bdrs1 bdrs2
    lem-rs-hbd (HBDFst bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs = HBDFst bdr , HBDFst bdrs
    lem-rs-hbd (HBDSnd bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs = HBDSnd bdr , HBDSnd bdrs
    lem-rs-hbd HBDEHole = HBDEHole , HBDEHole
    lem-rs-hbd (HBDNEHole bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs =
      HBDNEHole bdr , HBDNEHole bdrs

    lem-rs-hbd-rs : {rs1 : rules} {r : rule} {rs2 : rules} →
                    hole-binders-disjoint-rs rs1 (r / rs2) →
                    hole-binders-disjoint-rs rs1 r ×
                      hole-binders-disjoint-rs rs1 rs2
    lem-rs-hbd-rs HBDNoRules = HBDNoRules , HBDNoRules
    lem-rs-hbd-rs (HBDRules bdr bdrs)
      with lem-rs-hbd-r bdr | lem-rs-hbd-rs bdrs
    ... | bdrr , bdrrs | bdrsr , bdrsrs =
      HBDRules bdrr bdrsr , HBDRules bdrrs bdrsrs
   
    lem-rs-hbd-r : {r1 : rule} {r2 : rule} {rs : rules} →
                   hole-binders-disjoint-r r1 (r2 / rs) →
                   hole-binders-disjoint-r r1 r2 ×
                     hole-binders-disjoint-r r1 rs
    lem-rs-hbd-r (HBDRule bdp bd)
      with lem-rs-hbd-p bdp | lem-rs-hbd bd
    ... | bdpr , bdprs | bdr , bdrs =
      HBDRule bdpr bdr , HBDRule bdprs bdrs

    lem-rs-hbd-p : {p : pattrn} {r : rule} {rs : rules} →
                   hole-binders-disjoint-p p (r / rs) →
                   hole-binders-disjoint-p p r ×
                     hole-binders-disjoint-p p rs
    lem-rs-hbd-p HBDPNum = HBDPNum , HBDPNum
    lem-rs-hbd-p HBDPVar = HBDPVar , HBDPVar
    lem-rs-hbd-p (HBDPInl bd)
      with lem-rs-hbd-p bd
    ... | bdr , bdrs = HBDPInl bdr , HBDPInl bdrs
    lem-rs-hbd-p (HBDPInr bd)
      with lem-rs-hbd-p bd
    ... | bdr , bdrs = HBDPInr bdr , HBDPInr bdrs
    lem-rs-hbd-p (HBDPPair bd1 bd2)
      with lem-rs-hbd-p bd1 | lem-rs-hbd-p bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2  =
      HBDPPair bdr1 bdr2 , HBDPPair bdrs1 bdrs2
    lem-rs-hbd-p HBDPWild = HBDPWild , HBDPWild
    lem-rs-hbd-p (HBDPEHole (HUBRules ubr ubrs)) =
      HBDPEHole ubr , HBDPEHole ubrs
    lem-rs-hbd-p (HBDPNEHole (HUBRules ubr ubrs) bd)
      with lem-rs-hbd-p bd
    ... | bdr , bdrs = HBDPNEHole ubr bdr , HBDPNEHole ubrs bdrs
    
  mutual
    lem-r-hbd : {e : ihexp} {pr : pattrn} {er : ihexp} →
                hole-binders-disjoint e (pr => er) →
                hole-binders-disjoint e pr ×
                  hole-binders-disjoint e er
    lem-r-hbd HBDNum = HBDNum , HBDNum
    lem-r-hbd HBDVar = HBDVar , HBDVar
    lem-r-hbd (HBDLam bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDLam bdp , HBDLam bdr
    lem-r-hbd (HBDAp bd1 bd2)
      with lem-r-hbd bd1 | lem-r-hbd bd2
    ... | bdp1 , bdr1 | bdp2 , bdr2 =
      HBDAp bdp1 bdp2 , HBDAp bdr1 bdr2
    lem-r-hbd (HBDInl bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDInl bdp , HBDInl bdr
    lem-r-hbd (HBDInr bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDInr bdp , HBDInr bdr
    lem-r-hbd (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-r-hbd bd |
           lem-r-hbd-rs bdpre |
           lem-r-hbd-rs bdpost 
    ... | bdp , bdr
        | bdprep , bdprer
        | bdpostp , bdpostr =
      HBDMatch bdp (HBDZRules bdprep bdpostp) ,
      HBDMatch bdr (HBDZRules bdprer bdpostr)
    lem-r-hbd (HBDPair bd1 bd2)
      with lem-r-hbd bd1 | lem-r-hbd bd2
    ... | bdp1 , bdr1 | bdp2 , bdr2 =
      HBDPair bdp1 bdp2 , HBDPair bdr1 bdr2
    lem-r-hbd (HBDFst bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDFst bdp , HBDFst bdr
    lem-r-hbd (HBDSnd bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDSnd bdp , HBDSnd bdr
    lem-r-hbd HBDEHole = HBDEHole , HBDEHole
    lem-r-hbd (HBDNEHole bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDNEHole bdp , HBDNEHole bdr

    lem-r-hbd-rs : {rs : rules} {pr : pattrn} {er : ihexp} →
                   hole-binders-disjoint-rs rs (pr => er) →
                   hole-binders-disjoint-rs rs pr ×
                     hole-binders-disjoint-rs rs er
    lem-r-hbd-rs HBDNoRules = HBDNoRules , HBDNoRules
    lem-r-hbd-rs (HBDRules bdr bdrs)
      with lem-r-hbd-r bdr | lem-r-hbd-rs bdrs
    ... | bdrp , bdre | bdrsp , bdrse =
      HBDRules bdrp bdrsp , HBDRules bdre bdrse

    lem-r-hbd-r : {r : rule} {pr : pattrn} {er : ihexp} →
                  hole-binders-disjoint-r r (pr => er) →
                  hole-binders-disjoint-r r pr ×
                    hole-binders-disjoint-r r er
    lem-r-hbd-r (HBDRule bdp bd)
      with lem-r-hbd-p bdp | lem-r-hbd bd
    ... | bdpp , bdpe | ebdp , ebde =
      HBDRule bdpp ebdp , HBDRule bdpe ebde

    lem-r-hbd-p : {p : pattrn} {pr : pattrn} {er : ihexp} →
                  hole-binders-disjoint-p p (pr => er) →
                  hole-binders-disjoint-p p pr ×
                    hole-binders-disjoint-p p er
    lem-r-hbd-p HBDPNum = HBDPNum , HBDPNum
    lem-r-hbd-p HBDPVar = HBDPVar , HBDPVar
    lem-r-hbd-p (HBDPInl bd)
      with lem-r-hbd-p bd
    ... | bdp , bde = HBDPInl bdp , HBDPInl bde
    lem-r-hbd-p (HBDPInr bd)
      with lem-r-hbd-p bd
    ... | bdp , bde = HBDPInr bdp , HBDPInr bde
    lem-r-hbd-p (HBDPPair bd1 bd2)
      with lem-r-hbd-p bd1 | lem-r-hbd-p bd2
    ... | bdp1 , bde1 | bdp2 , bde2 =
      HBDPPair bdp1 bdp2 , HBDPPair bde1 bde2
    lem-r-hbd-p HBDPWild = HBDPWild , HBDPWild
    lem-r-hbd-p (HBDPEHole (HUBRule ubp ube)) =
      HBDPEHole ubp , HBDPEHole ube
    lem-r-hbd-p (HBDPNEHole (HUBRule ubp ube) bd)
      with lem-r-hbd-p bd
    ... | bdp , bde =
      HBDPNEHole ubp bdp , HBDPNEHole ube bde

  mutual
    lem-p-hbd-inl : {e : ihexp} {p1 : pattrn} →
                    hole-binders-disjoint e (inl p1) →
                    hole-binders-disjoint e p1
    lem-p-hbd-inl HBDNum = HBDNum
    lem-p-hbd-inl HBDVar = HBDVar
    lem-p-hbd-inl (HBDLam bd) = HBDLam (lem-p-hbd-inl bd)
    lem-p-hbd-inl (HBDAp bd1 bd2) =
      HBDAp (lem-p-hbd-inl bd1) (lem-p-hbd-inl bd2)
    lem-p-hbd-inl (HBDInl bd) = HBDInl (lem-p-hbd-inl bd)
    lem-p-hbd-inl (HBDInr bd) = HBDInr (lem-p-hbd-inl bd)
    lem-p-hbd-inl (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-p-hbd-inl bd)
              (HBDZRules (lem-p-hbd-inl-rs bdpre)
                        (lem-p-hbd-inl-rs bdpost))
    lem-p-hbd-inl (HBDPair bd1 bd2) =
      HBDPair (lem-p-hbd-inl bd1) (lem-p-hbd-inl bd2)
    lem-p-hbd-inl (HBDFst bd) =  HBDFst (lem-p-hbd-inl bd)
    lem-p-hbd-inl (HBDSnd bd) = HBDSnd (lem-p-hbd-inl bd)
    lem-p-hbd-inl HBDEHole = HBDEHole
    lem-p-hbd-inl (HBDNEHole bd) =
      HBDNEHole (lem-p-hbd-inl bd)

    lem-p-hbd-inl-rs : {rs : rules} {p1 : pattrn} →
                       hole-binders-disjoint-rs rs (inl p1) →
                       hole-binders-disjoint-rs rs p1
    lem-p-hbd-inl-rs HBDNoRules = HBDNoRules
    lem-p-hbd-inl-rs (HBDRules bdr bdrs) =
      HBDRules (lem-p-hbd-inl-r bdr) (lem-p-hbd-inl-rs bdrs)

    lem-p-hbd-inl-r : {r : rule} {p1 : pattrn} →
                      hole-binders-disjoint-r r (inl p1) →
                      hole-binders-disjoint-r r p1
    lem-p-hbd-inl-r (HBDRule bdp bd) =
      HBDRule (lem-p-hbd-inl-p bdp) (lem-p-hbd-inl bd)

    lem-p-hbd-inl-p : {p : pattrn} {p1 : pattrn} →
                      hole-binders-disjoint-p p (inl p1) →
                      hole-binders-disjoint-p p p1
    lem-p-hbd-inl-p HBDPNum = HBDPNum
    lem-p-hbd-inl-p HBDPVar = HBDPVar
    lem-p-hbd-inl-p (HBDPInl bd) =
      HBDPInl (lem-p-hbd-inl-p bd)
    lem-p-hbd-inl-p (HBDPInr bd) =
      HBDPInr (lem-p-hbd-inl-p bd)
    lem-p-hbd-inl-p (HBDPPair bd1 bd2) =
      HBDPPair (lem-p-hbd-inl-p bd1)
        (lem-p-hbd-inl-p bd2)
    lem-p-hbd-inl-p HBDPWild = HBDPWild
    lem-p-hbd-inl-p (HBDPEHole (HUBPInl ub)) =
      HBDPEHole ub
    lem-p-hbd-inl-p (HBDPNEHole (HUBPInl ub) bd) =
      HBDPNEHole ub (lem-p-hbd-inl-p bd)

  mutual
    lem-p-hbd-inr : {e : ihexp} {p1 : pattrn} →
                    hole-binders-disjoint e (inr p1) →
                    hole-binders-disjoint e p1
    lem-p-hbd-inr HBDNum = HBDNum
    lem-p-hbd-inr HBDVar = HBDVar
    lem-p-hbd-inr (HBDLam bd) =
      HBDLam (lem-p-hbd-inr bd)
    lem-p-hbd-inr (HBDAp bd1 bd2) =
      HBDAp (lem-p-hbd-inr bd1) (lem-p-hbd-inr bd2)
    lem-p-hbd-inr (HBDInl bd) = HBDInl (lem-p-hbd-inr bd)
    lem-p-hbd-inr (HBDInr bd) = HBDInr (lem-p-hbd-inr bd)
    lem-p-hbd-inr (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-p-hbd-inr bd)
              (HBDZRules (lem-p-hbd-inr-rs bdpre)
                        (lem-p-hbd-inr-rs bdpost))
    lem-p-hbd-inr (HBDPair bd1 bd2) =
      HBDPair (lem-p-hbd-inr bd1) (lem-p-hbd-inr bd2)
    lem-p-hbd-inr (HBDFst bd) = HBDFst (lem-p-hbd-inr bd)
    lem-p-hbd-inr (HBDSnd bd) = HBDSnd (lem-p-hbd-inr bd)
    lem-p-hbd-inr HBDEHole = HBDEHole
    lem-p-hbd-inr (HBDNEHole bd) = HBDNEHole (lem-p-hbd-inr bd)

    lem-p-hbd-inr-rs : {rs : rules} {p1 : pattrn} →
                       hole-binders-disjoint-rs rs (inr p1) →
                       hole-binders-disjoint-rs rs p1
    lem-p-hbd-inr-rs HBDNoRules = HBDNoRules
    lem-p-hbd-inr-rs (HBDRules bdr bdrs) =
      HBDRules (lem-p-hbd-inr-r bdr) (lem-p-hbd-inr-rs bdrs)

    lem-p-hbd-inr-r : {r : rule} {p1 : pattrn} →
                      hole-binders-disjoint-r r (inr p1) →
                      hole-binders-disjoint-r r p1
    lem-p-hbd-inr-r (HBDRule bdp bd) =
      HBDRule (lem-p-hbd-inr-p bdp) (lem-p-hbd-inr bd)

    lem-p-hbd-inr-p : {p : pattrn} {p1 : pattrn} →
                      hole-binders-disjoint-p p (inr p1) →
                      hole-binders-disjoint-p p p1
    lem-p-hbd-inr-p HBDPNum = HBDPNum
    lem-p-hbd-inr-p HBDPVar = HBDPVar
    lem-p-hbd-inr-p (HBDPInl bd) =
      HBDPInl (lem-p-hbd-inr-p bd)
    lem-p-hbd-inr-p (HBDPInr bd) =
      HBDPInr (lem-p-hbd-inr-p bd)
    lem-p-hbd-inr-p (HBDPPair bd1 bd2) =
      HBDPPair (lem-p-hbd-inr-p bd1)
              (lem-p-hbd-inr-p bd2)
    lem-p-hbd-inr-p HBDPWild = HBDPWild
    lem-p-hbd-inr-p (HBDPEHole (HUBPInr ub)) =
      HBDPEHole ub
    lem-p-hbd-inr-p (HBDPNEHole (HUBPInr ub) bd) =
      HBDPNEHole ub (lem-p-hbd-inr-p bd)

  mutual
    lem-p-hbd-pair : {e : ihexp} {p1 p2 : pattrn} →
                     hole-binders-disjoint e ⟨ p1 , p2 ⟩ →
                     hole-binders-disjoint e p1 ×
                       hole-binders-disjoint e p2
    lem-p-hbd-pair HBDNum = HBDNum , HBDNum
    lem-p-hbd-pair HBDVar = HBDVar , HBDVar
    lem-p-hbd-pair (HBDLam bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDLam bd1 , HBDLam bd2
    lem-p-hbd-pair (HBDAp bd1 bd2)
      with lem-p-hbd-pair bd1 | lem-p-hbd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDAp bd1₁ bd2₁ , HBDAp bd1₂ bd2₂
    lem-p-hbd-pair (HBDInl bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDInl bd1 , HBDInl bd2
    lem-p-hbd-pair (HBDInr bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDInr bd1 , HBDInr bd2
    lem-p-hbd-pair (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-p-hbd-pair bd |
           lem-p-hbd-pair-rs bdpre |
           lem-p-hbd-pair-rs bdpost
    ... | bd1 , bd2
        | bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      HBDMatch bd1 (HBDZRules bdpre1 bdpost1) ,
      HBDMatch bd2 (HBDZRules bdpre2 bdpost2)
    lem-p-hbd-pair (HBDPair bd1 bd2)
      with lem-p-hbd-pair bd1 | lem-p-hbd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPair bd1₁ bd2₁ , HBDPair bd1₂ bd2₂
    lem-p-hbd-pair (HBDFst bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDFst bd1 , HBDFst bd2
    lem-p-hbd-pair (HBDSnd bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDSnd bd1 , HBDSnd bd2
    lem-p-hbd-pair HBDEHole = HBDEHole , HBDEHole
    lem-p-hbd-pair (HBDNEHole bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDNEHole bd1 , HBDNEHole bd2

    lem-p-hbd-pair-rs : {rs : rules} {p1 p2 : pattrn} →
                        hole-binders-disjoint-rs rs ⟨ p1 , p2 ⟩ →
                        hole-binders-disjoint-rs rs p1 ×
                          hole-binders-disjoint-rs rs p2
    lem-p-hbd-pair-rs HBDNoRules = HBDNoRules , HBDNoRules
    lem-p-hbd-pair-rs (HBDRules bdr bdrs)
      with lem-p-hbd-pair-r bdr |
           lem-p-hbd-pair-rs bdrs
    ... | bdr1 , bdr2 | bdrs1 , bdrs2 =
      HBDRules bdr1 bdrs1 , HBDRules bdr2 bdrs2

    lem-p-hbd-pair-r : {r : rule} {p1 p2 : pattrn} →
                       hole-binders-disjoint-r r ⟨ p1 , p2 ⟩ →
                       hole-binders-disjoint-r r p1 ×
                         hole-binders-disjoint-r r p2
    lem-p-hbd-pair-r (HBDRule bdp bd)
      with lem-p-hbd-pair-p bdp |
           lem-p-hbd-pair bd
    ... | bdp1 , bdp2 | bd1 , bd2 =
      HBDRule bdp1 bd1 , HBDRule bdp2 bd2

    lem-p-hbd-pair-p : {p : pattrn} {p1 p2 : pattrn} →
                       hole-binders-disjoint-p p ⟨ p1 , p2 ⟩ →
                       hole-binders-disjoint-p p p1 ×
                         hole-binders-disjoint-p p p2
    lem-p-hbd-pair-p HBDPNum = HBDPNum , HBDPNum
    lem-p-hbd-pair-p HBDPVar = HBDPVar , HBDPVar
    lem-p-hbd-pair-p (HBDPInl bd)
      with lem-p-hbd-pair-p bd
    ... | bd1 , bd2 = HBDPInl bd1 , HBDPInl bd2
    lem-p-hbd-pair-p (HBDPInr bd)
      with lem-p-hbd-pair-p bd
    ... | bd1 , bd2 = HBDPInr bd1 , HBDPInr bd2
    lem-p-hbd-pair-p (HBDPPair bd1 bd2)
      with lem-p-hbd-pair-p bd1 |
           lem-p-hbd-pair-p bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPPair bd1₁ bd2₁ , HBDPPair bd1₂ bd2₂
    lem-p-hbd-pair-p HBDPWild = HBDPWild , HBDPWild
    lem-p-hbd-pair-p (HBDPEHole (HUBPPair ub1 ub2)) =
      HBDPEHole ub1 , HBDPEHole ub2
    lem-p-hbd-pair-p (HBDPNEHole (HUBPPair ub1 ub2) bd)
      with lem-p-hbd-pair-p bd
    ... | bd1 , bd2 =
      HBDPNEHole ub1 bd1 , HBDPNEHole ub2 bd2

  mutual
    lem-p-hbd-ehole : {e : ihexp} {u : Nat} →
                    hole-binders-disjoint {T = pattrn} e ⦇-⦈[ u ] →
                    hole-unbound-in u e
    lem-p-hbd-ehole HBDNum = HUBNum
    lem-p-hbd-ehole HBDVar = HUBVar
    lem-p-hbd-ehole (HBDLam bd) =
      HUBLam (lem-p-hbd-ehole bd)
    lem-p-hbd-ehole (HBDAp bd1 bd2) =
      HUBAp (lem-p-hbd-ehole bd1) (lem-p-hbd-ehole bd2)
    lem-p-hbd-ehole (HBDInl bd) =
      HUBInl (lem-p-hbd-ehole bd)
    lem-p-hbd-ehole (HBDInr bd) =
      HUBInr (lem-p-hbd-ehole bd)
    lem-p-hbd-ehole (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HUBMatch (lem-p-hbd-ehole bd)
              (HUBZRules (lem-p-hbd-ehole-rs bdpre)
                        (lem-p-hbd-ehole-rs bdpost))
    lem-p-hbd-ehole (HBDPair bd1 bd2) =
      HUBPair (lem-p-hbd-ehole bd1) (lem-p-hbd-ehole bd2)
    lem-p-hbd-ehole (HBDFst bd) = HUBFst (lem-p-hbd-ehole bd)
    lem-p-hbd-ehole (HBDSnd bd) = HUBSnd (lem-p-hbd-ehole bd)
    lem-p-hbd-ehole HBDEHole = HUBEHole
    lem-p-hbd-ehole (HBDNEHole bd) =
      HUBNEHole (lem-p-hbd-ehole bd)

    lem-p-hbd-ehole-rs : {rs : rules} {w : Nat} →
                       hole-binders-disjoint-rs {T = pattrn} rs ⦇-⦈[ w ] →
                       hole-unbound-in w rs
    lem-p-hbd-ehole-rs HBDNoRules = HUBNoRules
    lem-p-hbd-ehole-rs (HBDRules bdr bdrs) =
      HUBRules (lem-p-hbd-ehole-r bdr) (lem-p-hbd-ehole-rs bdrs)

    lem-p-hbd-ehole-r : {r : rule} {w : Nat} →
                      hole-binders-disjoint-r {T = pattrn} r ⦇-⦈[ w ] →
                      hole-unbound-in w r
    lem-p-hbd-ehole-r (HBDRule bdp bd) =
      HUBRule (lem-p-hbd-ehole-p bdp) (lem-p-hbd-ehole bd)

    lem-p-hbd-ehole-p : {p : pattrn} {w : Nat} →
                      hole-binders-disjoint-p {T = pattrn} p ⦇-⦈[ w ] →
                      hole-unbound-in w p
    lem-p-hbd-ehole-p HBDPNum = HUBPNum
    lem-p-hbd-ehole-p HBDPVar = HUBPVar
    lem-p-hbd-ehole-p (HBDPInl bd) =
      HUBPInl (lem-p-hbd-ehole-p bd)
    lem-p-hbd-ehole-p (HBDPInr bd) =
      HUBPInr (lem-p-hbd-ehole-p bd)
    lem-p-hbd-ehole-p (HBDPPair bd1 bd2) =
      HUBPPair (lem-p-hbd-ehole-p bd1)
              (lem-p-hbd-ehole-p bd2)
    lem-p-hbd-ehole-p HBDPWild = HUBPWild
    lem-p-hbd-ehole-p (HBDPEHole (HUBPEHole u≠w)) =
      HUBPEHole (flip u≠w)
    lem-p-hbd-ehole-p (HBDPNEHole (HUBPEHole u≠w) bd) =
      HUBPNEHole (flip u≠w) (lem-p-hbd-ehole-p bd)

  mutual
    lem-p-hbd-nehole : {e : ihexp}
                      {p1 : pattrn} {w : Nat} {τ : htyp} →
                      hole-binders-disjoint e ⦇⌜ p1 ⌟⦈[ w , τ ] →
                      hole-unbound-in w e ×
                        hole-binders-disjoint e p1
    lem-p-hbd-nehole HBDNum = HUBNum , HBDNum
    lem-p-hbd-nehole HBDVar = HUBVar , HBDVar
    lem-p-hbd-nehole (HBDLam hbd)
      with lem-p-hbd-nehole hbd
    ... | ub , hbd' = HUBLam ub , HBDLam hbd'
    lem-p-hbd-nehole (HBDAp hbd1 hbd2)
      with lem-p-hbd-nehole hbd1 | lem-p-hbd-nehole hbd2
    ... | ub1 , hbd1' | ub2 , hbd2' =
      HUBAp ub1 ub2 , HBDAp hbd1' hbd2'
    lem-p-hbd-nehole (HBDInl hbd)
      with lem-p-hbd-nehole hbd
    ... | ub , hbd' = HUBInl ub , HBDInl hbd'
    lem-p-hbd-nehole (HBDInr hbd)
      with lem-p-hbd-nehole hbd
    ... | ub , hbd' = HUBInr ub , HBDInr hbd'
    lem-p-hbd-nehole (HBDMatch hbd (HBDZRules hbdpre hbdpost))
      with lem-p-hbd-nehole hbd |
           lem-p-hbd-nehole-rs hbdpre |
           lem-p-hbd-nehole-rs hbdpost
    ... | ub , hbd'
        | ubpre , hbdpre'
        | ubdpost , hbdpost' =
      HUBMatch ub (HUBZRules ubpre ubdpost) ,
      HBDMatch hbd' (HBDZRules hbdpre' hbdpost')
    lem-p-hbd-nehole (HBDPair hbd1 hbd2)
      with lem-p-hbd-nehole hbd1 | lem-p-hbd-nehole hbd2
    ... | ub1 , hbd1' | ub2 , hbd2' =
      HUBPair ub1 ub2 , HBDPair hbd1' hbd2'
    lem-p-hbd-nehole (HBDFst hbd)
      with lem-p-hbd-nehole hbd
    ... | ub , hbd' = HUBFst ub , HBDFst hbd'
    lem-p-hbd-nehole (HBDSnd hbd)
      with lem-p-hbd-nehole hbd
    ... | ub , hbd' = HUBSnd ub , HBDSnd hbd'
    lem-p-hbd-nehole HBDEHole = HUBEHole , HBDEHole
    lem-p-hbd-nehole (HBDNEHole hbd)
      with lem-p-hbd-nehole hbd
    ... | ub , hbd' = HUBNEHole ub , HBDNEHole hbd'

    lem-p-hbd-nehole-rs : {rs : rules}
                          {p1 : pattrn} {w : Nat} {τ : htyp} →
                          hole-binders-disjoint-rs rs ⦇⌜ p1 ⌟⦈[ w , τ ] →
                          hole-unbound-in-rs w rs ×
                            hole-binders-disjoint-rs rs p1
    lem-p-hbd-nehole-rs HBDNoRules = HUBNoRules , HBDNoRules
    lem-p-hbd-nehole-rs (HBDRules bdr bdrs)
      with lem-p-hbd-nehole-r bdr | lem-p-hbd-nehole-rs bdrs
    ... | ubr , bdr' | ubrs , bdrs' =
      HUBRules ubr ubrs , HBDRules bdr' bdrs'

    lem-p-hbd-nehole-r : {r : rule}
                         {p1 : pattrn} {w : Nat} {τ : htyp} →
                         hole-binders-disjoint-r r ⦇⌜ p1 ⌟⦈[ w , τ ] →
                         hole-unbound-in-r w r ×
                           hole-binders-disjoint-r r p1
    lem-p-hbd-nehole-r (HBDRule bdp bde)
      with lem-p-hbd-nehole-p bdp | lem-p-hbd-nehole bde
    ... | ubp , bdp' | ube , bde' =
      HUBRule ubp ube , HBDRule bdp' bde'

    lem-p-hbd-nehole-p : {p : pattrn}
                         {p1 : pattrn} {w : Nat} {τ : htyp} →
                         hole-binders-disjoint-p p ⦇⌜ p1 ⌟⦈[ w , τ ] →
                         hole-unbound-in w p ×
                           hole-binders-disjoint-p p p1
    lem-p-hbd-nehole-p HBDPNum = HUBPNum , HBDPNum
    lem-p-hbd-nehole-p HBDPVar = HUBPVar , HBDPVar
    lem-p-hbd-nehole-p (HBDPInl bd)
      with lem-p-hbd-nehole-p bd
    ... | ub , bd' = HUBPInl ub , HBDPInl bd'
    lem-p-hbd-nehole-p (HBDPInr bd)
      with lem-p-hbd-nehole-p bd
    ... | ub , bd' = HUBPInr ub , HBDPInr bd'
    lem-p-hbd-nehole-p (HBDPPair bd1 bd2)
      with lem-p-hbd-nehole-p bd1 | lem-p-hbd-nehole-p bd2
    ... | ub1 , bd1' | ub2 , bd2' =
      HUBPPair ub1 ub2 , HBDPPair bd1' bd2'
    lem-p-hbd-nehole-p HBDPWild = HUBPWild , HBDPWild
    lem-p-hbd-nehole-p (HBDPEHole (HUBPNEHole u≠w ub)) =
      HUBPEHole (flip u≠w) , HBDPEHole ub
    lem-p-hbd-nehole-p (HBDPNEHole (HUBPNEHole u≠w ub) bd)
      with lem-p-hbd-nehole-p bd
    ... | ub' , bd' =
      HUBPNEHole (flip u≠w) ub' , HBDPNEHole ub bd'
    
  mutual
    hole-binders-disjoint-sym : {e1 e2 : ihexp} →
                                hole-binders-disjoint e1 e2 →
                                hole-binders-disjoint e2 e1
    hole-binders-disjoint-sym {e2 = N n} bd = HBDNum
    hole-binders-disjoint-sym {e2 = X x} bd = HBDVar
    hole-binders-disjoint-sym {e2 = ·λ x ·[ τ ] e2} bd = 
      HBDLam (hole-binders-disjoint-sym (lem-hbd-lam bd))
    hole-binders-disjoint-sym {e2 = e2₁ ∘ e2₂} bd
      with lem-hbd-ap bd
    ... | bd1 , bd2 =
      HBDAp (hole-binders-disjoint-sym bd1)
           (hole-binders-disjoint-sym bd2)
    hole-binders-disjoint-sym {e2 = inl τ e2} bd =
      HBDInl (hole-binders-disjoint-sym (lem-hbd-inl bd))
    hole-binders-disjoint-sym {e2 = inr τ e2} bd =
      HBDInr (hole-binders-disjoint-sym (lem-hbd-inr bd))
    hole-binders-disjoint-sym
      {e2 = match e2 (rs-pre / r / rs-post)} bd
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDMatch (hole-binders-disjoint-sym bd')
              (HBDZRules (rs-hole-binders-disjoint-sym bdpre)
                        (HBDRules (r-hole-binders-disjoint-sym bdr)
                                 (rs-hole-binders-disjoint-sym bdpost)))
                        
    hole-binders-disjoint-sym {e2 = ⟨ e2₁ , e2₂ ⟩} bd
      with lem-hbd-pair bd
    ... | bd1 , bd2 =
      HBDPair (hole-binders-disjoint-sym bd1)
             (hole-binders-disjoint-sym bd2)
    hole-binders-disjoint-sym {e2 = fst e2} bd =
      HBDFst (hole-binders-disjoint-sym (lem-hbd-fst bd))
    hole-binders-disjoint-sym {e2 = snd e2} bd =
      HBDSnd (hole-binders-disjoint-sym (lem-hbd-snd bd))
    hole-binders-disjoint-sym {e2 = ⦇-⦈[ u ]} bd = HBDEHole
    hole-binders-disjoint-sym {e2 = ⦇⌜ e2 ⌟⦈[ u ]} bd =
      HBDNEHole (hole-binders-disjoint-sym (lem-hbd-nehole bd))

    rs-hole-binders-disjoint-sym : {e : ihexp} {rs : rules} →
                                   hole-binders-disjoint e rs →
                                   hole-binders-disjoint-rs rs e
    rs-hole-binders-disjoint-sym {rs = nil} bd = HBDNoRules
    rs-hole-binders-disjoint-sym {rs = r / rs} bd
      with lem-rs-hbd bd
    ... | rbd , rsbd =
      HBDRules (r-hole-binders-disjoint-sym rbd)
              (rs-hole-binders-disjoint-sym rsbd)

    r-hole-binders-disjoint-sym : {e : ihexp} {r : rule} →
                                  hole-binders-disjoint e r →
                                  hole-binders-disjoint-r r e
    r-hole-binders-disjoint-sym {r = pr => er} bd
      with lem-r-hbd bd
    ... | bdp , bde =
      HBDRule (p-hole-binders-disjoint-sym bdp)
              (hole-binders-disjoint-sym bde)
    
    p-hole-binders-disjoint-sym : {e : ihexp} {p : pattrn} →
                                  hole-binders-disjoint e p →
                                  hole-binders-disjoint-p p e
    p-hole-binders-disjoint-sym {p = N n} bd = HBDPNum
    p-hole-binders-disjoint-sym {p = X x} bd = HBDPVar
    p-hole-binders-disjoint-sym {p = inl p} bd =
      HBDPInl (p-hole-binders-disjoint-sym (lem-p-hbd-inl bd))
    p-hole-binders-disjoint-sym {p = inr p} bd =
      HBDPInr (p-hole-binders-disjoint-sym (lem-p-hbd-inr bd))
    p-hole-binders-disjoint-sym {p = ⟨ p1 , p2 ⟩} bd
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = 
      HBDPPair (p-hole-binders-disjoint-sym bd1)
              (p-hole-binders-disjoint-sym bd2)
    p-hole-binders-disjoint-sym {p = wild} bd = HBDPWild
    p-hole-binders-disjoint-sym {p = ⦇-⦈[ w ]} bd =
      HBDPEHole (lem-p-hbd-ehole bd)
    p-hole-binders-disjoint-sym {p = ⦇⌜ p ⌟⦈[ w , τ ]} bd
      with lem-p-hbd-nehole bd
    ... | ub , bd' =
      HBDPNEHole ub (p-hole-binders-disjoint-sym bd')
