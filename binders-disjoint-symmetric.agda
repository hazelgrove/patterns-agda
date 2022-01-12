open import Nat
open import Prelude
open import contexts
open import core
open import binders-disjointness
open import freshness
open import lemmas-contexts

module binders-disjoint-symmetric where
  -- these lemmas build up to proving that the
  -- binders-disjoint judgement is symmetric.
  -- all of them are entirely mechanical, but horribly tedious
  mutual
    lem-bd-lam : {e : ihexp} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                 binders-disjoint e (·λ x ·[ τ1 ] e1) →
                 unbound-in x e ×
                   binders-disjoint e e1
    lem-bd-lam BDNum = UBNum , BDNum 
    lem-bd-lam BDVar = UBVar , BDVar
    lem-bd-lam (BDLam (UBLam x≠y ub) bd)
      with lem-bd-lam bd
    ... | ub' , bd' =
      UBLam (flip x≠y) ub' , BDLam ub bd'
    lem-bd-lam (BDAp bd1 bd2)
      with lem-bd-lam bd1 | lem-bd-lam bd2
    ... | ub1 , bd1' | ub2 , bd2' =
      UBAp ub1 ub2 , BDAp bd1' bd2'
    lem-bd-lam (BDInl bd)
      with lem-bd-lam bd
    ... | ub , bd' = UBInl ub , BDInl bd' 
    lem-bd-lam (BDInr bd)
      with lem-bd-lam bd
    ... | ub , bd' = UBInr ub , BDInr bd'
    lem-bd-lam (BDMatch bd (BDZRules bdpre bdpost))
      with lem-bd-lam bd |
           lem-bd-lam-rs bdpre |
           lem-bd-lam-rs bdpost
    ... | ub , bd'
        | ubpre , bdpre' 
        | ubpost , bdpost'  = 
      UBMatch ub (UBZRules ubpre ubpost) ,
        BDMatch bd' (BDZRules bdpre' bdpost')
    lem-bd-lam (BDPair bd1 bd2)
      with lem-bd-lam bd1 | lem-bd-lam bd2
    ... | ub1 , bd1'  | ub2 , bd2' =
      UBPair ub1 ub2 , BDPair bd1' bd2'
    lem-bd-lam (BDFst bd)
      with lem-bd-lam bd
    ... | ub , bd' =  UBFst ub , BDFst bd'
    lem-bd-lam (BDSnd bd)
      with lem-bd-lam bd
    ... | ub , bd' = UBSnd ub , BDSnd bd'
    lem-bd-lam BDEHole = UBEHole , BDEHole
    lem-bd-lam (BDNEHole bd)
      with lem-bd-lam bd
    ... | ub , bd' = UBNEHole ub , BDNEHole bd' 

    lem-bd-lam-rs : {rs : rules} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                    binders-disjoint-rs rs (·λ x ·[ τ1 ] e1) →
                    unbound-in-rs x rs ×
                      binders-disjoint-rs rs e1
                      
    lem-bd-lam-rs BDNoRules = UBNoRules , BDNoRules
    lem-bd-lam-rs (BDRules bdr bdrs)
      with lem-bd-lam-r bdr | lem-bd-lam-rs bdrs
    ... | ubr , bdr' | ubrs , bdrs' =
      UBRules ubr ubrs , BDRules bdr' bdrs'

    lem-bd-lam-r : {r : rule} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                   binders-disjoint-r r (·λ x ·[ τ1 ] e1) →
                   unbound-in-r x r ×
                     binders-disjoint-r r e1
    lem-bd-lam-r (BDRule bdp bd)
      with lem-bd-lam-p bdp | lem-bd-lam bd
    ... | ubp , bdp' | ub , bd' =
      UBRule ubp ub , BDRule bdp' bd'

    lem-bd-lam-p : {p : pattrn} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                   binders-disjoint-p p (·λ x ·[ τ1 ] e1) →
                   unbound-in-p x p ×
                     binders-disjoint-p p e1
    lem-bd-lam-p BDPNum = UBPNum , BDPNum 
    lem-bd-lam-p (BDPVar (UBLam x≠y ub)) =
      UBPVar (flip x≠y) , BDPVar ub
    lem-bd-lam-p (BDPInl bd)
      with lem-bd-lam-p bd
    ... | ub , bd' = UBPInl ub , BDPInl bd'
    lem-bd-lam-p (BDPInr bd)
      with lem-bd-lam-p bd
    ... | ub , bd' = UBPInr ub , BDPInr bd'
    lem-bd-lam-p (BDPPair bd1 bd2)
      with lem-bd-lam-p bd1 | lem-bd-lam-p bd2
    ... | ub1 , bd1' | ub2 , bd2' =
      UBPPair ub1 ub2 , BDPPair bd1' bd2'
    lem-bd-lam-p BDPWild = UBPWild , BDPWild
    lem-bd-lam-p BDPEHole = UBPEHole , BDPEHole
    lem-bd-lam-p (BDPNEHole bd)
      with lem-bd-lam-p bd
    ... | ub , bd' = UBPNEHole ub , BDPNEHole bd'
    
  mutual
    lem-bd-ap : {e : ihexp} {e1 e2 : ihexp} →
                binders-disjoint e (e1 ∘ e2) →
                binders-disjoint e e1 ×
                  binders-disjoint e e2
    lem-bd-ap BDNum = BDNum , BDNum
    lem-bd-ap BDVar = BDVar , BDVar
    lem-bd-ap (BDLam (UBAp ub1 ub2) bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDLam ub1 bd1 , BDLam ub2 bd2
    lem-bd-ap (BDAp bd1 bd2)
      with lem-bd-ap bd1 | lem-bd-ap bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDAp bd1₁ bd2₁ , BDAp bd1₂ bd2₂
    lem-bd-ap (BDInl bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDInl bd1 , BDInl bd2
    lem-bd-ap (BDInr bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDInr bd1 , BDInr bd2
    lem-bd-ap (BDMatch bd (BDZRules pret postt))
      with lem-bd-ap bd |
           lem-bd-ap-rs pret |
           lem-bd-ap-rs postt
    ... | bd1 , bd2 
        |  bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      BDMatch bd1 (BDZRules bdpre1 bdpost1) ,
      BDMatch bd2 (BDZRules bdpre2 bdpost2)
    lem-bd-ap (BDPair bd1 bd2)
      with lem-bd-ap bd1 | lem-bd-ap bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDPair bd1₁ bd2₁ , BDPair bd1₂ bd2₂
    lem-bd-ap (BDFst bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDFst bd1 , BDFst bd2
    lem-bd-ap (BDSnd bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDSnd bd1 , BDSnd bd2
    lem-bd-ap BDEHole = BDEHole , BDEHole
    lem-bd-ap (BDNEHole bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDNEHole bd1 , BDNEHole bd2

    lem-bd-ap-rs : {rs : rules} {e1 e2 : ihexp} →
                   binders-disjoint-rs rs (e1 ∘ e2) →
                   binders-disjoint-rs rs e1 ×
                     binders-disjoint-rs rs e2
    lem-bd-ap-rs BDNoRules = BDNoRules , BDNoRules
    lem-bd-ap-rs (BDRules bdr bdrs)
      with lem-bd-ap-r bdr | lem-bd-ap-rs bdrs
    ... | bdr1 , bdr2 | bd1 , bd2 =
      BDRules bdr1 bd1 , BDRules bdr2 bd2
      
    lem-bd-ap-r : {r : rule} {e1 e2 : ihexp} →
                  binders-disjoint-r r (e1 ∘ e2) →
                  binders-disjoint-r r e1 ×
                    binders-disjoint-r r e2
    lem-bd-ap-r (BDRule pt bd)
      with lem-bd-ap-p pt | lem-bd-ap bd
    ... | pt1 , pt2 | bd1 , bd2 =
      BDRule pt1 bd1 , BDRule pt2 bd2

    lem-bd-ap-p : {p : pattrn} {e1 e2 : ihexp} →
                  binders-disjoint-p p (e1 ∘ e2) →
                  binders-disjoint-p p e1 ×
                    binders-disjoint-p p e2
    lem-bd-ap-p BDPNum = BDPNum , BDPNum
    lem-bd-ap-p (BDPVar (UBAp ub1 ub2)) =
      BDPVar ub1 , BDPVar ub2
    lem-bd-ap-p (BDPInl bd)
      with lem-bd-ap-p bd
    ... | bd1 , bd2 = BDPInl bd1 , BDPInl bd2
    lem-bd-ap-p (BDPInr bd)
      with lem-bd-ap-p bd
    ... | bd1 , bd2 = BDPInr bd1 , BDPInr bd2
    lem-bd-ap-p (BDPPair bd1 bd2)
      with lem-bd-ap-p bd1 | lem-bd-ap-p bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDPPair bd1₁ bd2₁ , BDPPair bd1₂ bd2₂
    lem-bd-ap-p BDPWild = BDPWild , BDPWild
    lem-bd-ap-p BDPEHole = BDPEHole , BDPEHole
    lem-bd-ap-p (BDPNEHole bd)
      with lem-bd-ap-p bd
    ... | bd1 , bd2 = BDPNEHole bd1 , BDPNEHole bd2

  mutual
    lem-bd-inl : {e : ihexp} {τ : htyp} {e1 : ihexp} →
                 binders-disjoint e (inl τ e1) →
                 binders-disjoint e e1
    lem-bd-inl BDNum = BDNum
    lem-bd-inl BDVar = BDVar
    lem-bd-inl (BDLam (UBInl ub) bd) =
      BDLam ub (lem-bd-inl bd)
    lem-bd-inl (BDAp bd1 bd2) =
      BDAp (lem-bd-inl bd1) (lem-bd-inl bd2)
    lem-bd-inl (BDInl bd) = BDInl (lem-bd-inl bd)
    lem-bd-inl (BDInr bd) = BDInr (lem-bd-inl bd)
    lem-bd-inl (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-bd-inl bd)
              (BDZRules (lem-bd-inl-rs bdpre)
                        (lem-bd-inl-rs bdpost))
    lem-bd-inl (BDPair bd1 bd2) =
      BDPair (lem-bd-inl bd1) (lem-bd-inl bd2)
    lem-bd-inl (BDFst bd) = BDFst (lem-bd-inl bd)
    lem-bd-inl (BDSnd bd) = BDSnd (lem-bd-inl bd)
    lem-bd-inl BDEHole = BDEHole
    lem-bd-inl (BDNEHole bd) = BDNEHole (lem-bd-inl bd)

    lem-bd-inl-rs : {rs : rules} {τ : htyp} {e1 : ihexp} →
                    binders-disjoint-rs rs (inl τ e1) →
                    binders-disjoint-rs rs e1
    lem-bd-inl-rs BDNoRules = BDNoRules
    lem-bd-inl-rs (BDRules bdr bdrs) =
      BDRules (lem-bd-inl-r bdr) (lem-bd-inl-rs bdrs)

    lem-bd-inl-r : {r : rule} {τ : htyp} {e1 : ihexp} →
                   binders-disjoint-r r (inl τ e1) →
                   binders-disjoint-r r e1
    lem-bd-inl-r (BDRule bdp bd) =
      BDRule (lem-bd-inl-p bdp) (lem-bd-inl bd)

    lem-bd-inl-p : {p : pattrn} {τ : htyp} {e1 : ihexp} →
                   binders-disjoint-p p (inl τ e1) →
                   binders-disjoint-p p e1
    lem-bd-inl-p BDPNum = BDPNum
    lem-bd-inl-p (BDPVar (UBInl ub)) = BDPVar ub
    lem-bd-inl-p (BDPInl bd) = BDPInl (lem-bd-inl-p bd)
    lem-bd-inl-p (BDPInr bd) = BDPInr (lem-bd-inl-p bd)
    lem-bd-inl-p (BDPPair bd1 bd2) =
      BDPPair (lem-bd-inl-p bd1) (lem-bd-inl-p bd2)
    lem-bd-inl-p BDPWild = BDPWild
    lem-bd-inl-p BDPEHole = BDPEHole
    lem-bd-inl-p (BDPNEHole bd) =
      BDPNEHole (lem-bd-inl-p bd)
    
  mutual
    lem-bd-inr : {e : ihexp} {τ : htyp} {e1 : ihexp} →
                 binders-disjoint e (inr τ e1) →
                 binders-disjoint e e1
    lem-bd-inr BDNum = BDNum
    lem-bd-inr BDVar = BDVar
    lem-bd-inr (BDLam (UBInr ub) bd) =
      BDLam ub (lem-bd-inr bd)
    lem-bd-inr (BDAp bd1 bd2) =
      BDAp (lem-bd-inr bd1) (lem-bd-inr bd2)
    lem-bd-inr (BDInl bd) = BDInl (lem-bd-inr bd)
    lem-bd-inr (BDInr bd) = BDInr (lem-bd-inr bd)
    lem-bd-inr (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-bd-inr bd)
              (BDZRules (lem-bd-inr-rs bdpre)
                        (lem-bd-inr-rs bdpost))
    lem-bd-inr (BDPair bd1 bd2) =
      BDPair (lem-bd-inr bd1) (lem-bd-inr bd2)
    lem-bd-inr (BDFst bd) = BDFst (lem-bd-inr bd)
    lem-bd-inr (BDSnd bd) = BDSnd (lem-bd-inr bd)
    lem-bd-inr BDEHole = BDEHole
    lem-bd-inr (BDNEHole bd) = BDNEHole (lem-bd-inr bd)

    lem-bd-inr-rs : {rs : rules} {τ : htyp} {e1 : ihexp} →
                    binders-disjoint-rs rs (inr τ e1) →
                    binders-disjoint-rs rs e1
    lem-bd-inr-rs BDNoRules = BDNoRules
    lem-bd-inr-rs (BDRules bdr bdrs) =
      BDRules (lem-bd-inr-r bdr) (lem-bd-inr-rs bdrs)

    lem-bd-inr-r : {r : rule} {τ : htyp} {e1 : ihexp}  →
                   binders-disjoint-r r (inr τ e1) →
                   binders-disjoint-r r e1
    lem-bd-inr-r (BDRule bdp bd) =
      BDRule (lem-bd-inr-p bdp) (lem-bd-inr bd)

    lem-bd-inr-p : {p : pattrn} {τ : htyp} {e1 : ihexp} →
                   binders-disjoint-p p (inr τ e1) →
                   binders-disjoint-p p e1
    lem-bd-inr-p BDPNum = BDPNum
    lem-bd-inr-p (BDPVar (UBInr ub)) = BDPVar ub
    lem-bd-inr-p (BDPInl bd) = BDPInl (lem-bd-inr-p bd)
    lem-bd-inr-p (BDPInr bd) = BDPInr (lem-bd-inr-p bd)
    lem-bd-inr-p (BDPPair bd1 bd2) =
      BDPPair (lem-bd-inr-p bd1) (lem-bd-inr-p bd2)
    lem-bd-inr-p BDPWild = BDPWild
    lem-bd-inr-p BDPEHole = BDPEHole
    lem-bd-inr-p (BDPNEHole bd) =
      BDPNEHole (lem-bd-inr-p bd)
    
  mutual
    lem-bd-match : {e : ihexp} {e1 : ihexp}
                   {rs-pre : rules} {r : rule} {rs-post : rules} →
                   binders-disjoint e
                     (match e1 (rs-pre / r / rs-post)) →
                   binders-disjoint e e1 ×
                     binders-disjoint e rs-pre ×
                       binders-disjoint e r ×
                         binders-disjoint e rs-post
    lem-bd-match BDNum = BDNum , BDNum , BDNum , BDNum
    lem-bd-match BDVar = BDVar , BDVar , BDVar , BDVar
    lem-bd-match (BDLam (UBMatch ub
                                 (UBZRules ubpre (UBRules ubr ubpost)))
                 bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDLam ub bd' ,
      BDLam ubpre bdpre ,
      BDLam ubr bdr ,
      BDLam ubpost bdpost
    lem-bd-match (BDAp bd1 bd2)
      with lem-bd-match bd1 | lem-bd-match bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1 |
          bd2' , bdpre2 , bdr2 , bdpost2 =
      BDAp bd1' bd2' ,
      BDAp bdpre1 bdpre2 ,
      BDAp bdr1 bdr2 ,
      BDAp bdpost1 bdpost2 
    lem-bd-match (BDInl bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDInl bd' , BDInl bdpre , BDInl bdr , BDInl bdpost
    lem-bd-match (BDInr bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDInr bd' , BDInr bdpre , BDInr bdr , BDInr bdpost
    lem-bd-match (BDMatch bd (BDZRules bdpre bdpost))
      with lem-bd-match bd |
           lem-bd-match-rs bdpre |
           lem-bd-match-rs bdpost
    ... | bd' , bdpre , bdr , bdpost
        | bdpre' , bdprepre , bdprer , bdprepost
        | bdpost' , bdpostpre , bdpostr , bdpostpost =
      BDMatch bd' (BDZRules bdpre' bdpost') ,
      BDMatch bdpre (BDZRules bdprepre bdpostpre) ,
      BDMatch bdr (BDZRules bdprer bdpostr) ,
      BDMatch bdpost (BDZRules bdprepost bdpostpost)
    lem-bd-match (BDPair bd1 bd2)
      with lem-bd-match bd1 | lem-bd-match bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1 |
          bd2' , bdpre2 , bdr2 , bdpost2 =
      BDPair bd1' bd2' ,
      BDPair bdpre1 bdpre2 ,
      BDPair bdr1 bdr2 ,
      BDPair bdpost1 bdpost2 
    lem-bd-match (BDFst bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDFst bd' , BDFst bdpre , BDFst bdr , BDFst bdpost
    lem-bd-match (BDSnd bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDSnd bd' , BDSnd bdpre , BDSnd bdr , BDSnd bdpost
    lem-bd-match BDEHole =
      BDEHole , BDEHole , BDEHole , BDEHole
    lem-bd-match (BDNEHole bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDNEHole bd' , BDNEHole bdpre ,
      BDNEHole bdr , BDNEHole bdpost

    lem-bd-match-rs : {rs : rules} {e1 : ihexp}
                      {rs-pre : rules} {r : rule} {rs-post : rules} →
                      binders-disjoint-rs rs
                        (match e1 (rs-pre / r / rs-post)) →
                      binders-disjoint-rs rs e1 ×
                        binders-disjoint-rs rs rs-pre ×
                          binders-disjoint-rs rs r ×
                            binders-disjoint-rs rs rs-post
    lem-bd-match-rs BDNoRules =
      BDNoRules , BDNoRules , BDNoRules , BDNoRules 
    lem-bd-match-rs (BDRules bdr bdrs)
      with lem-bd-match-r bdr | lem-bd-match-rs bdrs
    ... | bdr' , bdrpre , bdrr , bdrpost
        | bdrs' , bdrspre , bdrsr , bdrspost =
      BDRules bdr' bdrs' ,
      BDRules bdrpre bdrspre ,
      BDRules bdrr bdrsr ,
      BDRules bdrpost bdrspost

    lem-bd-match-r : {r : rule} {e1 : ihexp}
                     {rs-pre : rules} {r1 : rule} {rs-post : rules} →
                     binders-disjoint-r r
                       (match e1 (rs-pre / r1 / rs-post)) →
                     binders-disjoint-r r e1 ×
                       binders-disjoint-r r rs-pre ×
                         binders-disjoint-r r r1 ×
                           binders-disjoint-r r rs-post
    lem-bd-match-r (BDRule bdp bd)
      with lem-bd-match-p bdp | lem-bd-match bd
    ... | bdp' , bdppre , bdpr , bdppost
        | bd' , bdpre , bdr , bdpost =
      BDRule bdp' bd' ,
      BDRule bdppre bdpre ,
      BDRule bdpr bdr ,
      BDRule bdppost bdpost
  
    lem-bd-match-p : {p : pattrn} {e1 : ihexp}
                     {rs-pre : rules} {r1 : rule} {rs-post : rules} →
                     binders-disjoint-p p
                       (match e1 (rs-pre / r1 / rs-post)) →
                     binders-disjoint-p p e1 ×
                       binders-disjoint-p p rs-pre ×
                         binders-disjoint-p p r1 ×
                           binders-disjoint-p p rs-post
    lem-bd-match-p BDPNum = BDPNum , BDPNum , BDPNum , BDPNum
    lem-bd-match-p (BDPVar (UBMatch ub
                                    (UBZRules ubpre
                                              (UBRules ubr ubpost)))) =
      BDPVar ub , BDPVar ubpre , BDPVar ubr , BDPVar ubpost
    lem-bd-match-p (BDPInl bd)
      with lem-bd-match-p bd
    ... | bd' , bdpre , bdr , bdpost =
      BDPInl bd' , BDPInl bdpre , BDPInl bdr , BDPInl bdpost
    lem-bd-match-p (BDPInr bd)
      with lem-bd-match-p bd
    ... | bd' , bdpre , bdr , bdpost =
      BDPInr bd' , BDPInr bdpre , BDPInr bdr , BDPInr bdpost
    lem-bd-match-p (BDPPair bd1 bd2)
      with lem-bd-match-p bd1 | lem-bd-match-p bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1
        | bd2' , bdpre2 , bdr2 , bdpost2 =
      BDPPair bd1' bd2' ,
      BDPPair bdpre1 bdpre2 ,
      BDPPair bdr1 bdr2 ,
      BDPPair bdpost1 bdpost2
    lem-bd-match-p BDPWild =
      BDPWild , BDPWild , BDPWild , BDPWild
    lem-bd-match-p BDPEHole =
      BDPEHole , BDPEHole , BDPEHole , BDPEHole
    lem-bd-match-p (BDPNEHole bd)
      with lem-bd-match-p bd
    ... | bd' , bdpre , bdr , bdpost =
      BDPNEHole bd' , BDPNEHole bdpre , BDPNEHole bdr , BDPNEHole bdpost
    
  mutual
    lem-bd-pair : {e : ihexp} {e1 e2 : ihexp} →
                  binders-disjoint e ⟨ e1 , e2 ⟩ →
                  (binders-disjoint e e1) ×
                    (binders-disjoint e e2)
    lem-bd-pair BDNum = BDNum , BDNum
    lem-bd-pair BDVar = BDVar , BDVar
    lem-bd-pair (BDLam (UBPair ub1 ub2) bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDLam ub1 bd1 , BDLam ub2 bd2
    lem-bd-pair (BDAp bd1 bd2)
      with lem-bd-pair bd1 | lem-bd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDAp bd1₁ bd2₁ , BDAp bd1₂ bd2₂
    lem-bd-pair (BDInl bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDInl bd1 , BDInl bd2
    lem-bd-pair (BDInr bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDInr bd1 , BDInr bd2
    lem-bd-pair (BDMatch bd (BDZRules bdpre bdpost))
      with lem-bd-pair bd |
           lem-bd-pair-rs bdpre |
           lem-bd-pair-rs bdpost
    ... | bd1 , bd2
        | bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      BDMatch bd1 (BDZRules bdpre1 bdpost1) ,
      BDMatch bd2 (BDZRules bdpre2 bdpost2)
    lem-bd-pair (BDPair bd1 bd2)
      with lem-bd-pair bd1 | lem-bd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDPair bd1₁ bd2₁ , BDPair bd1₂ bd2₂
    lem-bd-pair (BDFst bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDFst bd1 , BDFst bd2
    lem-bd-pair (BDSnd bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDSnd bd1 , BDSnd bd2
    lem-bd-pair BDEHole = BDEHole , BDEHole
    lem-bd-pair (BDNEHole bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDNEHole bd1 , BDNEHole bd2

    lem-bd-pair-rs : {rs : rules} {e1 e2 : ihexp} →
                     binders-disjoint-rs rs ⟨ e1 , e2 ⟩ →
                     (binders-disjoint-rs rs e1) ×
                       (binders-disjoint-rs rs e2)
    lem-bd-pair-rs BDNoRules = BDNoRules , BDNoRules
    lem-bd-pair-rs (BDRules bdr bdrs)
      with lem-bd-pair-r bdr | lem-bd-pair-rs bdrs
    ... | bdr' , ubr | bdrs' , ubrs =
      BDRules bdr' bdrs' , BDRules ubr ubrs

    lem-bd-pair-r : {r : rule} {e1 e2 : ihexp} →
                    binders-disjoint-r r ⟨ e1 , e2 ⟩ →
                    (binders-disjoint-r r e1) ×
                      (binders-disjoint-r r e2)
    lem-bd-pair-r (BDRule bdp bd)
      with lem-bd-pair-p bdp | lem-bd-pair bd
    ... | bdp' , ubp | bd' , ub =
      BDRule bdp' bd' , BDRule ubp ub

    lem-bd-pair-p : {p : pattrn} {e1 e2 : ihexp} →
                    binders-disjoint-p p ⟨ e1 , e2 ⟩ →
                    (binders-disjoint-p p e1) ×
                      (binders-disjoint-p p e2)
    lem-bd-pair-p BDPNum = BDPNum , BDPNum
    lem-bd-pair-p (BDPVar (UBPair ub1 ub2)) =
      BDPVar ub1 , BDPVar ub2
    lem-bd-pair-p (BDPInl bd)
      with lem-bd-pair-p bd
    ... | bd' , ub = BDPInl bd' , BDPInl ub
    lem-bd-pair-p (BDPInr bd)
      with lem-bd-pair-p bd
    ... | bd' , ub = BDPInr bd' , BDPInr ub
    lem-bd-pair-p (BDPPair bd1 bd2)
      with lem-bd-pair-p bd1 | lem-bd-pair-p bd2
    ... | bd1' , ub1 | bd2' , ub2 =
      BDPPair bd1' bd2' , BDPPair ub1 ub2
    lem-bd-pair-p BDPWild = BDPWild , BDPWild
    lem-bd-pair-p BDPEHole = BDPEHole , BDPEHole
    lem-bd-pair-p (BDPNEHole bd)
      with lem-bd-pair-p bd
    ... | bd' , ub = BDPNEHole bd' , BDPNEHole ub
    
  mutual
    lem-bd-fst : {e : ihexp} {e1 : ihexp} →
                 binders-disjoint e (fst e1) →
                 binders-disjoint e e1
    lem-bd-fst BDNum = BDNum
    lem-bd-fst BDVar = BDVar
    lem-bd-fst (BDLam (UBFst ub) bd) = BDLam ub (lem-bd-fst bd)
    lem-bd-fst (BDAp bd1 bd2) =
      BDAp (lem-bd-fst bd1) (lem-bd-fst bd2)
    lem-bd-fst (BDInl bd) = BDInl (lem-bd-fst bd)
    lem-bd-fst (BDInr bd) = BDInr (lem-bd-fst bd)
    lem-bd-fst (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-bd-fst bd)
              (BDZRules (lem-bd-fst-rs bdpre)
                        (lem-bd-fst-rs bdpost))
    lem-bd-fst (BDPair bd1 bd2) =
      BDPair (lem-bd-fst bd1) (lem-bd-fst bd2)
    lem-bd-fst (BDFst bd) = BDFst (lem-bd-fst bd)
    lem-bd-fst (BDSnd bd) = BDSnd (lem-bd-fst bd)
    lem-bd-fst BDEHole = BDEHole
    lem-bd-fst (BDNEHole bd) = BDNEHole (lem-bd-fst bd)

    lem-bd-fst-rs : {rs : rules} {e1 : ihexp} →
                    binders-disjoint-rs rs (fst e1) →
                    binders-disjoint-rs rs e1
    lem-bd-fst-rs BDNoRules = BDNoRules
    lem-bd-fst-rs (BDRules bdr bdrs) =
      BDRules (lem-bd-fst-r bdr) (lem-bd-fst-rs bdrs)

    lem-bd-fst-r : {r : rule} {e1 : ihexp} →
                   binders-disjoint-r r (fst e1) →
                   binders-disjoint-r r e1
    lem-bd-fst-r (BDRule bdp bd) =
      BDRule (lem-bd-fst-p bdp) (lem-bd-fst bd)

    lem-bd-fst-p : {p : pattrn} {e1 : ihexp} →
                   binders-disjoint-p p (fst e1) →
                   binders-disjoint-p p e1
    lem-bd-fst-p BDPNum = BDPNum
    lem-bd-fst-p (BDPVar (UBFst ub)) = BDPVar ub
    lem-bd-fst-p (BDPInl bd) = BDPInl (lem-bd-fst-p bd)
    lem-bd-fst-p (BDPInr bd) = BDPInr (lem-bd-fst-p bd)
    lem-bd-fst-p (BDPPair bd1 bd2) =
      BDPPair (lem-bd-fst-p bd1) (lem-bd-fst-p bd2)
    lem-bd-fst-p BDPWild = BDPWild
    lem-bd-fst-p BDPEHole = BDPEHole
    lem-bd-fst-p (BDPNEHole bd) =
      BDPNEHole (lem-bd-fst-p bd)
    
  mutual
    lem-bd-snd : {e : ihexp} {e1 : ihexp} →
                 binders-disjoint e (snd e1) →
                 binders-disjoint e e1
    lem-bd-snd BDNum = BDNum
    lem-bd-snd BDVar = BDVar
    lem-bd-snd (BDLam (UBSnd ub) bd) =
      BDLam ub (lem-bd-snd bd)
    lem-bd-snd (BDAp bd1 bd2) =
      BDAp (lem-bd-snd bd1) (lem-bd-snd bd2)
    lem-bd-snd (BDInl bd) = BDInl (lem-bd-snd bd)
    lem-bd-snd (BDInr bd) = BDInr (lem-bd-snd bd)
    lem-bd-snd (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-bd-snd bd)
              (BDZRules (lem-bd-snd-rs bdpre)
                        (lem-bd-snd-rs bdpost))
    lem-bd-snd (BDPair bd1 bd2) =
      BDPair (lem-bd-snd bd1) (lem-bd-snd bd2)
    lem-bd-snd (BDFst bd) = BDFst (lem-bd-snd bd)
    lem-bd-snd (BDSnd bd) = BDSnd (lem-bd-snd bd)
    lem-bd-snd BDEHole = BDEHole
    lem-bd-snd (BDNEHole bd) = BDNEHole (lem-bd-snd bd)

    lem-bd-snd-rs : {rs : rules} {e1 : ihexp} →
                    binders-disjoint-rs rs (snd e1) →
                    binders-disjoint-rs rs e1
    lem-bd-snd-rs BDNoRules = BDNoRules
    lem-bd-snd-rs (BDRules bdr bdrs) =
      BDRules (lem-bd-snd-r bdr) (lem-bd-snd-rs bdrs)

    lem-bd-snd-r : {r : rule} {e1 : ihexp} →
                   binders-disjoint-r r (snd e1) →
                   binders-disjoint-r r e1
    lem-bd-snd-r (BDRule bdp bd) =
      BDRule (lem-bd-snd-p bdp) (lem-bd-snd bd)

    lem-bd-snd-p : {p : pattrn} {e1 : ihexp} →
                   binders-disjoint-p p (snd e1) →
                   binders-disjoint-p p e1
    lem-bd-snd-p BDPNum = BDPNum
    lem-bd-snd-p (BDPVar (UBSnd ub)) = BDPVar ub
    lem-bd-snd-p (BDPInl bd) = BDPInl (lem-bd-snd-p bd)
    lem-bd-snd-p (BDPInr bd) = BDPInr (lem-bd-snd-p bd)
    lem-bd-snd-p (BDPPair bd1 bd2) =
      BDPPair (lem-bd-snd-p bd1) (lem-bd-snd-p bd2)
    lem-bd-snd-p BDPWild = BDPWild
    lem-bd-snd-p BDPEHole = BDPEHole
    lem-bd-snd-p (BDPNEHole bd) =
      BDPNEHole (lem-bd-snd-p bd)

  mutual
    lem-bd-nehole : {e : ihexp} {e1 : ihexp} {u : Nat} →
                    binders-disjoint e ⦇⌜ e1 ⌟⦈[ u ] →
                    binders-disjoint e e1
    lem-bd-nehole BDNum = BDNum
    lem-bd-nehole BDVar = BDVar
    lem-bd-nehole (BDLam (UBNEHole ub) bd) =
      BDLam ub (lem-bd-nehole bd)
    lem-bd-nehole (BDAp bd1 bd2) =
      BDAp (lem-bd-nehole bd1) (lem-bd-nehole bd2)
    lem-bd-nehole (BDInl bd) = BDInl (lem-bd-nehole bd)
    lem-bd-nehole (BDInr bd) = BDInr (lem-bd-nehole bd)
    lem-bd-nehole (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-bd-nehole bd)
              (BDZRules (lem-bd-nehole-rs bdpre)
                        (lem-bd-nehole-rs bdpost))
    lem-bd-nehole (BDPair bd1 bd2) =
      BDPair (lem-bd-nehole bd1) (lem-bd-nehole bd2)
    lem-bd-nehole (BDFst bd) = BDFst (lem-bd-nehole bd)
    lem-bd-nehole (BDSnd bd) = BDSnd (lem-bd-nehole bd)
    lem-bd-nehole BDEHole = BDEHole
    lem-bd-nehole (BDNEHole bd) =
      BDNEHole (lem-bd-nehole bd)

    lem-bd-nehole-rs : {rs : rules} {e1 : ihexp} {u : Nat} →
                       binders-disjoint-rs rs ⦇⌜ e1 ⌟⦈[ u ] →
                       binders-disjoint-rs rs e1
    lem-bd-nehole-rs BDNoRules = BDNoRules
    lem-bd-nehole-rs (BDRules bdr bdrs) =
      BDRules (lem-bd-nehole-r bdr) (lem-bd-nehole-rs bdrs)

    lem-bd-nehole-r : {r : rule} {e1 : ihexp} {u : Nat} →
                      binders-disjoint-r r ⦇⌜ e1 ⌟⦈[ u ] →
                      binders-disjoint-r r e1
    lem-bd-nehole-r (BDRule bdp bd) =
      BDRule (lem-bd-nehole-p bdp) (lem-bd-nehole bd)

    lem-bd-nehole-p : {p : pattrn} {e1 : ihexp} {u : Nat} →
                      binders-disjoint-p p ⦇⌜ e1 ⌟⦈[ u ] →
                      binders-disjoint-p p e1
    lem-bd-nehole-p BDPNum = BDPNum
    lem-bd-nehole-p (BDPVar (UBNEHole ub)) = BDPVar ub
    lem-bd-nehole-p (BDPInl bd) = BDPInl (lem-bd-nehole-p bd)
    lem-bd-nehole-p (BDPInr bd) = BDPInr (lem-bd-nehole-p bd)
    lem-bd-nehole-p (BDPPair bd1 bd2) =
      BDPPair (lem-bd-nehole-p bd1) (lem-bd-nehole-p bd2)
    lem-bd-nehole-p BDPWild = BDPWild
    lem-bd-nehole-p BDPEHole = BDPEHole
    lem-bd-nehole-p (BDPNEHole bd) =
      BDPNEHole (lem-bd-nehole-p bd)
      
  mutual
    lem-rs-bd : {e : ihexp} {r : rule} {rs : rules} →
                binders-disjoint e (r / rs) →
                binders-disjoint e r ×
                  binders-disjoint e rs
    lem-rs-bd BDNum = BDNum , BDNum
    lem-rs-bd BDVar = BDVar , BDVar
    lem-rs-bd (BDLam (UBRules ubr ubrs) bd)
      with lem-rs-bd bd
    ... | bdr , bdrs = BDLam ubr bdr , BDLam ubrs bdrs
    lem-rs-bd (BDAp bd1 bd2)
      with lem-rs-bd bd1 | lem-rs-bd bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2 =
      BDAp bdr1 bdr2 , BDAp bdrs1 bdrs2
    lem-rs-bd (BDInl bd)
      with lem-rs-bd bd
    ... | bdr , bdrs = BDInl bdr , BDInl bdrs
    lem-rs-bd (BDInr bd)
      with lem-rs-bd bd
    ... | bdr , bdrs = BDInr bdr , BDInr bdrs
    lem-rs-bd (BDMatch bd (BDZRules bdpre bdpost))
      with lem-rs-bd bd |
           lem-rs-bd-rs bdpre |
           lem-rs-bd-rs bdpost
    ... | bdr , bdrs
        | bdprer , bdprers
        | bdpostr , bdpostrs =
      BDMatch bdr (BDZRules bdprer bdpostr) ,
      BDMatch bdrs (BDZRules bdprers bdpostrs)
    lem-rs-bd (BDPair bd1 bd2)
      with lem-rs-bd bd1 | lem-rs-bd bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2 =
      BDPair bdr1 bdr2 , BDPair bdrs1 bdrs2
    lem-rs-bd (BDFst bd)
      with lem-rs-bd bd
    ... | bdr , bdrs = BDFst bdr , BDFst bdrs
    lem-rs-bd (BDSnd bd)
      with lem-rs-bd bd
    ... | bdr , bdrs = BDSnd bdr , BDSnd bdrs
    lem-rs-bd BDEHole = BDEHole , BDEHole
    lem-rs-bd (BDNEHole bd)
      with lem-rs-bd bd
    ... | bdr , bdrs =
      BDNEHole bdr , BDNEHole bdrs

    lem-rs-bd-rs : {rs1 : rules} {r : rule} {rs2 : rules} →
                   binders-disjoint-rs rs1 (r / rs2) →
                   binders-disjoint-rs rs1 r ×
                     binders-disjoint-rs rs1 rs2
    lem-rs-bd-rs BDNoRules = BDNoRules , BDNoRules
    lem-rs-bd-rs (BDRules bdr bdrs)
      with lem-rs-bd-r bdr | lem-rs-bd-rs bdrs
    ... | bdrr , bdrrs | bdrsr , bdrsrs =
      BDRules bdrr bdrsr , BDRules bdrrs bdrsrs
   
    lem-rs-bd-r : {r1 : rule} {r2 : rule} {rs : rules} →
                  binders-disjoint-r r1 (r2 / rs) →
                  binders-disjoint-r r1 r2 ×
                    binders-disjoint-r r1 rs
    lem-rs-bd-r (BDRule bdp bd)
      with lem-rs-bd-p bdp | lem-rs-bd bd
    ... | bdpr , bdprs | bdr , bdrs =
      BDRule bdpr bdr , BDRule bdprs bdrs

    lem-rs-bd-p : {p : pattrn} {r : rule} {rs : rules} →
                  binders-disjoint-p p (r / rs) →
                  binders-disjoint-p p r ×
                    binders-disjoint-p p rs
    lem-rs-bd-p BDPNum = BDPNum , BDPNum
    lem-rs-bd-p (BDPVar (UBRules ubr ubrs)) =
      BDPVar ubr , BDPVar ubrs
    lem-rs-bd-p (BDPInl bd)
      with lem-rs-bd-p bd
    ... | bdr , bdrs = BDPInl bdr , BDPInl bdrs
    lem-rs-bd-p (BDPInr bd)
      with lem-rs-bd-p bd
    ... | bdr , bdrs = BDPInr bdr , BDPInr bdrs
    lem-rs-bd-p (BDPPair bd1 bd2)
      with lem-rs-bd-p bd1 | lem-rs-bd-p bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2  =
      BDPPair bdr1 bdr2 , BDPPair bdrs1 bdrs2
    lem-rs-bd-p BDPWild = BDPWild , BDPWild
    lem-rs-bd-p BDPEHole = BDPEHole , BDPEHole
    lem-rs-bd-p (BDPNEHole bd)
      with lem-rs-bd-p bd
    ... | bdr , bdrs = BDPNEHole bdr , BDPNEHole bdrs
    
  mutual
    lem-r-bd : {e : ihexp} {pr : pattrn} {er : ihexp} →
               binders-disjoint e (pr => er) →
               binders-disjoint e pr ×
                 binders-disjoint e er
    lem-r-bd BDNum = BDNum , BDNum
    lem-r-bd BDVar = BDVar , BDVar
    lem-r-bd (BDLam (UBRule ubr ub) bd)
      with lem-r-bd bd
    ... | bdp , bdr = BDLam ubr bdp , BDLam ub bdr
    lem-r-bd (BDAp bd1 bd2)
      with lem-r-bd bd1 | lem-r-bd bd2
    ... | bdp1 , bdr1 | bdp2 , bdr2 =
      BDAp bdp1 bdp2 , BDAp bdr1 bdr2
    lem-r-bd (BDInl bd)
      with lem-r-bd bd
    ... | bdp , bdr = BDInl bdp , BDInl bdr
    lem-r-bd (BDInr bd)
      with lem-r-bd bd
    ... | bdp , bdr = BDInr bdp , BDInr bdr
    lem-r-bd (BDMatch bd (BDZRules bdpre bdpost))
      with lem-r-bd bd |
           lem-r-bd-rs bdpre |
           lem-r-bd-rs bdpost 
    ... | bdp , bdr
        | bdprep , bdprer
        | bdpostp , bdpostr =
      BDMatch bdp (BDZRules bdprep bdpostp) ,
      BDMatch bdr (BDZRules bdprer bdpostr)
    lem-r-bd (BDPair bd1 bd2)
      with lem-r-bd bd1 | lem-r-bd bd2
    ... | bdp1 , bdr1 | bdp2 , bdr2 =
      BDPair bdp1 bdp2 , BDPair bdr1 bdr2
    lem-r-bd (BDFst bd)
      with lem-r-bd bd
    ... | bdp , bdr = BDFst bdp , BDFst bdr
    lem-r-bd (BDSnd bd)
      with lem-r-bd bd
    ... | bdp , bdr = BDSnd bdp , BDSnd bdr
    lem-r-bd BDEHole = BDEHole , BDEHole
    lem-r-bd (BDNEHole bd)
      with lem-r-bd bd
    ... | bdp , bdr = BDNEHole bdp , BDNEHole bdr

    lem-r-bd-rs : {rs : rules} {pr : pattrn} {er : ihexp} →
                  binders-disjoint-rs rs (pr => er) →
                  binders-disjoint-rs rs pr ×
                    binders-disjoint-rs rs er
    lem-r-bd-rs BDNoRules = BDNoRules , BDNoRules
    lem-r-bd-rs (BDRules bdr bdrs)
      with lem-r-bd-r bdr | lem-r-bd-rs bdrs
    ... | bdrp , bdre | bdrsp , bdrse =
      BDRules bdrp bdrsp , BDRules bdre bdrse

    lem-r-bd-r : {r : rule} {pr : pattrn} {er : ihexp} →
                 binders-disjoint-r r (pr => er) →
                 binders-disjoint-r r pr ×
                   binders-disjoint-r r er
    lem-r-bd-r (BDRule bdp bd)
      with lem-r-bd-p bdp | lem-r-bd bd
    ... | bdpp , bdpe | ebdp , ebde =
      BDRule bdpp ebdp , BDRule bdpe ebde

    lem-r-bd-p : {p : pattrn} {pr : pattrn} {er : ihexp} →
                 binders-disjoint-p p (pr => er) →
                 binders-disjoint-p p pr ×
                   binders-disjoint-p p er
    lem-r-bd-p BDPNum = BDPNum , BDPNum
    lem-r-bd-p (BDPVar (UBRule ubr ubrs)) =
      BDPVar ubr , BDPVar ubrs
    lem-r-bd-p (BDPInl bd)
      with lem-r-bd-p bd
    ... | bdp , bde = BDPInl bdp , BDPInl bde
    lem-r-bd-p (BDPInr bd)
      with lem-r-bd-p bd
    ... | bdp , bde = BDPInr bdp , BDPInr bde
    lem-r-bd-p (BDPPair bd1 bd2)
      with lem-r-bd-p bd1 | lem-r-bd-p bd2
    ... | bdp1 , bde1 | bdp2 , bde2 =
      BDPPair bdp1 bdp2 , BDPPair bde1 bde2
    lem-r-bd-p BDPWild = BDPWild , BDPWild
    lem-r-bd-p BDPEHole = BDPEHole , BDPEHole
    lem-r-bd-p (BDPNEHole bd)
      with lem-r-bd-p bd
    ... | bdp , bde =
      BDPNEHole bdp , BDPNEHole bde

  mutual
    lem-p-bd-var : {e : ihexp} {x : Nat} →
                   binders-disjoint {T = pattrn} e (X x) →
                   unbound-in x e
    lem-p-bd-var BDNum = UBNum
    lem-p-bd-var BDVar = UBVar
    lem-p-bd-var (BDLam (UBPVar x≠y) bd) =
      UBLam (flip x≠y) (lem-p-bd-var bd)
    lem-p-bd-var (BDAp bd1 bd2) =
      UBAp (lem-p-bd-var bd1) (lem-p-bd-var bd2)
    lem-p-bd-var (BDInl bd) =
      UBInl (lem-p-bd-var bd)
    lem-p-bd-var (BDInr bd) =
      UBInr (lem-p-bd-var bd)
    lem-p-bd-var (BDMatch bd (BDZRules bdpre bdpost)) =
      UBMatch (lem-p-bd-var bd)
              (UBZRules (lem-p-bd-var-rs bdpre)
                        (lem-p-bd-var-rs bdpost))
    lem-p-bd-var (BDPair bd1 bd2) =
      UBPair (lem-p-bd-var bd1) (lem-p-bd-var bd2)
    lem-p-bd-var (BDFst bd) = UBFst (lem-p-bd-var bd)
    lem-p-bd-var (BDSnd bd) = UBSnd (lem-p-bd-var bd)
    lem-p-bd-var BDEHole = UBEHole
    lem-p-bd-var (BDNEHole bd) =
      UBNEHole (lem-p-bd-var bd)

    lem-p-bd-var-rs : {rs : rules} {x : Nat} →
                      binders-disjoint-rs {T = pattrn} rs (X x) →
                      unbound-in x rs
    lem-p-bd-var-rs BDNoRules = UBNoRules
    lem-p-bd-var-rs (BDRules bdr bdrs) =
      UBRules (lem-p-bd-var-r bdr) (lem-p-bd-var-rs bdrs)

    lem-p-bd-var-r : {r : rule} {x : Nat} →
                     binders-disjoint-r {T = pattrn} r (X x) →
                     unbound-in x r
    lem-p-bd-var-r (BDRule bdp bd) =
      UBRule (lem-p-bd-var-p bdp) (lem-p-bd-var bd)

    lem-p-bd-var-p : {p : pattrn} {x : Nat} →
                     binders-disjoint-p {T = pattrn} p (X x) →
                     unbound-in x p
    lem-p-bd-var-p BDPNum = UBPNum
    lem-p-bd-var-p (BDPVar (UBPVar x≠y)) =
      UBPVar (flip x≠y)
    lem-p-bd-var-p (BDPInl bd) =
      UBPInl (lem-p-bd-var-p bd)
    lem-p-bd-var-p (BDPInr bd) =
      UBPInr (lem-p-bd-var-p bd)
    lem-p-bd-var-p (BDPPair bd1 bd2) =
      UBPPair (lem-p-bd-var-p bd1)
              (lem-p-bd-var-p bd2)
    lem-p-bd-var-p BDPWild = UBPWild
    lem-p-bd-var-p BDPEHole = UBPEHole
    lem-p-bd-var-p (BDPNEHole bd) =
      UBPNEHole (lem-p-bd-var-p bd)

  mutual
    lem-p-bd-inl : {e : ihexp} {p1 : pattrn} →
                   binders-disjoint e (inl p1) →
                   binders-disjoint e p1
    lem-p-bd-inl BDNum = BDNum
    lem-p-bd-inl BDVar = BDVar
    lem-p-bd-inl (BDLam (UBPInl ub) bd) =
      BDLam ub (lem-p-bd-inl bd)
    lem-p-bd-inl (BDAp bd1 bd2) =
      BDAp (lem-p-bd-inl bd1) (lem-p-bd-inl bd2)
    lem-p-bd-inl (BDInl bd) = BDInl (lem-p-bd-inl bd)
    lem-p-bd-inl (BDInr bd) = BDInr (lem-p-bd-inl bd)
    lem-p-bd-inl (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-p-bd-inl bd)
              (BDZRules (lem-p-bd-inl-rs bdpre)
                        (lem-p-bd-inl-rs bdpost))
    lem-p-bd-inl (BDPair bd1 bd2) =
      BDPair (lem-p-bd-inl bd1) (lem-p-bd-inl bd2)
    lem-p-bd-inl (BDFst bd) =  BDFst (lem-p-bd-inl bd)
    lem-p-bd-inl (BDSnd bd) = BDSnd (lem-p-bd-inl bd)
    lem-p-bd-inl BDEHole = BDEHole
    lem-p-bd-inl (BDNEHole bd) =
      BDNEHole (lem-p-bd-inl bd)

    lem-p-bd-inl-rs : {rs : rules} {p1 : pattrn} →
                      binders-disjoint-rs rs (inl p1) →
                      binders-disjoint-rs rs p1
    lem-p-bd-inl-rs BDNoRules = BDNoRules
    lem-p-bd-inl-rs (BDRules bdr bdrs) =
      BDRules (lem-p-bd-inl-r bdr) (lem-p-bd-inl-rs bdrs)

    lem-p-bd-inl-r : {r : rule} {p1 : pattrn} →
                     binders-disjoint-r r (inl p1) →
                     binders-disjoint-r r p1
    lem-p-bd-inl-r (BDRule bdp bd) =
      BDRule (lem-p-bd-inl-p bdp) (lem-p-bd-inl bd)

    lem-p-bd-inl-p : {p : pattrn} {p1 : pattrn} →
                     binders-disjoint-p p (inl p1) →
                     binders-disjoint-p p p1
    lem-p-bd-inl-p BDPNum = BDPNum
    lem-p-bd-inl-p (BDPVar (UBPInl ub)) = BDPVar ub
    lem-p-bd-inl-p (BDPInl bd) =
      BDPInl (lem-p-bd-inl-p bd)
    lem-p-bd-inl-p (BDPInr bd) =
      BDPInr (lem-p-bd-inl-p bd)
    lem-p-bd-inl-p (BDPPair bd1 bd2) =
      BDPPair (lem-p-bd-inl-p bd1)
        (lem-p-bd-inl-p bd2)
    lem-p-bd-inl-p BDPWild = BDPWild
    lem-p-bd-inl-p BDPEHole = BDPEHole
    lem-p-bd-inl-p (BDPNEHole bd) =
      BDPNEHole (lem-p-bd-inl-p bd)

  mutual
    lem-p-bd-inr : {e : ihexp} {p1 : pattrn} →
                   binders-disjoint e (inr p1) →
                   binders-disjoint e p1
    lem-p-bd-inr BDNum = BDNum
    lem-p-bd-inr BDVar = BDVar
    lem-p-bd-inr (BDLam (UBPInr ub) bd) =
      BDLam ub (lem-p-bd-inr bd)
    lem-p-bd-inr (BDAp bd1 bd2) =
      BDAp (lem-p-bd-inr bd1) (lem-p-bd-inr bd2)
    lem-p-bd-inr (BDInl bd) = BDInl (lem-p-bd-inr bd)
    lem-p-bd-inr (BDInr bd) = BDInr (lem-p-bd-inr bd)
    lem-p-bd-inr (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-p-bd-inr bd)
              (BDZRules (lem-p-bd-inr-rs bdpre)
                        (lem-p-bd-inr-rs bdpost))
    lem-p-bd-inr (BDPair bd1 bd2) =
      BDPair (lem-p-bd-inr bd1) (lem-p-bd-inr bd2)
    lem-p-bd-inr (BDFst bd) = BDFst (lem-p-bd-inr bd)
    lem-p-bd-inr (BDSnd bd) = BDSnd (lem-p-bd-inr bd)
    lem-p-bd-inr BDEHole = BDEHole
    lem-p-bd-inr (BDNEHole bd) = BDNEHole (lem-p-bd-inr bd)

    lem-p-bd-inr-rs : {rs : rules} {p1 : pattrn} →
                      binders-disjoint-rs rs (inr p1) →
                      binders-disjoint-rs rs p1
    lem-p-bd-inr-rs BDNoRules = BDNoRules
    lem-p-bd-inr-rs (BDRules bdr bdrs) =
      BDRules (lem-p-bd-inr-r bdr) (lem-p-bd-inr-rs bdrs)

    lem-p-bd-inr-r : {r : rule} {p1 : pattrn} →
                     binders-disjoint-r r (inr p1) →
                     binders-disjoint-r r p1
    lem-p-bd-inr-r (BDRule bdp bd) =
      BDRule (lem-p-bd-inr-p bdp) (lem-p-bd-inr bd)

    lem-p-bd-inr-p : {p : pattrn} {p1 : pattrn} →
                     binders-disjoint-p p (inr p1) →
                     binders-disjoint-p p p1
    lem-p-bd-inr-p BDPNum = BDPNum
    lem-p-bd-inr-p (BDPVar (UBPInr ub)) = BDPVar ub
    lem-p-bd-inr-p (BDPInl bd) =
      BDPInl (lem-p-bd-inr-p bd)
    lem-p-bd-inr-p (BDPInr bd) =
      BDPInr (lem-p-bd-inr-p bd)
    lem-p-bd-inr-p (BDPPair bd1 bd2) =
      BDPPair (lem-p-bd-inr-p bd1)
              (lem-p-bd-inr-p bd2)
    lem-p-bd-inr-p BDPWild = BDPWild
    lem-p-bd-inr-p BDPEHole = BDPEHole
    lem-p-bd-inr-p (BDPNEHole bd) =
      BDPNEHole (lem-p-bd-inr-p bd)

  mutual
    lem-p-bd-pair : {e : ihexp} {p1 p2 : pattrn} →
                    binders-disjoint e ⟨ p1 , p2 ⟩ →
                    binders-disjoint e p1 ×
                      binders-disjoint e p2
    lem-p-bd-pair BDNum = BDNum , BDNum
    lem-p-bd-pair BDVar = BDVar , BDVar
    lem-p-bd-pair (BDLam (UBPPair ub1 ub2) bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDLam ub1 bd1 , BDLam ub2 bd2
    lem-p-bd-pair (BDAp bd1 bd2)
      with lem-p-bd-pair bd1 | lem-p-bd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDAp bd1₁ bd2₁ , BDAp bd1₂ bd2₂
    lem-p-bd-pair (BDInl bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDInl bd1 , BDInl bd2
    lem-p-bd-pair (BDInr bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDInr bd1 , BDInr bd2
    lem-p-bd-pair (BDMatch bd (BDZRules bdpre bdpost))
      with lem-p-bd-pair bd |
           lem-p-bd-pair-rs bdpre |
           lem-p-bd-pair-rs bdpost
    ... | bd1 , bd2
        | bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      BDMatch bd1 (BDZRules bdpre1 bdpost1) ,
      BDMatch bd2 (BDZRules bdpre2 bdpost2)
    lem-p-bd-pair (BDPair bd1 bd2)
      with lem-p-bd-pair bd1 | lem-p-bd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDPair bd1₁ bd2₁ , BDPair bd1₂ bd2₂
    lem-p-bd-pair (BDFst bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDFst bd1 , BDFst bd2
    lem-p-bd-pair (BDSnd bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDSnd bd1 , BDSnd bd2
    lem-p-bd-pair BDEHole = BDEHole , BDEHole
    lem-p-bd-pair (BDNEHole bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDNEHole bd1 , BDNEHole bd2

    lem-p-bd-pair-rs : {rs : rules} {p1 p2 : pattrn} →
                       binders-disjoint-rs rs ⟨ p1 , p2 ⟩ →
                       binders-disjoint-rs rs p1 ×
                         binders-disjoint-rs rs p2
    lem-p-bd-pair-rs BDNoRules = BDNoRules , BDNoRules
    lem-p-bd-pair-rs (BDRules bdr bdrs)
      with lem-p-bd-pair-r bdr |
           lem-p-bd-pair-rs bdrs
    ... | bdr1 , bdr2 | bdrs1 , bdrs2 =
      BDRules bdr1 bdrs1 , BDRules bdr2 bdrs2

    lem-p-bd-pair-r : {r : rule} {p1 p2 : pattrn} →
                      binders-disjoint-r r ⟨ p1 , p2 ⟩ →
                      binders-disjoint-r r p1 ×
                        binders-disjoint-r r p2
    lem-p-bd-pair-r (BDRule bdp bd)
      with lem-p-bd-pair-p bdp |
           lem-p-bd-pair bd
    ... | bdp1 , bdp2 | bd1 , bd2 =
      BDRule bdp1 bd1 , BDRule bdp2 bd2

    lem-p-bd-pair-p : {p : pattrn} {p1 p2 : pattrn} →
                      binders-disjoint-p p ⟨ p1 , p2 ⟩ →
                      binders-disjoint-p p p1 ×
                        binders-disjoint-p p p2
    lem-p-bd-pair-p BDPNum = BDPNum , BDPNum
    lem-p-bd-pair-p (BDPVar (UBPPair ub1 ub2)) =
      BDPVar ub1 , BDPVar ub2
    lem-p-bd-pair-p (BDPInl bd)
      with lem-p-bd-pair-p bd
    ... | bd1 , bd2 = BDPInl bd1 , BDPInl bd2
    lem-p-bd-pair-p (BDPInr bd)
      with lem-p-bd-pair-p bd
    ... | bd1 , bd2 = BDPInr bd1 , BDPInr bd2
    lem-p-bd-pair-p (BDPPair bd1 bd2)
      with lem-p-bd-pair-p bd1 |
           lem-p-bd-pair-p bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDPPair bd1₁ bd2₁ , BDPPair bd1₂ bd2₂
    lem-p-bd-pair-p BDPWild = BDPWild , BDPWild
    lem-p-bd-pair-p BDPEHole = BDPEHole , BDPEHole
    lem-p-bd-pair-p (BDPNEHole bd)
      with lem-p-bd-pair-p bd
    ... | bd1 , bd2 = BDPNEHole bd1 , BDPNEHole bd2

  mutual
    lem-p-bd-nehole : {e : ihexp}
                      {p1 : pattrn} {w : Nat} {τ : htyp} →
                      binders-disjoint e ⦇⌜ p1 ⌟⦈[ w , τ ] →
                      binders-disjoint e p1
    lem-p-bd-nehole BDNum = BDNum
    lem-p-bd-nehole BDVar = BDVar
    lem-p-bd-nehole (BDLam (UBPNEHole ub) bd) =
      BDLam ub (lem-p-bd-nehole bd)
    lem-p-bd-nehole (BDAp bd1 bd2) =
      BDAp (lem-p-bd-nehole bd1) (lem-p-bd-nehole bd2)
    lem-p-bd-nehole (BDInl bd) =
      BDInl (lem-p-bd-nehole bd)
    lem-p-bd-nehole (BDInr bd) =
      BDInr (lem-p-bd-nehole bd)
    lem-p-bd-nehole (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-p-bd-nehole bd)
              (BDZRules (lem-p-bd-nehole-rs bdpre)
                        (lem-p-bd-nehole-rs bdpost))
    lem-p-bd-nehole (BDPair bd1 bd2) =
      BDPair (lem-p-bd-nehole bd1) (lem-p-bd-nehole bd2)
    lem-p-bd-nehole (BDFst bd) =
      BDFst (lem-p-bd-nehole bd)
    lem-p-bd-nehole (BDSnd bd) =
      BDSnd (lem-p-bd-nehole bd)
    lem-p-bd-nehole BDEHole = BDEHole
    lem-p-bd-nehole (BDNEHole bd) =
      BDNEHole (lem-p-bd-nehole bd)

    lem-p-bd-nehole-rs : {rs : rules}
                        {p1 : pattrn} {w : Nat} {τ : htyp} →
                        binders-disjoint-rs rs ⦇⌜ p1 ⌟⦈[ w , τ ] →
                        binders-disjoint-rs rs p1
    lem-p-bd-nehole-rs BDNoRules = BDNoRules
    lem-p-bd-nehole-rs (BDRules bdr bdrs) =
      BDRules (lem-p-bd-nehole-r bdr) (lem-p-bd-nehole-rs bdrs)

    lem-p-bd-nehole-r : {r : rule}
                        {p1 : pattrn} {w : Nat} {τ : htyp} →
                        binders-disjoint-r r ⦇⌜ p1 ⌟⦈[ w , τ ] →
                        binders-disjoint-r r p1
    lem-p-bd-nehole-r (BDRule bdp bd) =
      BDRule (lem-p-bd-nehole-p bdp) (lem-p-bd-nehole bd)

    lem-p-bd-nehole-p : {p : pattrn}
                        {p1 : pattrn} {w : Nat} {τ : htyp} →
                        binders-disjoint-p p ⦇⌜ p1 ⌟⦈[ w , τ ] →
                        binders-disjoint-p p p1
    lem-p-bd-nehole-p BDPNum = BDPNum
    lem-p-bd-nehole-p (BDPVar (UBPNEHole ub)) = BDPVar ub
    lem-p-bd-nehole-p (BDPInl bd) =
      BDPInl (lem-p-bd-nehole-p bd)
    lem-p-bd-nehole-p (BDPInr bd) =
      BDPInr (lem-p-bd-nehole-p bd)
    lem-p-bd-nehole-p (BDPPair bd1 bd2) =
      BDPPair (lem-p-bd-nehole-p bd1)
              (lem-p-bd-nehole-p bd2)
    lem-p-bd-nehole-p BDPWild = BDPWild
    lem-p-bd-nehole-p BDPEHole = BDPEHole
    lem-p-bd-nehole-p (BDPNEHole bd) =
      BDPNEHole (lem-p-bd-nehole-p bd)
    
  mutual
    binders-disjoint-sym : {e1 e2 : ihexp} →
                           binders-disjoint e1 e2 →
                           binders-disjoint e2 e1
    binders-disjoint-sym {e2 = N n} bd = BDNum
    binders-disjoint-sym {e2 = X x} bd = BDVar
    binders-disjoint-sym {e2 = ·λ x ·[ τ ] e2} bd
      with lem-bd-lam bd
    ... | ub , bd' =
      BDLam ub (binders-disjoint-sym bd')
    binders-disjoint-sym {e2 = e2₁ ∘ e2₂} bd
      with lem-bd-ap bd
    ... | bd1 , bd2 =
      BDAp (binders-disjoint-sym bd1)
           (binders-disjoint-sym bd2)
    binders-disjoint-sym {e2 = inl τ e2} bd =
      BDInl (binders-disjoint-sym (lem-bd-inl bd))
    binders-disjoint-sym {e2 = inr τ e2} bd =
      BDInr (binders-disjoint-sym (lem-bd-inr bd))
    binders-disjoint-sym
      {e2 = match e2 (rs-pre / r / rs-post)} bd
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDMatch (binders-disjoint-sym bd')
              (BDZRules (rs-binders-disjoint-sym bdpre)
                        (BDRules (r-binders-disjoint-sym bdr)
                                 (rs-binders-disjoint-sym bdpost)))
                        
    binders-disjoint-sym {e2 = ⟨ e2₁ , e2₂ ⟩} bd
      with lem-bd-pair bd
    ... | bd1 , bd2 =
      BDPair (binders-disjoint-sym bd1)
             (binders-disjoint-sym bd2)
    binders-disjoint-sym {e2 = fst e2} bd =
      BDFst (binders-disjoint-sym (lem-bd-fst bd))
    binders-disjoint-sym {e2 = snd e2} bd =
      BDSnd (binders-disjoint-sym (lem-bd-snd bd))
    binders-disjoint-sym {e2 = ⦇-⦈[ u ]} bd = BDEHole
    binders-disjoint-sym {e2 = ⦇⌜ e2 ⌟⦈[ u ]} bd =
      BDNEHole (binders-disjoint-sym (lem-bd-nehole bd))

    rs-binders-disjoint-sym : {e : ihexp} {rs : rules} →
                              binders-disjoint e rs →
                              binders-disjoint-rs rs e
    rs-binders-disjoint-sym {rs = nil} bd = BDNoRules
    rs-binders-disjoint-sym {rs = r / rs} bd
      with lem-rs-bd bd
    ... | rbd , rsbd =
      BDRules (r-binders-disjoint-sym rbd)
              (rs-binders-disjoint-sym rsbd)

    r-binders-disjoint-sym : {e : ihexp} {r : rule} →
                             binders-disjoint e r →
                             binders-disjoint-r r e
    r-binders-disjoint-sym {r = pr => er} bd
      with lem-r-bd bd
    ... | bdp , bde =
      BDRule (p-binders-disjoint-sym bdp)
             (binders-disjoint-sym bde)
    
    p-binders-disjoint-sym : {e : ihexp} {p : pattrn} →
                             binders-disjoint e p →
                             binders-disjoint-p p e
    p-binders-disjoint-sym {p = N n} bd = BDPNum
    p-binders-disjoint-sym {p = X x} bd =
      BDPVar (lem-p-bd-var bd)
    p-binders-disjoint-sym {p = inl p} bd =
      BDPInl (p-binders-disjoint-sym (lem-p-bd-inl bd))
    p-binders-disjoint-sym {p = inr p} bd =
      BDPInr (p-binders-disjoint-sym (lem-p-bd-inr bd))
    p-binders-disjoint-sym {p = ⟨ p1 , p2 ⟩} bd
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = 
      BDPPair (p-binders-disjoint-sym bd1)
              (p-binders-disjoint-sym bd2)
    p-binders-disjoint-sym {p = wild} bd = BDPWild
    p-binders-disjoint-sym {p = ⦇-⦈[ w ]} bd = BDPEHole
    p-binders-disjoint-sym {p = ⦇⌜ p ⌟⦈[ w , τ ]} bd =
      BDPNEHole (p-binders-disjoint-sym (lem-p-bd-nehole bd))
