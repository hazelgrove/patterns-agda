open import Nat
open import Prelude
open import binders-disjointness
open import contexts
open import core
open import freshness
open import lemmas-contexts
open import patterns-core
open import result-judgements
open import statics-core

module lemmas-freshness where
  unbound-in-p-apart-Γp : ∀{p τ ξ Γp Δp x} →
                          p :: τ [ ξ ]⊣ Γp , Δp →
                          unbound-in-p x p →
                          x # Γp
  unbound-in-p-apart-Γp PTVar (UBPVar x≠y) =
    neq-apart-singleton x≠y
  unbound-in-p-apart-Γp PTNum UBPNum = refl
  unbound-in-p-apart-Γp (PTInl pt) (UBPInl ub) =
    unbound-in-p-apart-Γp pt ub
  unbound-in-p-apart-Γp (PTInr pt) (UBPInr ub) =
    unbound-in-p-apart-Γp pt ub
  unbound-in-p-apart-Γp {x = x}
                        (PTPair {Γ1 = Γ1} {Γ2 = Γ2}
                                disj disjh pt1 pt2)
                        (UBPPair ub1 ub2) =
    apart-parts Γ1 Γ2 x
                (unbound-in-p-apart-Γp pt1 ub1)
                (unbound-in-p-apart-Γp pt2 ub2)
  unbound-in-p-apart-Γp PTEHole UBPEHole = refl
  unbound-in-p-apart-Γp (PTNEHole pt apt') (UBPNEHole ub) =
    unbound-in-p-apart-Γp pt ub
  unbound-in-p-apart-Γp PTWild UBPWild = refl

  dom-Γp-unbound-in : ∀{p τ ξ Γp Δp x T t} →
                      {{_ : UnboundIn T}} →
                      p :: τ [ ξ ]⊣ Γp , Δp →
                      dom Γp x →
                      binders-disjoint-p {T = T} p t →
                      unbound-in x t
  dom-Γp-unbound-in PTVar x∈Γp (BDPVar {x = y} ub)
    with dom-singleton-eq x∈Γp
  ... | refl = ub
  dom-Γp-unbound-in (PTInl pt) x∈Γp (BDPInl bd) =
    dom-Γp-unbound-in pt x∈Γp bd
  dom-Γp-unbound-in (PTInr pt) x∈Γp (BDPInr bd) =
    dom-Γp-unbound-in pt x∈Γp bd
  dom-Γp-unbound-in {x = x} (PTPair {Γ1 = Γ1} {Γ2 = Γ2}
                                    Γ1##Γ2 Δ1##Δ2 pt1 pt2)
                    (τ , x∈Γp)
                    (BDPPair bd1 bd2)
    with dom-union-part Γ1 Γ2 x τ x∈Γp
  ... | Inl x∈Γ1 = dom-Γp-unbound-in pt1 (τ , x∈Γ1) bd1
  ... | Inr x∈Γ2 = dom-Γp-unbound-in pt2 (τ , x∈Γ2) bd2
  dom-Γp-unbound-in PTEHole () BDPEHole
  dom-Γp-unbound-in (PTNEHole pt w#Δ) x∈Γp (BDPNEHole bd) =
    dom-Γp-unbound-in pt x∈Γp bd

  
  apart-Γp-unbound-in-p : ∀{p τ ξ Γp Δp x} →
                          p :: τ [ ξ ]⊣ Γp , Δp →
                          x # Γp →
                          unbound-in-p x p
  apart-Γp-unbound-in-p {τ = τ} {x = x} (PTVar {x = y}) x#Γp =
    UBPVar (apart-singleton-neq x#Γp)
  apart-Γp-unbound-in-p PTNum x#Γp = UBPNum
  apart-Γp-unbound-in-p (PTInl pt) x#Γp =
    UBPInl (apart-Γp-unbound-in-p pt x#Γp)
  apart-Γp-unbound-in-p (PTInr pt) x#Γp =
    UBPInr (apart-Γp-unbound-in-p pt x#Γp)
  apart-Γp-unbound-in-p {x = x}
                        (PTPair {Γ1 = Γ1} {Γ2 = Γ2}
                                Γ1##Γ2 Δ1##Δ2 pt1 pt2)
                        x#Γp =
    UBPPair (apart-Γp-unbound-in-p pt1
                                   (apart-union-l Γ1 Γ2 x x#Γp))
            (apart-Γp-unbound-in-p pt2
                                   (apart-union-r Γ1 Γ2 x x#Γp))
  apart-Γp-unbound-in-p PTEHole x#Γp = UBPEHole
  apart-Γp-unbound-in-p (PTNEHole pt w#Δ) x#Γp =
    UBPNEHole (apart-Γp-unbound-in-p pt x#Γp)
  apart-Γp-unbound-in-p PTWild x#Γp = UBPWild
  
  hole-unbound-in-p-apart-Δp : ∀{u p τ ξ Γp Δp} →
                               p :: τ [ ξ ]⊣ Γp , Δp →
                               hole-unbound-in-p u p →
                               u # Δp
  hole-unbound-in-p-apart-Δp PTNum HUBPNum = refl
  hole-unbound-in-p-apart-Δp PTVar HUBPVar = refl
  hole-unbound-in-p-apart-Δp (PTInl pt) (HUBPInl hub) =
    hole-unbound-in-p-apart-Δp pt hub
  hole-unbound-in-p-apart-Δp (PTInr pt) (HUBPInr hub) =
    hole-unbound-in-p-apart-Δp pt hub
  hole-unbound-in-p-apart-Δp {u = u}
                             (PTPair {Δ1 = Δ1} {Δ2 = Δ2}
                                     disj disjh pt1 pt2)
                             (HUBPPair hub1 hub2) =
    apart-parts Δ1 Δ2 u
                (hole-unbound-in-p-apart-Δp pt1 hub1)
                (hole-unbound-in-p-apart-Δp pt2 hub2)
  hole-unbound-in-p-apart-Δp PTWild HUBPWild = refl
  hole-unbound-in-p-apart-Δp PTEHole (HUBPEHole u≠u') =
    neq-apart-singleton u≠u'
  hole-unbound-in-p-apart-Δp {u = u} (PTNEHole pt apt')
                          (HUBPNEHole {u' = u'} u≠u' hub)
    with hole-unbound-in-p-apart-Δp pt hub
  ... | apt
    with natEQ u' u
  ... | Inl u'=u = abort (u≠u' (! u'=u))
  ... | Inr u'≠u = apt

  dom-Δp-unbound-in : ∀{p τ ξ Γp Δp u T t} →
                      {{_ : HoleUnboundIn T}} →
                      p :: τ [ ξ ]⊣ Γp , Δp →
                      dom Δp u →
                      hole-binders-disjoint-p {T = T} p t →
                      hole-unbound-in u t
  dom-Δp-unbound-in PTVar () HBDPVar
  dom-Δp-unbound-in (PTInl pt) u∈Δp (HBDPInl bd) =
     dom-Δp-unbound-in pt u∈Δp bd
  dom-Δp-unbound-in (PTInr pt) u∈Δp (HBDPInr bd) =
     dom-Δp-unbound-in pt u∈Δp bd
  dom-Δp-unbound-in {u = u} (PTPair {Δ1 = Δ1} {Δ2 = Δ2}
                                    Γ1##Γ2 Δ1##Δ2 pt1 pt2)
                    (τ , u∈Δp)
                    (HBDPPair bd1 bd2)
    with dom-union-part Δ1 Δ2 u τ u∈Δp
  ... | Inl u∈Δ1 = dom-Δp-unbound-in pt1 (τ , u∈Δ1) bd1
  ... | Inr u∈Δ2 = dom-Δp-unbound-in pt2 (τ , u∈Δ2) bd2
  dom-Δp-unbound-in PTEHole u∈Δp (HBDPEHole ub)
    with dom-singleton-eq u∈Δp
  ... | refl = ub
  dom-Δp-unbound-in {u = u}
                    (PTNEHole {w = w} {τ = τ1} {Δ = Δ} pt w#Δ)
                    (τ , u∈Δp) (HBDPNEHole ub bd)
    with dom-union-part (■ (w , τ1)) Δ u τ u∈Δp
  ... | Inr u∈Δ = dom-Δp-unbound-in pt (τ , u∈Δ) bd
  ... | Inl u∈■
    with dom-singleton-eq (τ , u∈■)
  ... | refl = ub
  
  apart-Δp-hole-unbound-in-p : ∀{u p τ ξ Γp Δp} →
                               p :: τ [ ξ ]⊣ Γp , Δp →
                               u # Δp →
                               hole-unbound-in-p u p
  apart-Δp-hole-unbound-in-p PTVar u#Δp = HUBPVar
  apart-Δp-hole-unbound-in-p PTNum u#Δp = HUBPNum
  apart-Δp-hole-unbound-in-p (PTInl pt) u#Δp =
    HUBPInl (apart-Δp-hole-unbound-in-p pt u#Δp)
  apart-Δp-hole-unbound-in-p (PTInr pt) u#Δp =
    HUBPInr (apart-Δp-hole-unbound-in-p pt u#Δp)
  apart-Δp-hole-unbound-in-p {u = u}
                             (PTPair {Δ1 = Δ1} {Δ2 = Δ2}
                                     Γ1##Γ2 Δ1##Δ2 pt1 pt2)
                             u#Δp =
    HUBPPair (apart-Δp-hole-unbound-in-p
               pt1 (apart-union-l Δ1 Δ2 u u#Δp))
             (apart-Δp-hole-unbound-in-p
               pt2 (apart-union-r Δ1 Δ2 u u#Δp))
  apart-Δp-hole-unbound-in-p {u = u}
                             (PTEHole {w = w} {τ = τ})
                             u#Δp =
    HUBPEHole (apart-singleton-neq u#Δp)
  apart-Δp-hole-unbound-in-p {u = u}
                             (PTNEHole {w = w} {τ = τ} {Δ = Δ}
                                       pt w#Δ)
                             u#Δp =
    HUBPNEHole (apart-singleton-neq
                 (apart-union-l (■ (w , τ)) Δ u u#Δp))
               (apart-Δp-hole-unbound-in-p
                 pt (apart-union-r (■ (w , τ)) Δ u u#Δp))
  apart-Δp-hole-unbound-in-p PTWild u#Δp = HUBPWild

  mutual
    binders-fresh-r : ∀{Γ Δ r τ1 ξ τ2 x} →
                      Γ , Δ ⊢ r :: τ1 [ ξ ]=> τ2 →
                      unbound-in-r x r →
                      x # Γ →
                      fresh-r x r
    binders-fresh-r {Γ = Γ} {x = x}
                    (CTRule {Γp = Γp} pt Γ##Γp Δ##Δp wt)
                    (UBRule xubp xube) x#Γ =        
      FRule xubp
            (binders-fresh wt xube
              (apart-parts Γ Γp x x#Γ
                (unbound-in-p-apart-Γp pt xubp)))

    binders-fresh-rs : ∀{Γ Δ rs τ1 ξ τ2 x} →
                       Γ , Δ ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                       unbound-in-rs x rs →
                       x # Γ →
                       fresh-rs x rs
    binders-fresh-rs (CTOneRule rt) (UBRules xubr _) x#Γ = 
      FRules (binders-fresh-r rt xubr x#Γ) FNoRules
    binders-fresh-rs (CTRules rt rst)
                     (UBRules xubr xubrs) x#Γ =
      FRules (binders-fresh-r rt xubr x#Γ)
             (binders-fresh-rs rst xubrs x#Γ)
    
    binders-fresh : ∀{Γ Δ e τ x} →
                    Γ , Δ ⊢ e :: τ →
                    unbound-in x e →
                    x # Γ →
                    fresh x e
    binders-fresh TANum UBNum x#Γ = FNum
    binders-fresh (TAVar {x = y} y∈Γ) UBVar x#Γ =
      FVar (λ{ refl → some-not-none ((! y∈Γ) · x#Γ) })
    binders-fresh {Γ = Γ} (TALam {x = y} y#Γ wt)
                  (UBLam x≠y xub) x#Γ =
      FLam x≠y (binders-fresh wt xub (neq-apart-extend Γ x≠y x#Γ))
    binders-fresh (TAAp wt1 wt2) (UBAp ub1 ub2) x#Γ =
      FAp (binders-fresh wt1 ub1 x#Γ) (binders-fresh wt2 ub2 x#Γ)
    binders-fresh (TAInl wt) (UBInl ub) x#Γ =
      FInl (binders-fresh wt ub x#Γ)
    binders-fresh (TAInr wt) (UBInr ub) x#Γ =
      FInr (binders-fresh wt ub x#Γ)
    binders-fresh (TAMatchZPre {r = p => d} wt (CTOneRule rt))
                  (UBMatch xube (UBZRules UBNoRules (UBRules ubr _))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules FNoRules
                      (FRules (binders-fresh-r rt ubr x#Γ)
                              FNoRules))
    binders-fresh (TAMatchZPre {r = p => d} wt (CTRules rt rst))
                  (UBMatch xube (UBZRules _ (UBRules ubr xubrs))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules FNoRules
                      (FRules (binders-fresh-r rt ubr x#Γ)
                              (binders-fresh-rs rst xubrs x#Γ)))
    binders-fresh (TAMatchNZPre wt fin pret (CTOneRule rt) ¬red)
                  (UBMatch xube
                           (UBZRules xubpre (UBRules xubr xubpost))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules (binders-fresh-rs pret xubpre x#Γ)
                      (FRules (binders-fresh-r rt xubr x#Γ)
                              FNoRules))
    binders-fresh (TAMatchNZPre wt fin pret
                                (CTRules rt postt) ¬red)
                  (UBMatch xube
                           (UBZRules xubpre (UBRules xubr xubpost))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules (binders-fresh-rs pret xubpre x#Γ)
                      (FRules (binders-fresh-r rt xubr x#Γ)
                              (binders-fresh-rs postt xubpost x#Γ)))
    binders-fresh (TAPair wt1 wt2) (UBPair ub1 ub2) x#Γ =
      FPair (binders-fresh wt1 ub1 x#Γ)
            (binders-fresh wt2 ub2 x#Γ)
    binders-fresh (TAFst wt) (UBFst ub) x#Γ =
      FFst (binders-fresh wt ub x#Γ)
    binders-fresh (TASnd wt) (UBSnd ub) x#Γ =
      FSnd (binders-fresh wt ub x#Γ)
    binders-fresh (TAEHole u∈Δ) UBEHole x#Γ = FEHole
    binders-fresh (TANEHole u∈Δ wt) (UBNEHole ub) x#Γ =
      FNEHole (binders-fresh wt ub x#Γ)

  mutual
    hole-binders-fresh-r : ∀{Γ Δ r τ1 ξ τ2 u} →
                           Γ , Δ ⊢ r :: τ1 [ ξ ]=> τ2 →
                           hole-unbound-in-r u r →
                           u # Δ →
                           hole-fresh-r u r
    hole-binders-fresh-r {Δ = Δ} {u = u}
                    (CTRule {Δp = Δp} pt Γ##Γp Δ##Δp wt)
                    (HUBRule ubp ube) u#Δ =        
      HFRule ubp
             (hole-binders-fresh
               wt ube
               (apart-parts Δ Δp u u#Δ
                            (hole-unbound-in-p-apart-Δp pt ubp)))

    hole-binders-fresh-rs : ∀{Γ Δ rs τ1 ξ τ2 u} →
                            Γ , Δ ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                            hole-unbound-in-rs u rs →
                            u # Δ →
                            hole-fresh-rs u rs
    hole-binders-fresh-rs (CTOneRule rt) (HUBRules ubr _) u#Δ = 
      HFRules (hole-binders-fresh-r rt ubr u#Δ) HFNoRules
    hole-binders-fresh-rs (CTRules rt rst)
                     (HUBRules ubr ubrs) u#Δ =
      HFRules (hole-binders-fresh-r rt ubr u#Δ)
              (hole-binders-fresh-rs rst ubrs u#Δ)
    
    hole-binders-fresh : ∀{Γ Δ e τ u} →
                         Γ , Δ ⊢ e :: τ →
                         hole-unbound-in u e →
                         u # Δ →
                         hole-fresh u e
    hole-binders-fresh TANum HUBNum u#Δ = HFNum
    hole-binders-fresh (TAVar x∈Γ) HUBVar u#Δ = HFVar
    hole-binders-fresh (TALam x#Γ wt) (HUBLam ub) u#Δ =
      HFLam (hole-binders-fresh wt ub u#Δ)
    hole-binders-fresh (TAAp wt1 wt2) (HUBAp ub1 ub2) u#Δ =
      HFAp (hole-binders-fresh wt1 ub1 u#Δ)
           (hole-binders-fresh wt2 ub2 u#Δ)
    hole-binders-fresh (TAInl wt) (HUBInl ub) u#Δ =
      HFInl (hole-binders-fresh wt ub u#Δ)
    hole-binders-fresh (TAInr wt) (HUBInr ub) u#Δ =
      HFInr (hole-binders-fresh wt ub u#Δ)
    hole-binders-fresh (TAMatchZPre {r = p => d} wt (CTOneRule rt))
                       (HUBMatch ube
                                 (HUBZRules HUBNoRules (HUBRules ubr _)))
                       u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules HFNoRules
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 HFNoRules))
    hole-binders-fresh (TAMatchZPre {r = p => d} wt
                                    (CTRules rt rst))
                       (HUBMatch ube (HUBZRules _ (HUBRules ubr ubrs))) u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules HFNoRules
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 (hole-binders-fresh-rs rst ubrs u#Δ)))
    hole-binders-fresh (TAMatchNZPre wt fin pret
                                     (CTOneRule rt) ¬red)
                       (HUBMatch ube (HUBZRules ubpre (HUBRules ubr ubpost)))
                       u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules (hole-binders-fresh-rs pret ubpre u#Δ)
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 HFNoRules))
    hole-binders-fresh (TAMatchNZPre wt fin pret
                                     (CTRules rt postt) ¬red)
                       (HUBMatch ube (HUBZRules ubpre (HUBRules ubr ubpost)))
                       u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules (hole-binders-fresh-rs pret ubpre u#Δ)
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 (hole-binders-fresh-rs postt ubpost u#Δ)))
    hole-binders-fresh (TAPair wt1 wt2) (HUBPair ub1 ub2) u#Δ =
       HFPair (hole-binders-fresh wt1 ub1 u#Δ)
              (hole-binders-fresh wt2 ub2 u#Δ)
    hole-binders-fresh (TAFst wt) (HUBFst ub) u#Δ =
       HFFst (hole-binders-fresh wt ub u#Δ)
    hole-binders-fresh (TASnd wt) (HUBSnd ub) u#Δ =
       HFSnd (hole-binders-fresh wt ub u#Δ)
    hole-binders-fresh (TAEHole {u = u'} u'∈Δ) HUBEHole u#Δ =
       HFEHole λ{ refl → some-not-none (! u'∈Δ · u#Δ)}
    hole-binders-fresh (TANEHole {u = u'} u'∈Δ wt)
                       (HUBNEHole ub) u#Δ =
       HFNEHole (λ{ refl → some-not-none (! u'∈Δ · u#Δ) })
                (hole-binders-fresh wt ub u#Δ)
                
  
