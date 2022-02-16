open import List
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
                          Δp ⊢ p :: τ [ ξ ]⊣ Γp →
                          unbound-in-p x p →
                          x # Γp
  unbound-in-p-apart-Γp PTUnit UBPUnit = refl
  unbound-in-p-apart-Γp PTNum UBPNum = refl
  unbound-in-p-apart-Γp PTVar (UBPVar x≠y) =
    neq-apart-singleton x≠y
  unbound-in-p-apart-Γp (PTInl pt) (UBPInl ub) =
    unbound-in-p-apart-Γp pt ub
  unbound-in-p-apart-Γp (PTInr pt) (UBPInr ub) =
    unbound-in-p-apart-Γp pt ub
  unbound-in-p-apart-Γp {x = x}
                        (PTPair {Γ1 = Γ1} {Γ2 = Γ2}
                                disj pt1 pt2)
                        (UBPPair ub1 ub2) =
    apart-parts Γ1 Γ2 x
                (unbound-in-p-apart-Γp pt1 ub1)
                (unbound-in-p-apart-Γp pt2 ub2)
  unbound-in-p-apart-Γp (PTEHole w∈Δp) UBPEHole = refl
  unbound-in-p-apart-Γp (PTNEHole w∈Δp pt) (UBPNEHole ub) =
    unbound-in-p-apart-Γp pt ub
  unbound-in-p-apart-Γp PTWild UBPWild = refl

  dom-Γp-unbound-in : ∀{p τ ξ Γp Δp x T t} →
                      {{_ : UnboundIn T}} →
                      Δp ⊢ p :: τ [ ξ ]⊣ Γp →
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
                                    Γ1##Γ2 pt1 pt2)
                    (τ , x∈Γp)
                    (BDPPair bd1 bd2)
    with dom-union-part Γ1 Γ2 x τ x∈Γp
  ... | Inl x∈Γ1 = dom-Γp-unbound-in pt1 (τ , x∈Γ1) bd1
  ... | Inr x∈Γ2 = dom-Γp-unbound-in pt2 (τ , x∈Γ2) bd2
  dom-Γp-unbound-in (PTEHole w∈Δp) () BDPEHole
  dom-Γp-unbound-in (PTNEHole w∈Δp pt) x∈Γp (BDPNEHole bd) =
    dom-Γp-unbound-in pt x∈Γp bd

  -- (1, (3, 4))   (x, y)   x -> 1, y -> (3, 4)
  apart-Γp-unbound-in-p : ∀{p τ ξ Γp Δp x} →
                          Δp ⊢ p :: τ [ ξ ]⊣ Γp →
                          x # Γp →
                          unbound-in-p x p
  apart-Γp-unbound-in-p PTUnit x#Γp = UBPUnit
  apart-Γp-unbound-in-p PTNum x#Γp = UBPNum
  apart-Γp-unbound-in-p {τ = τ} {x = x} (PTVar {x = y}) x#Γp =
    UBPVar (apart-singleton-neq x#Γp)
  apart-Γp-unbound-in-p (PTInl pt) x#Γp =
    UBPInl (apart-Γp-unbound-in-p pt x#Γp)
  apart-Γp-unbound-in-p (PTInr pt) x#Γp =
    UBPInr (apart-Γp-unbound-in-p pt x#Γp)
  apart-Γp-unbound-in-p {x = x}
                        (PTPair {Γ1 = Γ1} {Γ2 = Γ2}
                                Γ1##Γ2 pt1 pt2)
                        x#Γp =
    UBPPair (apart-Γp-unbound-in-p pt1
                                   (apart-union-l Γ1 Γ2 x x#Γp))
            (apart-Γp-unbound-in-p pt2
                                   (apart-union-r Γ1 Γ2 x x#Γp))
  apart-Γp-unbound-in-p (PTEHole w∈Δp) x#Γp = UBPEHole
  apart-Γp-unbound-in-p (PTNEHole w∈Δp pt) x#Γp =
    UBPNEHole (apart-Γp-unbound-in-p pt x#Γp)
  apart-Γp-unbound-in-p PTWild x#Γp = UBPWild
  
  apart-Δp-hole-unbound-in-p : ∀{u p τ ξ Γp Δp} →
                               Δp ⊢ p :: τ [ ξ ]⊣ Γp →
                               u # Δp →
                               hole-unbound-in-p u p
  apart-Δp-hole-unbound-in-p PTUnit u#Δp = HUBPUnit
  apart-Δp-hole-unbound-in-p PTNum u#Δp = HUBPNum
  apart-Δp-hole-unbound-in-p PTVar u#Δp = HUBPVar
  apart-Δp-hole-unbound-in-p (PTInl pt) u#Δp =
    HUBPInl (apart-Δp-hole-unbound-in-p pt u#Δp)
  apart-Δp-hole-unbound-in-p (PTInr pt) u#Δp =
    HUBPInr (apart-Δp-hole-unbound-in-p pt u#Δp)
  apart-Δp-hole-unbound-in-p {u = u}
                             (PTPair Γ1##Γ2 pt1 pt2)
                             u#Δp =
    HUBPPair (apart-Δp-hole-unbound-in-p pt1 u#Δp)
             (apart-Δp-hole-unbound-in-p pt2 u#Δp)
  apart-Δp-hole-unbound-in-p {u = u}
                             (PTEHole {w = w} {τ = τ} w∈Δp)
                             u#Δp =
    HUBPEHole λ{refl → abort (some-not-none (! w∈Δp · u#Δp))}
  apart-Δp-hole-unbound-in-p {u = u}
                             (PTNEHole {w = w} {τ = τ} 
                                       w∈Δp pt)
                             u#Δp =
   HUBPNEHole (λ{refl → abort (some-not-none (! w∈Δp · u#Δp))})
              (apart-Δp-hole-unbound-in-p pt u#Δp)
  apart-Δp-hole-unbound-in-p PTWild u#Δp = HUBPWild

  mutual
    binders-fresh-r : ∀{Γ Δ Δp r τ1 ξ τ2 x} →
                      Γ , Δ , Δp ⊢ r :: τ1 [ ξ ]=> τ2 →
                      unbound-in-r x r →
                      x # Γ →
                      fresh-r x r
    binders-fresh-r {Γ = Γ} {x = x}
                    (RTRule {Γp = Γp} pt Γ##Γp wt)
                    (UBRule xubp xube) x#Γ =        
      FRule xubp
            (binders-fresh wt xube
              (apart-parts Γ Γp x x#Γ
                (unbound-in-p-apart-Γp pt xubp)))

    binders-fresh-rs : ∀{Γ Δ Δp rs τ1 ξ τ2 x} →
                       Γ , Δ , Δp ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                       unbound-in-rs x rs →
                       x # Γ →
                       fresh-rs x rs
    binders-fresh-rs (RTOneRule rt) (UBRules xubr _) x#Γ = 
      FRules (binders-fresh-r rt xubr x#Γ) FNoRules
    binders-fresh-rs (RTRules rt rst)
                     (UBRules xubr xubrs) x#Γ =
      FRules (binders-fresh-r rt xubr x#Γ)
             (binders-fresh-rs rst xubrs x#Γ)

    binders-fresh-σ : ∀{Γ Δ Δp σ Γ' x} →
                      Γ , Δ , Δp ⊢ σ :se: Γ' →
                      unbound-in-σ x σ →
                      x # Γ →
                      fresh-σ x σ
    binders-fresh-σ {Γ' = Γ'} {x = x} (STAId Γ'⊆Γ) UBσId x#Γ =
      FσId x#Γ'
      where
        x#Γ' : x # Γ'
        x#Γ' with Γ' x in Γ'x
        ... | Some τ =
          abort (some-not-none (! (Γ'⊆Γ x τ Γ'x) · x#Γ))
        ... | None = refl
    binders-fresh-σ {Γ = Γ} (STASubst st wt) (UBσSubst ub x≠y ubσ) x#Γ =
      FσSubst (binders-fresh wt ub x#Γ)
              x≠y
              (binders-fresh-σ st ubσ (neq-apart-extend Γ x≠y x#Γ))

    binders-fresh-θ : ∀{Γ Δ Δp θ Γ' x} →
                      Γ , Δ , Δp ⊢ θ :sl: Γ' →
                      unbound-in-θ x θ →
                      x # Γ →
                      fresh-θ x θ
    binders-fresh-θ STAEmpty ub x#Γ = FθEmpty
    binders-fresh-θ (STAExtend y#Γ wst wt)
                    (UBθExtend ubd x≠y ubθ) x#Γ =
      FθExtend (binders-fresh wt ubd x#Γ)
               x≠y
               (binders-fresh-θ wst ubθ x#Γ)
                      
    binders-fresh : ∀{Γ Δ Δp e τ x} →
                    Γ , Δ , Δp ⊢ e :: τ →
                    unbound-in x e →
                    x # Γ →
                    fresh x e
    binders-fresh TAUnit UBUnit x#Γ = FUnit
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
    binders-fresh (TAMatchZPre {r = p => d} wt (RTOneRule rt))
                  (UBMatch xube (UBZRules UBNoRules
                                          (UBRules ubr _))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules FNoRules
                      (FRules (binders-fresh-r rt ubr x#Γ)
                              FNoRules))
    binders-fresh (TAMatchZPre {r = p => d} wt (RTRules rt rst))
                  (UBMatch xube (UBZRules _ (UBRules ubr xubrs))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules FNoRules
                      (FRules (binders-fresh-r rt ubr x#Γ)
                              (binders-fresh-rs rst xubrs x#Γ)))
    binders-fresh (TAMatchNZPre wt fin pret (RTOneRule rt) ¬red)
                  (UBMatch xube
                           (UBZRules xubpre
                                     (UBRules xubr xubpost))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules (binders-fresh-rs pret xubpre x#Γ)
                      (FRules (binders-fresh-r rt xubr x#Γ)
                              FNoRules))
    binders-fresh (TAMatchNZPre wt fin pret
                                (RTRules rt postt) ¬red)
                  (UBMatch xube
                           (UBZRules xubpre
                                     (UBRules xubr xubpost))) x#Γ =
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
    binders-fresh (TAEHole u∈Δ st) (UBEHole ubσ) x#Γ =
      FEHole (binders-fresh-σ st ubσ x#Γ)
    binders-fresh (TANEHole u∈Δ st wt) (UBNEHole ubσ ub) x#Γ =
      FNEHole (binders-fresh-σ st ubσ x#Γ) (binders-fresh wt ub x#Γ)

  mutual
    hole-binders-fresh-r : ∀{Γ Δ Δp r τ1 ξ τ2 u} →
                           Γ , Δ , Δp ⊢ r :: τ1 [ ξ ]=> τ2 →
                           hole-unbound-in-r u r →
                           u # Δ →
                           hole-fresh-r u r
    hole-binders-fresh-r {Δ = Δ} {u = u}
                         (RTRule {Δp = Δp} pt Γ##Γp wt)
                         (HUBRule ubp ube) u#Δ =
      HFRule ubp
             (hole-binders-fresh wt ube u#Δ)

    hole-binders-fresh-rs : ∀{Γ Δ Δp rs τ1 ξ τ2 u} →
                            Γ , Δ , Δp ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                            hole-unbound-in-rs u rs →
                            u # Δ →
                            hole-fresh-rs u rs
    hole-binders-fresh-rs (RTOneRule rt) (HUBRules ubr _) u#Δ = 
      HFRules (hole-binders-fresh-r rt ubr u#Δ) HFNoRules
    hole-binders-fresh-rs (RTRules rt rst)
                     (HUBRules ubr ubrs) u#Δ =
      HFRules (hole-binders-fresh-r rt ubr u#Δ)
              (hole-binders-fresh-rs rst ubrs u#Δ)

    hole-binders-fresh-σ : ∀{Γ Δ Δp σ Γ' u} →
                           Γ , Δ , Δp ⊢ σ :se: Γ' →
                           hole-unbound-in-σ u σ →
                           u # Δ →
                           hole-fresh-σ u σ
    hole-binders-fresh-σ (STAId Γ⊆Γ') HUBσId u#Δ = HFσId
    hole-binders-fresh-σ (STASubst st wt) (HUBσSubst ub ubσ) u#Δ =
      HFσSubst (hole-binders-fresh wt ub u#Δ)
               (hole-binders-fresh-σ st ubσ u#Δ)
              
    hole-binders-fresh : ∀{Γ Δ Δp e τ u} →
                         Γ , Δ , Δp ⊢ e :: τ →
                         hole-unbound-in u e →
                         u # Δ →
                         hole-fresh u e
    hole-binders-fresh TAUnit HUBUnit u#Δ = HFUnit
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
    hole-binders-fresh (TAMatchZPre {r = p => d} wt (RTOneRule rt))
                       (HUBMatch ube
                                 (HUBZRules HUBNoRules (HUBRules ubr _)))
                       u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules HFNoRules
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 HFNoRules))
    hole-binders-fresh (TAMatchZPre {r = p => d} wt
                                    (RTRules rt rst))
                       (HUBMatch ube (HUBZRules _ (HUBRules ubr ubrs))) u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules HFNoRules
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 (hole-binders-fresh-rs rst ubrs u#Δ)))
    hole-binders-fresh (TAMatchNZPre wt fin pret
                                     (RTOneRule rt) ¬red)
                       (HUBMatch ube (HUBZRules ubpre (HUBRules ubr ubpost)))
                       u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules (hole-binders-fresh-rs pret ubpre u#Δ)
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 HFNoRules))
    hole-binders-fresh (TAMatchNZPre wt fin pret
                                     (RTRules rt postt) ¬red)
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
    hole-binders-fresh (TAEHole {u = u'} u'∈Δ st) (HUBEHole ubσ) u#Δ =
      HFEHole (λ{refl → some-not-none (! u'∈Δ · u#Δ)})
              (hole-binders-fresh-σ st ubσ u#Δ)
    hole-binders-fresh (TANEHole {u = u'} u'∈Δ st wt)
                       (HUBNEHole ubσ ub) u#Δ =
      HFNEHole (λ{refl → some-not-none (! u'∈Δ · u#Δ)})
               (hole-binders-fresh-σ st ubσ u#Δ)
               (hole-binders-fresh wt ub u#Δ)
                
