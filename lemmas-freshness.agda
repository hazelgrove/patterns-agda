open import Nat
open import Prelude
open import contexts
open import core
open import freshness
open import lemmas-disjointness
open import patterns-core

module lemmas-freshness where
  unbound-in-p-apart : ∀{p τ ξ Γp Δp x} →
                       p :: τ [ ξ ]⊣ Γp , Δp →
                       unbound-in-p x p →
                       x # Γp
  unbound-in-p-apart PTVar (UBPVar x≠y) = apart-singleton x≠y
  unbound-in-p-apart PTNum UBPNum = refl
  unbound-in-p-apart (PTInl pt) (UBPInl ub) = unbound-in-p-apart pt ub
  unbound-in-p-apart (PTInr pt) (UBPInr ub)  = unbound-in-p-apart pt ub
  unbound-in-p-apart {x = x}
                     (PTPair {Γ1 = Γ1} {Γ2 = Γ2} disj disjh pt1 pt2)
                     (UBPPair ub1 ub2) =
    apart-parts Γ1 Γ2 x
                (unbound-in-p-apart pt1 ub1)
                (unbound-in-p-apart pt2 ub2)
  unbound-in-p-apart PTEHole UBPEHole = refl
  unbound-in-p-apart (PTNEHole pt apt') (UBPNEHole ub) = unbound-in-p-apart pt ub
  unbound-in-p-apart PTWild UBPWild = refl

  apart-unbound-in-p : ∀{p τ ξ Γp Δp x} →
                       p :: τ [ ξ ]⊣ Γp , Δp →
                       x # Γp →
                       unbound-in-p x p
  apart-unbound-in-p {τ = τ} {x = x} (PTVar {x = y}) x#Γp =
    UBPVar (apart-noteq x y τ x#Γp)
  apart-unbound-in-p PTNum x#Γp = UBPNum
  apart-unbound-in-p (PTInl pt) x#Γp =
    UBPInl (apart-unbound-in-p pt x#Γp)
  apart-unbound-in-p (PTInr pt) x#Γp =
    UBPInr (apart-unbound-in-p pt x#Γp)
  apart-unbound-in-p {x = x} (PTPair {Γ1 = Γ1} {Γ2 = Γ2} Γ1##Γ2 Δ1##Δ2 pt1 pt2) x#Γp =
    UBPPair (apart-unbound-in-p pt1 (apart-union1 Γ1 Γ2 x x#Γp))
            (apart-unbound-in-p pt2 (apart-union2 Γ1 Γ2 x x#Γp))
  apart-unbound-in-p PTEHole x#Γp = UBPEHole
  apart-unbound-in-p (PTNEHole pt w#Δ) x#Γp =
    UBPNEHole (apart-unbound-in-p pt x#Γp)
  apart-unbound-in-p PTWild x#Γp = UBPWild
  
  hole-unbound-in-p-apart : ∀{u p τ ξ Γp Δp} →
                            p :: τ [ ξ ]⊣ Γp , Δp →
                            hole-unbound-in-p u p →
                            u # Δp
  hole-unbound-in-p-apart PTNum HUBPNum = refl
  hole-unbound-in-p-apart PTVar HUBPVar = refl
  hole-unbound-in-p-apart (PTInl pt) (HUBPInl hub) =
    hole-unbound-in-p-apart pt hub
  hole-unbound-in-p-apart (PTInr pt) (HUBPInr hub) =
    hole-unbound-in-p-apart pt hub
  hole-unbound-in-p-apart {u = u}
                          (PTPair {Δ1 = Δ1} {Δ2 = Δ2} disj disjh pt1 pt2)
                          (HUBPPair hub1 hub2) =
    apart-parts Δ1 Δ2 u
                (hole-unbound-in-p-apart pt1 hub1)
                (hole-unbound-in-p-apart pt2 hub2)
  hole-unbound-in-p-apart PTWild HUBPWild = refl
  hole-unbound-in-p-apart PTEHole (HUBPEHole u≠u') = apart-singleton u≠u'
  hole-unbound-in-p-apart {u = u} (PTNEHole pt apt')
                          (HUBPNEHole {u' = u'} u≠u' hub)
    with hole-unbound-in-p-apart pt hub
  ... | apt
    with natEQ u' u
  ... | Inl u'=u = abort (u≠u' (! u'=u))
  ... | Inr u'≠u = apt

  apart-hole-unbound-in-p : ∀{u p τ ξ Γp Δp} →
                            p :: τ [ ξ ]⊣ Γp , Δp →
                            u # Δp →
                            hole-unbound-in-p u p
  apart-hole-unbound-in-p PTVar u#Δp = HUBPVar
  apart-hole-unbound-in-p PTNum u#Δp = HUBPNum
  apart-hole-unbound-in-p (PTInl pt) u#Δp =
    HUBPInl (apart-hole-unbound-in-p pt u#Δp)
  apart-hole-unbound-in-p (PTInr pt) u#Δp =
    HUBPInr (apart-hole-unbound-in-p pt u#Δp)
  apart-hole-unbound-in-p {u = u} (PTPair {Δ1 = Δ1} {Δ2 = Δ2} Γ1##Γ2 Δ1##Δ2 pt1 pt2) u#Δp =
    HUBPPair (apart-hole-unbound-in-p pt1 (apart-union1 Δ1 Δ2 u u#Δp))
             (apart-hole-unbound-in-p pt2 (apart-union2 Δ1 Δ2 u u#Δp))
  apart-hole-unbound-in-p {u = u} (PTEHole {w = w} {τ = τ}) u#Δp =
    HUBPEHole (apart-noteq u w τ u#Δp)
  apart-hole-unbound-in-p {u = u} (PTNEHole {w = w} {τ = τ} {Δ = Δ} pt w#Δ) u#Δp =
    HUBPNEHole (apart-noteq u w τ (apart-union1 (■ (w , τ)) Δ u u#Δp))
               (apart-hole-unbound-in-p pt (apart-union2 (■ (w , τ)) Δ u u#Δp))
  apart-hole-unbound-in-p PTWild u#Δp = HUBPWild
  
  mutual
    max-var : ihexp → Nat
    max-var (N n) = 0
    max-var (X x) = x
    max-var (·λ x ·[ τ ] e) = max x (max-var e)
    max-var (e1 ∘ e2) = max (max-var e1) (max-var e2)
    max-var (inl τ e) = max-var e
    max-var (inr τ e) = max-var e
    max-var (match e rs) = max (max-var e) (max-var-zrs rs)
    max-var ⟨ e1 , e2 ⟩ = max (max-var e1) (max-var e2)
    max-var (fst e) = max-var e
    max-var (snd e) = max-var e
    max-var ⦇-⦈[ u ] = 0
    max-var ⦇⌜ e ⌟⦈[ u ] = max-var e

    max-var-p : pattrn → Nat
    max-var-p (N n) = 0
    max-var-p (X x) = x
    max-var-p (inl p) = max-var-p p
    max-var-p (inr p) = max-var-p p
    max-var-p ⟨ p1 , p2 ⟩ = max (max-var-p p1) (max-var-p p2)
    max-var-p wild = 0
    max-var-p ⦇-⦈[ w ] = 0
    max-var-p ⦇⌜ p ⌟⦈[ w , τ ] = max-var-p p
    
    max-var-r : rule → Nat
    max-var-r (p => e) = max (max-var-p p) (max-var e)

    max-var-rs : rules → Nat
    max-var-rs nil = 0
    max-var-rs (r / rs) = max (max-var-r r) (max-var-rs rs)

    max-var-zrs : zrules → Nat
    max-var-zrs (rs-pre / r / rs-post) =
      max (max (max-var-rs rs-pre) (max-var-r r))
          (max-var-rs rs-post)

  mutual
    max<-fresh : ∀{x e} →
                 (max-var e) < x →
                 fresh x e
    max<-fresh {e = N n} max<x = FNum
    max<-fresh {e = X x} max<x = FVar (flip (<→≠ max<x))
    max<-fresh {e = ·λ x ·[ τ ] e} max<x =
      FLam (flip (<→≠ (max<→arg1< max<x))) (max<-fresh (max<→arg2< max<x))
    max<-fresh {e = e1 ∘ e2} max<x =
      FAp (max<-fresh (max<→arg1< max<x)) (max<-fresh (max<→arg2< max<x))
    max<-fresh {e = inl τ e} max<x = FInl (max<-fresh max<x)
    max<-fresh {e = inr τ e} max<x = FInr (max<-fresh max<x)
    max<-fresh {e = match e rs} max<x =
      FMatch (max<-fresh (max<→arg1< max<x)) (max<-fresh-zrs (max<→arg2< max<x))
    max<-fresh {e = ⟨ e1 , e2 ⟩} max<x =
      FPair (max<-fresh (max<→arg1< max<x)) (max<-fresh (max<→arg2< max<x))
    max<-fresh {e = fst e} max<x = FFst (max<-fresh max<x)
    max<-fresh {e = snd e} max<x = FSnd (max<-fresh max<x)
    max<-fresh {e = ⦇-⦈[ u ]} max<x = FEHole
    max<-fresh {e = ⦇⌜ e ⌟⦈[ u ]} max<x = FNEHole (max<-fresh max<x)

    max<-unbound-in-p : ∀{x p} →
                        (max-var-p p) < x →
                        unbound-in-p x p
    max<-unbound-in-p {p = N n} max<x = UBPNum
    max<-unbound-in-p {p = X x} max<x = UBPVar (flip (<→≠ max<x))
    max<-unbound-in-p {p = inl p} max<x = UBPInl (max<-unbound-in-p max<x)
    max<-unbound-in-p {p = inr p} max<x = UBPInr (max<-unbound-in-p max<x)
    max<-unbound-in-p {p = ⟨ p1 , p2 ⟩} max<x =
      UBPPair (max<-unbound-in-p (max<→arg1< max<x))
              (max<-unbound-in-p (max<→arg2< max<x))
    max<-unbound-in-p {p = wild} max<x = UBPWild
    max<-unbound-in-p {p = ⦇-⦈[ w ]} max<x = UBPEHole
    max<-unbound-in-p {p = ⦇⌜ p ⌟⦈[ w , τ ]} max<x =
      UBPNEHole (max<-unbound-in-p max<x)

    max<-fresh-r : ∀{x r} →
                   (max-var-r r) < x →
                   fresh-r x r
    max<-fresh-r {r = p => e} max<x =
      FRule (max<-unbound-in-p (max<→arg1< max<x))
            (max<-fresh (max<→arg2< max<x))

    max<-fresh-rs : ∀{x rs} →
                    (max-var-rs rs) < x →
                    fresh-rs x rs
    max<-fresh-rs {rs = nil} max<x = FNoRules
    max<-fresh-rs {rs = r / rs} max<x =
      FRules (max<-fresh-r (max<→arg1< max<x)) (max<-fresh-rs (max<→arg2< max<x))

    max<-fresh-zrs : ∀{x zrs} →
                     (max-var-zrs zrs) < x →
                     fresh-zrs x zrs
    max<-fresh-zrs {zrs = rs-pre / r / rs-post} max<x =
      FZRules (max<-fresh-rs (max<→arg1< (max<→arg1< max<x)))
              (max<-fresh-r (max<→arg2< {m = max-var-rs rs-pre} {n = max-var-r r}
                            (max<→arg1< max<x)))
              (max<-fresh-rs (max<→arg2< max<x))
    
  exists-fresh : (e : ihexp) →
                 Σ[ x ∈ Nat ] (fresh x e)
  exists-fresh e = 1+ (max-var e) , max<-fresh (n<1+n (max-var e))
