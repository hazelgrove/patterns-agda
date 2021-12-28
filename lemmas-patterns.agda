open import constraints-core
open import core
open import patterns-core
open import statics-core

module lemmas-patterns where
  pattern-constr-same-type : ∀{p τ ξ Γ Δ} →
                             p :: τ [ ξ ]⊣ Γ , Δ →
                             ξ :c: τ
  pattern-constr-same-type PTVar = CTTruth
  pattern-constr-same-type PTNum = CTNum
  pattern-constr-same-type (PTInl pt) =
    CTInl (pattern-constr-same-type pt)
  pattern-constr-same-type (PTInr pt) =
    CTInr (pattern-constr-same-type pt)
  pattern-constr-same-type (PTPair disj disjh pt1 pt2) =
    CTPair (pattern-constr-same-type pt1)
           (pattern-constr-same-type pt2)
  pattern-constr-same-type PTEHole = CTUnknown
  pattern-constr-same-type (PTNEHole pt x) = CTUnknown
  pattern-constr-same-type PTWild = CTTruth
                                 

  pattern-constr-pos : ∀{p τ ξ Γ Δ} →
                       p :: τ [ ξ ]⊣ Γ , Δ →
                       ξ possible
  pattern-constr-pos PTVar = PTruth
  pattern-constr-pos PTNum = PNum
  pattern-constr-pos (PTInl pt) =
    PInl (pattern-constr-pos pt)
  pattern-constr-pos (PTInr pt) =
    PInr (pattern-constr-pos pt)
  pattern-constr-pos (PTPair disj disjh pt1 pt2) =
    PPair (pattern-constr-pos pt1)
          (pattern-constr-pos pt2)
  pattern-constr-pos PTEHole = PUnknown
  pattern-constr-pos (PTNEHole pt x) = PUnknown
  pattern-constr-pos PTWild = PTruth

  constr-ref-pattern-ref : ∀{p τ ξ Γ Δ} →
                           p :: τ [ ξ ]⊣ Γ , Δ →
                           ξ xrefutable →
                           p refutable
  constr-ref-pattern-ref PTNum xref = RNum
  constr-ref-pattern-ref (PTInl pt) xref = RInl
  constr-ref-pattern-ref (PTInr pt) xref = RInr
  constr-ref-pattern-ref (PTPair disj disjh pt1 pt2) (RXPairL xref1) =
    RPairL (constr-ref-pattern-ref pt1 xref1)
  constr-ref-pattern-ref (PTPair disj disjh pt1 pt2) (RXPairR xref2) =
    RPairR (constr-ref-pattern-ref pt2 xref2)
  constr-ref-pattern-ref PTEHole xref = REHole
  constr-ref-pattern-ref (PTNEHole pt x) xref = RNEHole

  pattern-ref-constr-ref : ∀{p τ ξ Γ Δ} →
                           p :: τ [ ξ ]⊣ Γ , Δ →
                           p refutable →
                           ξ xrefutable
  pattern-ref-constr-ref PTNum ref = RXNum
  pattern-ref-constr-ref (PTInl pt) ref = RXInl
  pattern-ref-constr-ref (PTInr pt) ref = RXInr
  pattern-ref-constr-ref (PTPair disj disjh pt1 pt2) (RPairL ref1) =
    RXPairL (pattern-ref-constr-ref pt1 ref1)
  pattern-ref-constr-ref (PTPair disj disjh pt1 pt2) (RPairR ref2) =
    RXPairR (pattern-ref-constr-ref pt2 ref2)
  pattern-ref-constr-ref PTEHole ref = RXUnknown
  pattern-ref-constr-ref (PTNEHole pt x) ref = RXUnknown
