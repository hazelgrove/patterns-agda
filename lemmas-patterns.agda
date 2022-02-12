open import List
open import Prelude
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import htyp-decidable
open import lemmas-contexts
open import lemmas-or-append
open import patterns-core
open import result-judgements
open import statics-core

module lemmas-patterns where  
  pattern-constr-same-type : ∀{Δp p τ ξ Γ} →
                             Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                             ξ :c: τ
  pattern-constr-same-type PTVar = CTTruth
  pattern-constr-same-type PTNum = CTNum
  pattern-constr-same-type (PTInl pt) =
    CTInl (pattern-constr-same-type pt)
  pattern-constr-same-type (PTInr pt) =
    CTInr (pattern-constr-same-type pt)
  pattern-constr-same-type (PTPair disj pt1 pt2) =
    CTPair (pattern-constr-same-type pt1)
           (pattern-constr-same-type pt2)
  pattern-constr-same-type (PTEHole w∈Δp) = CTUnknown
  pattern-constr-same-type (PTNEHole w∈Δp pt) = CTUnknown
  pattern-constr-same-type PTWild = CTTruth
                                 

  pattern-constr-pos : ∀{Δp p τ ξ Γ} →
                       Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                       ξ possible
  pattern-constr-pos PTVar = PTruth
  pattern-constr-pos PTNum = PNum
  pattern-constr-pos (PTInl pt) =
    PInl (pattern-constr-pos pt)
  pattern-constr-pos (PTInr pt) =
    PInr (pattern-constr-pos pt)
  pattern-constr-pos (PTPair disj pt1 pt2) =
    PPair (pattern-constr-pos pt1)
          (pattern-constr-pos pt2)
  pattern-constr-pos (PTEHole w∈Δp) = PUnknown
  pattern-constr-pos (PTNEHole w∈Δp pt) = PUnknown
  pattern-constr-pos PTWild = PTruth

  constr-ref-pattern-ref : ∀{Δp p τ ξ Γ} →
                           Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                           ξ xrefutable →
                           p refutable
  constr-ref-pattern-ref PTNum xref = RNum
  constr-ref-pattern-ref (PTInl pt) xref = RInl
  constr-ref-pattern-ref (PTInr pt) xref = RInr
  constr-ref-pattern-ref (PTPair disj pt1 pt2) (RXPairL xref1) =
    RPairL (constr-ref-pattern-ref pt1 xref1)
  constr-ref-pattern-ref (PTPair disj pt1 pt2) (RXPairR xref2) =
    RPairR (constr-ref-pattern-ref pt2 xref2)
  constr-ref-pattern-ref (PTEHole w∈Δp) xref = REHole
  constr-ref-pattern-ref (PTNEHole w∈Δp pt) xref = RNEHole

  pattern-ref-constr-ref : ∀{Δp p τ ξ Γ} →
                           Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                           p refutable →
                           ξ xrefutable
  pattern-ref-constr-ref PTNum ref = RXNum
  pattern-ref-constr-ref (PTInl pt) ref = RXInl
  pattern-ref-constr-ref (PTInr pt) ref = RXInr
  pattern-ref-constr-ref (PTPair disj pt1 pt2) (RPairL ref1) =
    RXPairL (pattern-ref-constr-ref pt1 ref1)
  pattern-ref-constr-ref (PTPair disj pt1 pt2) (RPairR ref2) =
    RXPairR (pattern-ref-constr-ref pt2 ref2)
  pattern-ref-constr-ref (PTEHole w∈Δp) ref = RXUnknown
  pattern-ref-constr-ref (PTNEHole w∈Δp pt) ref = RXUnknown

  -- appending a rule to the end of a list of rules
  -- ∨+s the emitted constraints
  rs-constr-append : ∀{rs r rss Γ Δ Δp τ ξrs ξr τ'} →
                     erase-r (rs / r / nil) rss →
                     Γ , Δ , Δp ⊢ rs ::s τ [ ξrs ]=> τ' →
                     Γ , Δ , Δp ⊢ r :: τ [ ξr ]=> τ' →
                     Γ , Δ , Δp ⊢ rss ::s τ [ ξrs ∨+ ξr ]=> τ'
  rs-constr-append {rs = r' / .nil} {r = r} {ξr = ξr}
                 (ERNZPre {er = _ / nil} ERZPre)
                 (CTOneRule (CTRule pt Γ##Γp wt'))
                 rt rewrite (pattern-∨+ pt ξr) =
    CTRules (CTRule pt Γ##Γp wt') (CTOneRule rt)
  rs-constr-append {rs = r' / .(_ / _)}
                 (ERNZPre (ERNZPre er)) (CTRules rt' rst') rt =
    CTRules rt' (rs-constr-append (ERNZPre er) rst' rt)

  notintro-mat-ref-not : ∀{e τ p θ} →
                         e notintro →
                         e ·: τ ▹ p ⊣ θ →
                         p refutable →
                         ⊥
  notintro-mat-ref-not NVAp (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVAp (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
  notintro-mat-ref-not NVMatch (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVMatch (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
  notintro-mat-ref-not NVFst (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVFst (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
  notintro-mat-ref-not NVSnd (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVSnd (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
  notintro-mat-ref-not NVEHole (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVEHole (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
  notintro-mat-ref-not NVNEHole (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVNEHole (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
                        
  
