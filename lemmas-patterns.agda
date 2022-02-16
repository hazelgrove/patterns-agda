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
  pattern-constr-same-type PTUnit = CTTruth
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
                                 
  rules-constr-same-type : ∀{Δp rs τ ξ} →
                                     Δp ⊢ rs ::s τ [ ξ ] →
                                     ξ :c: τ
  rules-constr-same-type (RTOneRule pt) =
    pattern-constr-same-type pt
  rules-constr-same-type (RTRules pt rst) =
    CTOr (pattern-constr-same-type pt)
         (rules-constr-same-type rst)
  
  pattern-constr-pos : ∀{Δp p τ ξ Γ} →
                       Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                       ξ possible
  pattern-constr-pos PTUnit = PTruth
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

  -- the two rules typing judgement behave as expected
  rules-type-no-target : ∀{Γ Δ Δp rs τ ξ τ'} →
                         Γ , Δ , Δp ⊢ rs ::s τ [ ξ ]=> τ' →
                         Δp ⊢ rs ::s τ [ ξ ]
  rules-type-no-target {rs = (p => e) / nil}
                       (RTOneRule (RTRule pt Γ##Γp wt')) =
    RTOneRule pt
  rules-type-no-target (RTRules (RTRule pt Γ##Γp wt') rst) =
    RTRules pt (rules-type-no-target rst)

  -- judgemental and functional pointer erasure align
  rel◆er : (rs : zrules) →
           erase-r rs (rs ◆er)
  rel◆er (nil / r / rs) = ERZPre
  rel◆er ((r' / rs') / r / rs) = ERNZPre (rel◆er (rs' / r / rs))
  
  -- appending more rules to the end of a list of rules
  -- ∨+s the emitted constraints
  rules-erase-constr-no-target : ∀{rs-pre r rs-post rss Δp τ ξpre ξrest} →
                                 erase-r (rs-pre / r / rs-post) rss →
                                 Δp ⊢ rs-pre ::s τ [ ξpre ] →
                                 Δp ⊢ (r / rs-post) ::s τ [ ξrest ] →
                                 Δp ⊢ rss ::s τ [ ξpre ∨+ ξrest ]
  rules-erase-constr-no-target
    {rs-pre = (p => e) / nil} {r = r} {rs-post = rs-post}
    {Δp = Δp} {τ = τ} {ξpre = ξpre} {ξrest = ξrest}
    (ERNZPre ERZPre) (RTOneRule pt) restt =
    tr (λ qq → Δp ⊢ (p => e) / (r / rs-post) ::s τ [ qq ])
       (! (pattern-∨+ pt ξrest))
       (RTRules pt restt)
  rules-erase-constr-no-target
    {rs-pre = r' / (_ / _)}
    (ERNZPre (ERNZPre er)) (RTRules rt' rst') restt =
    RTRules rt' (rules-erase-constr-no-target (ERNZPre er) rst' restt)

  -- same as the above, but tracking the type of the target
  rules-erase-constr : ∀{rs-pre r rs-post rss Γ Δ Δp τ ξpre ξrest τ'} →
                       erase-r (rs-pre / r / rs-post) rss →
                       Γ , Δ , Δp ⊢ rs-pre ::s τ [ ξpre ]=> τ' →
                       Γ , Δ , Δp ⊢ (r / rs-post) ::s τ [ ξrest ]=> τ' →
                       Γ , Δ , Δp ⊢ rss ::s τ [ ξpre ∨+ ξrest ]=> τ'
  rules-erase-constr
    {rs-pre = (p => e) / nil} {r = r} {rs-post = rs-post}
    {Γ = Γ} {Δ = Δ} {Δp = Δp}
    {τ = τ} {ξpre = ξpre} {ξrest = ξrest} {τ' = τ'}
    (ERNZPre ERZPre)
    (RTOneRule (RTRule pt Γ##Γp wt')) restt =
    tr (λ qq → Γ , Δ , Δp ⊢ (p => e) / (r / rs-post) ::s τ [ qq ]=> τ')
       (! (pattern-∨+ pt ξrest))
       (RTRules (RTRule pt Γ##Γp wt') restt)
  rules-erase-constr
    {rs-pre = r' / (_ / _)}
    (ERNZPre (ERNZPre er))
    (RTRules (RTRule pt Γ##Γp wt') rst') restt =
    RTRules (RTRule pt Γ##Γp wt')
            (rules-erase-constr (ERNZPre er) rst' restt)
  
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
                        
  
