open import Bool
open import Nat
open import Prelude
open import core
open import value-result-judgements

module constraints-core where
  -- incomplete match constraints
  data constr : Set where
    ·⊤    : constr
    ·⊥    : constr
    ·?    : constr
    N     : Nat → constr
    inl   : constr → constr
    inr   : constr → constr
    ⟨_,_⟩ : constr → constr → constr
    _∨_   : constr → constr → constr

  -- ξ constrains final expressions of type τ
  data _:c:_ : (ξ : constr) → (τ : htyp) → Set where
    CTTruth   : ∀{τ} →
                ·⊤ :c: τ
    CTFalsity : ∀{τ} →
                ·⊥ :c: τ
    CTUnknown : ∀{τ} →
                ·? :c: τ
    CTNum     : ∀{n} →
                N n :c: num
    CTInl     : ∀{ξ τ1 τ2} →
                ξ :c: τ1 →
                inl ξ :c: τ1 ⊕ τ2
    CTInr     : ∀{ξ τ1 τ2} →
                ξ :c: τ2 →
                inr ξ :c: τ1 ⊕ τ2
    CTPair    : ∀{ξ1 ξ2 τ1 τ2} →
                ξ1 :c: τ1 →
                ξ2 :c: τ2 →
                ⟨ ξ1 , ξ2 ⟩ :c: τ1 ⊠ τ2
    CTOr      : ∀{ξ1 ξ2 τ} →
                ξ1 :c: τ →
                ξ2 :c: τ →
                (ξ1 ∨ ξ2) :c: τ

  -- ξ is refutable
  data _xrefutable : (ξ : constr) → Set where
    RXUnknown : ·? xrefutable
    RXFalsity : ·⊥ xrefutable
    RXNum     : ∀{n} →
                (N n) xrefutable
    RXInl     : ∀{ξ} →
                (inl ξ) xrefutable
    RXInr     : ∀{ξ} →
                (inr ξ) xrefutable
    RXPairL   : ∀{ξ1 ξ2} →
                ξ1 xrefutable →
                ⟨ ξ1 , ξ2 ⟩ xrefutable
    RXPairR   : ∀{ξ1 ξ2} →
                ξ2 xrefutable →
                ⟨ ξ1 , ξ2 ⟩ xrefutable
    RXOr      : ∀{ξ1 ξ2} →
                ξ1 xrefutable →
                ξ2 xrefutable →
                (ξ1 ∨ ξ2) xrefutable
              
  data _possible : (ξ : constr) → Set where
    PTruth   : ·⊤ possible
    PUnknown : ·? possible
    PNum     : ∀{n} →
               (N n) possible
    PInl     : ∀{e} →
               e possible →
               (inl e) possible
    PInr     : ∀{e} →
               e possible →
               (inr e) possible
    PPair     : ∀{e1 e2} →
               e1 possible →
               e2 possible →
               ⟨ e1 , e2 ⟩ possible
    POrL     : ∀{e1 e2} →
               e1 possible →
               (e1 ∨ e2) possible
    POrR     : ∀{e1 e2} →
               e2 possible →
               (e1 ∨ e2) possible

  
  -- e satisfies ξ
  data _⊧̇_ : (e : ihexp) → (ξ : constr) → Set where
    CSTruth : ∀{e} →
              e ⊧̇ ·⊤
    CSNum   : ∀{n} →
              (N n) ⊧̇ (N n)
    CSInl   : ∀{e τ ξ} →
              e ⊧̇ ξ →
              (inl τ e) ⊧̇ (inl ξ)
    CSInr   : ∀{e τ ξ} →
              e ⊧̇ ξ →
              (inr τ e) ⊧̇ (inr ξ)
    CSPair  : ∀{e1 e2 ξ1 ξ2} →
              e1 ⊧̇ ξ1 →
              e2 ⊧̇ ξ2 →
              ⟨ e1 , e2 ⟩ ⊧̇ ⟨ ξ1 , ξ2 ⟩
    CSNotIntroPair : ∀{e ξ1 ξ2} →
                     e notintro →
                     fst e ⊧̇ ξ1 →
                     snd e ⊧̇ ξ2 →
                     e ⊧̇ ⟨ ξ1 , ξ2 ⟩
    CSOrL   : ∀{e ξ1 ξ2} →
              e ⊧̇ ξ1 →
              e ⊧̇ (ξ1 ∨ ξ2)
    CSOrR   : ∀{e ξ1 ξ2} →
              e ⊧̇ ξ2 →
              e ⊧̇ (ξ1 ∨ ξ2)

  -- e may satisfy ξ
  data _⊧̇?_ : (e : ihexp) → (ξ : constr) → Set where
    CMSUnknown  : ∀{e} →
                  e ⊧̇? ·?
    CMSInl      : ∀{e τ ξ} →
                  e ⊧̇? ξ →
                  inl τ e ⊧̇? inl ξ
    CMSInr      : ∀{e τ ξ} →
                  e ⊧̇? ξ →
                  inr τ e ⊧̇? inr ξ
    CMSPairL    : ∀{e1 e2 ξ1 ξ2} →
                  e1 ⊧̇? ξ1 →
                  e2 ⊧̇ ξ2 →
                  ⟨ e1 , e2 ⟩ ⊧̇? ⟨ ξ1 , ξ2 ⟩
    CMSPairR    : ∀{e1 e2 ξ1 ξ2} →
                  e1 ⊧̇ ξ1 →
                  e2 ⊧̇? ξ2 →
                  ⟨ e1 , e2 ⟩ ⊧̇? ⟨ ξ1 , ξ2 ⟩
    CMSPair     : ∀{e1 e2 ξ1 ξ2} →
                  e1 ⊧̇? ξ1 →
                  e2 ⊧̇? ξ2 →
                  ⟨ e1 , e2 ⟩ ⊧̇? ⟨ ξ1 , ξ2 ⟩
    CMSOrL      : ∀{e ξ1 ξ2} →
                  e ⊧̇? ξ1 →
                  (e ⊧̇ ξ2 → ⊥) →
                  e ⊧̇? (ξ1 ∨ ξ2)
    CMSOrR      : ∀{e ξ1 ξ2} →
                  (e ⊧̇ ξ1 → ⊥) →
                  e ⊧̇? ξ2 →
                  e ⊧̇? (ξ1 ∨ ξ2)
    CMSNotIntro : ∀{e ξ} →
                  e notintro →
                  ξ xrefutable →
                  ξ possible →
                  e ⊧̇? ξ
  
  -- e satisfies or may satisfy ξ
  data _⊧̇†?_ : (e : ihexp) → (ξ : constr) → Set where
    CSMSSat : ∀{e ξ} →
              e ⊧̇ ξ →
              e ⊧̇†? ξ
    CSMSMay : ∀{e ξ} →
              e ⊧̇? ξ →
              e ⊧̇†? ξ

  -- complete match constraints
  data comp-constr : Set where
    ·⊤    : comp-constr
    ·⊥    : comp-constr
    N     : Nat → comp-constr
    N̸     : Nat → comp-constr
    inl   : comp-constr → comp-constr
    inr   : comp-constr → comp-constr
    ⟨_,_⟩ : comp-constr → comp-constr → comp-constr
    _∨_   : comp-constr → comp-constr → comp-constr
    _∧_   : comp-constr → comp-constr → comp-constr

  -- ξ constrains final expressions of type τ
  data _:cc:_ : (ξ : comp-constr) → (τ : htyp) → Set where
    CTTruth   : ∀{τ} →
                ·⊤ :cc: τ
    CTFalsity : ∀{τ} →
                ·⊥ :cc: τ
    CTNum     : ∀{n} →
                N n :cc: num
    CTNotNum  : ∀{n} →
                N̸ n :cc: num
    CTInl     : ∀{ξ τ1 τ2} →
                ξ :cc: τ1 →
                inl ξ :cc: τ1 ⊕ τ2
    CTInr     : ∀{ξ τ1 τ2} →
                ξ :cc: τ2 →
                inr ξ :cc: τ1 ⊕ τ2
    CTPair    : ∀{ξ1 ξ2 τ1 τ2} →
                ξ1 :cc: τ1 →
                ξ2 :cc: τ2 →
                ⟨ ξ1 , ξ2 ⟩ :cc: τ1 ⊠ τ2
    CTOr      : ∀{ξ1 ξ2 τ} →
                ξ1 :cc: τ →
                ξ2 :cc: τ →
                (ξ1 ∨ ξ2) :cc: τ
    CTAnd     : ∀{ξ1 ξ2 τ} →
                ξ1 :cc: τ →
                ξ2 :cc: τ →
                (ξ1 ∧ ξ2) :cc: τ

  -- e satisfies ξ
  data _⊧_ : (e : ihexp) → (ξ : comp-constr) → Set where
    CSTruth  : ∀{e} →
               e ⊧ ·⊤
    CSNum    : ∀{n} →
               (N n) ⊧ (N n)
    CSNotNum : ∀{n1 n2} →
               n1 ≠ n2 →
               (N n1) ⊧ (N̸ n2)
    CSInl    : ∀{e τ ξ} →
               e ⊧ ξ →
               (inl τ e) ⊧ (inl ξ)
    CSInr    : ∀{e τ ξ} →
               e ⊧ ξ →
               (inr τ e) ⊧ (inr ξ)
    CSPair   : ∀{e1 e2 ξ1 ξ2} →
               e1 ⊧ ξ1 →
               e2 ⊧ ξ2 →
               ⟨ e1 , e2 ⟩ ⊧ ⟨ ξ1 , ξ2 ⟩
    CSOrL    : ∀{e ξ1 ξ2} →
               e ⊧ ξ1 →
               e ⊧ (ξ1 ∨ ξ2)
    CSOrR    : ∀{e ξ1 ξ2} →
               e ⊧ ξ2 →
               e ⊧ (ξ1 ∨ ξ2)
    CSAnd    : ∀{e ξ1 ξ2} →
               e ⊧ ξ1 →
               e ⊧ ξ2 →
               e ⊧ (ξ1 ∧ ξ2)
   

