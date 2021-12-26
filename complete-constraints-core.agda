open import Nat
open import Prelude
open import constraints-core
open import core

module complete-constraints-core where

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

  -- compute the dual of a constraint
  _◆d : comp-constr → comp-constr
  ·⊤ ◆d = ·⊥
  ·⊥ ◆d = ·⊤
  (N n) ◆d = N̸ n
  (N̸ n) ◆d = N n
  (inl ξ) ◆d = inl (ξ ◆d) ∨ inr ·⊤
  (inr ξ) ◆d = inr (ξ ◆d) ∨ inl ·⊤
  ⟨ ξ1 , ξ2 ⟩ ◆d = (⟨ ξ1 , ξ2 ◆d ⟩ ∨ ⟨ ξ1 ◆d , ξ2 ⟩) ∨ ⟨ ξ1 ◆d , ξ2 ◆d ⟩
  (ξ1 ∨ ξ2) ◆d = (ξ1 ◆d) ∧ (ξ2 ◆d)
  (ξ1 ∧ ξ2) ◆d = (ξ1 ◆d) ∨ (ξ2 ◆d)
  
  -- substitute ⊤ for ? in ξ
  _◆⊤ : constr → comp-constr
  ·⊤ ◆⊤ = ·⊤
  ·⊥ ◆⊤ = ·⊥
  ·? ◆⊤ = ·⊤
  (N n) ◆⊤ = N n
  (inl ξ) ◆⊤ = inl (ξ ◆⊤)
  (inr ξ) ◆⊤ = inr (ξ ◆⊤)
  ⟨ ξ1 , ξ2 ⟩ ◆⊤ = ⟨ ξ1 ◆⊤ , ξ2 ◆⊤ ⟩
  (ξ1 ∨ ξ2) ◆⊤ = (ξ1 ◆⊤) ∨ (ξ2 ◆⊤)

  -- substitute ⊥ for ? in ξ
  _◆⊥ : constr → comp-constr
  ·⊤ ◆⊥ = ·⊤
  ·⊥ ◆⊥ = ·⊥
  ·? ◆⊥ = ·⊥
  (N n) ◆⊥ = N n
  (inl ξ) ◆⊥ = inl (ξ ◆⊥)
  (inr ξ) ◆⊥ = inr (ξ ◆⊥)
  ⟨ ξ1 , ξ2 ⟩ ◆⊥ = ⟨ ξ1 ◆⊥ , ξ2 ◆⊥ ⟩
  (ξ1 ∨ ξ2) ◆⊥ = (ξ1 ◆⊥) ∨ (ξ2 ◆⊥)
