open import List
open import Nat
open import Prelude
open import contexts
open import constraints-core
open import core
open import substitution-env
open import value-judgements

module patterns-core where
  -- pointer erasure for pattern rules
  data erase-r : zrules → hrules → Set where
    ERZPre  : ∀{r rs} →
              erase-r (nil / r / rs) (r / rs)
    ERNZPre : ∀{r' rs' r rs er} →
              erase-r (rs' / r / rs) er →
              erase-r ((r' / rs') / r / rs) (r' / er)
  
  -- a pattern p is refutable
  data _refutable : (p : pattrn) → Set where
    RNum    : ∀{n} →
              (N n) refutable
    RInl    : ∀{p} →
              (inl p) refutable
    RInr    : ∀{p} →
              (inr p) refutable
    RPairL  : ∀{p1 p2} →
              p1 refutable →
              ⟨ p1 , p2 ⟩ refutable
    RPairR  : ∀{p1 p2} →
              p2 refutable →
              ⟨ p1 , p2 ⟩ refutable
    REHole  : ∀{w} →
              ⦇-⦈[ w ] refutable
    RNEHole : ∀{p w τ} →
              ⦇⌜ p ⌟⦈[ w , τ ] refutable

  -- e matches the pattern p, emitting the substitutions θ
  -- TODO : Do we need disjointness constraints here?
  data _▹_⊣_ : (e : ihexp) → (p : pattrn) → (θ : env) → Set where
    MNum  : ∀{n} →
            (N n) ▹ (N n) ⊣ Id ∅
    MVar  : ∀{e x} →
            e ▹ (X x) ⊣ Subst e x (Id ∅)
    MInl  : ∀{e τ p θ} →
            e ▹ p ⊣ θ →
            inl τ e ▹ inl p ⊣ θ
    MInr  : ∀{e τ p θ} →
            e ▹ p ⊣ θ →
            inr τ e ▹ inr p ⊣ θ
    MPair : ∀{e1 e2 p1 p2 θ1 θ2} →
            e1 ▹ p1 ⊣ θ1 →
            e2 ▹ p2 ⊣ θ2 →
            ⟨ e1 , e2 ⟩ ▹ ⟨ p1 , p2 ⟩ ⊣ (θ1 ⊎ θ2)
    MNotIntroPair : ∀{e p1 p2 θ1 θ2} →
                    e notintro →
                    fst e ▹ p1 ⊣ θ1 →
                    snd e ▹ p2 ⊣ θ2 →
                    e ▹ ⟨ p1 , p2 ⟩ ⊣ (θ1 ⊎ θ2)
    MWild : ∀{e} →
            e ▹ wild ⊣ Id ∅

  -- e may match p
  data _?▹_ : (e : ihexp) → (p : pattrn) → Set where
    MMNotIntro : ∀{e p} →
                 e notintro →
                 p refutable →
                 e ?▹ p
    MMInl      : ∀{e τ p} →
                 e ?▹ p →
                 inl τ e ?▹ inl p
    MMInr      : ∀{e τ p} →
                 e ?▹ p →
                 inr τ e ?▹ inr p
    MMPairL    : ∀{e1 e2 p1 p2 θ} →
                 e1 ?▹ p1 →
                 e2 ▹ p2 ⊣ θ →
                 ⟨ e1 , e2 ⟩ ?▹ ⟨ p1 , p2 ⟩
    MMPairR    : ∀{e1 e2 p1 p2 θ} →
                 e1 ▹ p1 ⊣ θ →
                 e2 ?▹ p2 →
                 ⟨ e1 , e2 ⟩ ?▹ ⟨ p1 , p2 ⟩
    MMPair     : ∀{e1 e2 p1 p2} →
                 e1 ?▹ p1 →
                 e2 ?▹ p2 →
                 ⟨ e1 , e2 ⟩ ?▹ ⟨ p1 , p2 ⟩
    MMEHole    : ∀{u p} →
                 ⦇-⦈[ u ] ?▹ p
    MMNEHole   : ∀{e u p} →
                 ⦇⌜ e ⌟⦈[ u ] ?▹ p
    
  -- e does not match p
  data _⊥▹_ : (e : ihexp) → (p : pattrn) → Set where
    NMNum   : ∀{n1 n2} →
              n1 ≠ n2 →
              (N n1) ⊥▹ (N n2)
    NMConfL : ∀{e τ p} →
              inr τ e ⊥▹ inl p
    NMConfR : ∀{e τ p} →
              inl τ e ⊥▹ inr p
    NMInl   : ∀{e τ p} →
              e ⊥▹ p →
              inl τ e ⊥▹ inl p
    NMInr   : ∀{e τ p} →
              e ⊥▹ p →
              inr τ e ⊥▹ inr p
    NMPairL : ∀{e1 e2 p1 p2} →
              e1 ⊥▹ p1 →
              ⟨ e1 , e2 ⟩ ⊥▹ ⟨ p1 , p2 ⟩
    NMPairR : ∀{e1 e2 p1 p2} →
              e2 ⊥▹ p2 →
              ⟨ e1 , e2 ⟩ ⊥▹ ⟨ p1 , p2 ⟩
    

  -- p is assigned type τ and emits constraint ξ, where Γ records
  -- assumptions about the type of free variables and Δ records
  -- assumptions about the type of pattern holes
  data _::_[_]⊣_,_ : (p : pattrn) → (τ : htyp) →
                     (ξ : constr) → (Γ : tctx) → (Δ : tctx) → Set where
    PTVar    : ∀{x τ} →
               X x :: τ [ ·⊤ ]⊣ ■ (x , τ) , ∅
    PTNum    : ∀{n} →
               N n :: num [ N n ]⊣ ∅ , ∅
    PTInl    : ∀{p τ1 τ2 ξ Γ Δ} →
               p :: τ1 [ ξ ]⊣ Γ , Δ →
               inl p :: (τ1 ⊕ τ2) [ inl ξ ]⊣ Γ , Δ
    PTInr    : ∀{p τ1 τ2 ξ Γ Δ} →
               p :: τ2 [ ξ ]⊣ Γ , Δ →
               inr p :: (τ1 ⊕ τ2) [ inr ξ ]⊣ Γ , Δ
    PTPair   : ∀{p1 p2 τ1 τ2 ξ1 ξ2 Γ1 Γ2 Δ1 Δ2} →
               Γ1 ## Γ2 →
               Δ1 ## Δ2 →
               p1 :: τ1 [ ξ1 ]⊣ Γ1 , Δ1 →
               p2 :: τ2 [ ξ2 ]⊣ Γ2 , Δ2 →
               ⟨ p1 , p2 ⟩ :: (τ1 ⊠ τ2) [ ⟨ ξ1 , ξ2 ⟩ ]⊣ (Γ1 ∪ Γ2) , (Δ1 ∪ Δ2)
    PTEHole  : ∀{w τ} →
               ⦇-⦈[ w ] :: τ [ ·? ]⊣ ∅ , ■ (w , τ)
    PTNEHole : ∀{p w τ τ' ξ Γ Δ} →
               p :: τ [ ξ ]⊣ Γ , Δ →
               w # Δ →
               ⦇⌜ p ⌟⦈[ w , τ ] :: τ' [ ·? ]⊣ Γ , (Δ ,, (w , τ))
    PTWild   : ∀{τ} →
               wild :: τ [ ·⊤ ]⊣ ∅ , ∅
    
