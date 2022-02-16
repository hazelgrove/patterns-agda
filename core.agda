open import List
open import Nat
open import Prelude
open import contexts

module core where
  -- types
  data htyp : Set where
    unit  : htyp
    num   : htyp
    _==>_ : htyp → htyp → htyp
    _⊕_   : htyp → htyp → htyp
    _⊠_   : htyp → htyp → htyp
    
  -- type constructors bind very tightly
  infixr 25  _==>_
  infixr 25 _⊕_
  infixr 25 _⊠_

  -- the type of type contexts, i.e., Γs in the judgements
  tctx : Set
  tctx = htyp ctx

  -- the type of hole contexts, i.e. Δs in the judgements.
  hctx : Set
  hctx = (htyp ctx × htyp) ctx

  -- the type of patten hole contexts, i.e. Δps in the judgements
  phctx : Set
  phctx = htyp ctx
  
  mutual
    -- patterns used for structural pattern matching
    data pattrn : Set where
      unit     : pattrn
      N        : Nat → pattrn
      X        : Nat → pattrn
      inl      : pattrn → pattrn
      inr      : pattrn → pattrn
      ⟨_,_⟩    : pattrn → pattrn → pattrn
      wild     : pattrn
      ⦇-⦈[_]   : Nat → pattrn
      ⦇⌜_⌟⦈[_] : pattrn → (Nat × htyp) → pattrn
    
    -- pattern matching rules
    data rule : Set where
      _=>_ : pattrn → ihexp → rule

    -- unzippered rules
    data rules : Set where
      nil : rules
      _/_ : rule → rules → rules

    -- zippered rules
    data zrules : Set where
      _/_/_ : rules → rule → rules → zrules

    -- substitution environments as used for hole closures
    data subst-env : Set where
      Id    : (Γ : tctx) → subst-env
      Subst : (d : ihexp) → (y : Nat) → subst-env → subst-env
    
    -- internal expressions
    data ihexp : Set where
      unit        : ihexp
      N           : Nat → ihexp
      X           : Nat → ihexp
      ·λ_·[_]_    : Nat → htyp → ihexp → ihexp
      _∘_         : ihexp → ihexp → ihexp
      inl         : htyp → ihexp → ihexp
      inr         : htyp → ihexp → ihexp
      match_·:_of : ihexp → htyp → zrules → ihexp
      ⟨_,_⟩       : ihexp → ihexp → ihexp
      fst         : ihexp → ihexp
      snd         : ihexp → ihexp
      ⦇-⦈⟨_⟩      : (Nat × subst-env) → ihexp
      ⦇⌜_⌟⦈⟨_⟩    : ihexp → (Nat × subst-env) → ihexp
 
