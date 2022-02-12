open import List
open import Nat
open import Prelude
open import complete-constraints-core
open import constraints-core
open import contexts
open import core
open import htyp-decidable
open import patterns-core
open import result-judgements

module statics-core where
  mutual
    -- substitution typing
    data _,_,_⊢_:s:_ : tctx → hctx → phctx →
                       env → tctx → Set where
      STAId    : ∀{Γ Δ Δp Γ'} →
                 ((x : Nat) (τ : htyp) →
                  (x , τ) ∈ Γ' →
                  (x , τ) ∈ Γ) →
                 Γ , Δ , Δp ⊢ Id Γ' :s: Γ'
      STASubst : ∀{Γ Δ Δp d y τ σ Γ'} →
                 (Γ ,, (y , τ)) , Δ , Δp ⊢ σ :s: Γ' →
                 Γ , Δ , Δp ⊢ d :: τ →
                 Γ , Δ , Δp ⊢ Subst d y σ :s: Γ'
                 
    data _,_,_⊢_::_ : (Γ : tctx) → (Δ : hctx) → (Δp : phctx) →
                      (e : ihexp) → (τ : htyp) → Set where
      TANum        : ∀{Γ Δ Δp n} →
                     Γ , Δ , Δp ⊢ (N n) :: num
      TAVar        : ∀{Γ x τ Δ Δp} →
                     (x , τ) ∈ Γ →
                     Γ , Δ , Δp ⊢ (X x) :: τ
      TALam        : ∀{Γ x τ1 Δ Δp e τ2} →
                     x # Γ →
                     (Γ ,, (x , τ1)) , Δ , Δp ⊢ e :: τ2 →
                     Γ , Δ , Δp ⊢ (·λ x ·[ τ1 ] e) :: (τ1 ==> τ2)
      TAAp         : ∀{Γ Δ Δp e1 e2 τ τ2} →
                     Γ , Δ , Δp ⊢ e1 :: (τ2 ==> τ) →
                     Γ , Δ , Δp ⊢ e2 :: τ2 →
                     Γ , Δ , Δp ⊢ (e1 ∘ e2) :: τ
      TAInl        : ∀{Γ Δ Δp e τ1 τ2} →
                     Γ , Δ , Δp ⊢ e :: τ1 →
                     Γ , Δ , Δp ⊢ inl τ2 e :: τ1 ⊕ τ2
      TAInr        : ∀{Γ Δ Δp e τ1 τ2} →
                     Γ , Δ , Δp ⊢ e :: τ2 →
                     Γ , Δ , Δp ⊢ inr τ1 e :: τ1 ⊕ τ2        
      TAMatchZPre  : ∀{Γ Δ Δp e τ τ' r rs ξ} →
                     Γ , Δ , Δp ⊢ e :: τ →
                     Γ , Δ , Δp ⊢ (r / rs) ::s τ [ ξ ]=> τ' →
                     Γ , Δ , Δp ⊢ match e ·: τ of (nil / r / rs) :: τ'
      TAMatchNZPre : ∀{Γ Δ Δp e τ τ' rs-pre r rs-post ξpre ξrest} →
                     Γ , Δ , Δp ⊢ e :: τ →
                     e final →
                     Γ , Δ , Δp ⊢ rs-pre ::s τ [ ξpre ]=> τ' →
                     Γ , Δ , Δp ⊢ (r / rs-post) ::s τ [ ξrest ]=> τ' →
                     (e ⊧̇†? ξpre → ⊥) →
                     Γ , Δ , Δp ⊢ match e ·: τ of (rs-pre / r / rs-post) :: τ'
      TAPair       : ∀{Γ Δ Δp e1 e2 τ1 τ2} →
                     Γ , Δ , Δp ⊢ e1 :: τ1 →
                     Γ , Δ , Δp ⊢ e2 :: τ2 →
                     Γ , Δ , Δp ⊢ ⟨ e1 , e2 ⟩ :: (τ1 ⊠ τ2)
      TAFst        : ∀{Γ Δ Δp e τ1 τ2} →
                     Γ , Δ , Δp ⊢ e :: (τ1 ⊠ τ2) →
                     Γ , Δ , Δp ⊢ (fst e) :: τ1
      TASnd        : ∀{Γ Δ Δp e τ1 τ2} →
                     Γ , Δ , Δp ⊢ e :: (τ1 ⊠ τ2) →
                     Γ , Δ , Δp ⊢ (snd e) :: τ2
      TAEHole      : ∀{Γ Δ Δp u σ Γ' τ} →
                     (u , (Γ' , τ)) ∈ Δ →
                     Γ , Δ , Δp ⊢ σ :s: Γ' →
                     Γ , Δ , Δp ⊢ ⦇-⦈⟨ u , σ ⟩ :: τ
      TANEHole     : ∀{Γ Δ Δp u σ Γ' τ e τ'} →
                     (u , (Γ' , τ)) ∈ Δ →
                     Γ , Δ , Δp ⊢ σ :s: Γ' →
                     Γ , Δ , Δp ⊢ e :: τ' → 
                     Γ , Δ , Δp ⊢ ⦇⌜ e ⌟⦈⟨ u , σ ⟩ :: τ

    -- r transforms a final expression of type τ to a final expression
    -- of type τ', emitting constraint ξ
    data _,_,_⊢_::_[_]=>_ : (Γ : tctx) → (Δ : hctx) → (Δp : phctx) →
                            (r : rule) → (τ : htyp) → (ξ : constr) →
                            (τ' : htyp) → Set where
      CTRule : ∀{Γ Δ Δp p e τ τ' ξ Γp} →
               Δp ⊢ p :: τ [ ξ ]⊣ Γp →
               Γ ## Γp →
               (Γ ∪ Γp) , Δ , Δp ⊢ e :: τ' →
               Γ , Δ , Δp ⊢ (p => e) :: τ [ ξ ]=> τ'

    -- rs transforms a final expression of type τ to a final
    -- expression of type τ', emitting constraint ξrs
    data _,_,_⊢_::s_[_]=>_ : (Γ : tctx) → (Δ : hctx) → (Δp : phctx) →
                             (rs : rules) → (τ : htyp) → (ξrs : constr) →
                             (τ' : htyp) → Set where
      CTOneRule : ∀{Γ Δ Δp r τ ξr τ'} →
                  Γ , Δ , Δp ⊢ r :: τ [ ξr ]=> τ' →
                  Γ , Δ , Δp ⊢ (r / nil) ::s τ [ ξr ]=> τ' 
      CTRules   : ∀{Γ Δ Δp r rs τ ξr ξrs τ'} →
                  Γ , Δ , Δp ⊢ r :: τ [ ξr ]=> τ' →
                  Γ , Δ , Δp ⊢ rs ::s τ [ ξrs ]=> τ' →
                  Γ , Δ , Δp ⊢ (r / rs) ::s τ [ ξr ∨ ξrs ]=> τ'

  -- substitution list typing
  -- since the e ▹ p ⊣ θ judgement is used for the dynamics and
  -- thus does not have typing information, it emits a list of
  -- substitutions θ rather than an actual substitution environment
  -- as used for holes. we then have a separate typing judgement
  -- for these substitution lists
  --
  -- the purpose of this typing is also somewhat different to that
  -- of substitution environments. an environment σ records a
  -- series of substitutions which are applied one after another,
  -- and the typing judgement Γ , Δ , Δp ⊢ σ :s: Γσ tells us that
  -- any term which is well-typed in Γσ will be well-typed in Γ after
  -- applying σ. contrastingly, a list of substitutions θ is supposed
  -- to indicate a set of substitutions applied "simultaneously"
  -- as emitted by a single pattern match. for this reason,
  -- we don't extend Γ to Γ ,, (y , τ) in the recursive part of
  -- STExtend. as well, we require that the type Γθ records all typing
  -- assumptions about substituted variables in θ, while substitution
  -- environment only requires that the Id Γ case records a subset thereof
  data _,_,_⊢_:ls:_ : tctx → hctx → phctx →
                      subst-list → tctx → Set where
      STAEmpty  : ∀{Γ Δ Δp} →
                  Γ , Δ , Δp ⊢ [] :ls: ∅
      STAExtend : ∀{Γ Δ Δp θ Γθ d τ y} →
                  y # Γ →
                  Γ , Δ , Δp ⊢ θ :ls: Γθ →
                  Γ , Δ , Δp ⊢ d :: τ →
                  Γ , Δ , Δp ⊢ ((d , τ , y) :: θ) :ls: (Γθ ,, (y , τ))
                 
  -- ξ1 entails ξ2
  data _c⊧̇_ : (ξ1 : constr) → (ξ2 : constr) → Set where
    Entails : ∀{ξ1 ξ2 τ} →
              ξ1 :c: τ →
              ξ2 :c: τ →
              (∀{Δ Δp e} →
               ∅ , Δ , Δp ⊢ e :: τ →
               e val →
               e ⊧̇†? ξ1 →
               e ⊧̇ ξ2) →
              ξ1 c⊧̇ ξ2

  -- ξ1 potentially entails ξ2
  data _c⊧̇†?_ : (ξ1 : constr) → (ξ2 : constr) → Set where
    PotEntails : ∀{ξ1 ξ2 τ} →
                 ξ1 :c: τ →
                 ξ2 :c: τ →
                 (∀{Δ Δp e} →
                  ∅ , Δ , Δp ⊢ e :: τ →
                  e final →
                  e ⊧̇†? ξ1 →
                  e ⊧̇†? ξ2) →
                 ξ1 c⊧̇†? ξ2

  -- ξ1 entails ξ2
  data _cc⊧_ : (ξ1 : comp-constr) → (ξ2 : comp-constr) → Set where
    Entails : ∀{ξ1 ξ2 τ} →
              ξ1 :cc: τ →
              ξ2 :cc: τ →
              (∀{Δ Δp e} →
               ∅ , Δ , Δp ⊢ e :: τ →
               e val →
               e ⊧ ξ1 →
               e ⊧ ξ2) →
              ξ1 cc⊧ ξ2

  -- rs is matched by expressions of type τ, emitting constraint ξrs.
  data _⊢_::s_[_] : (Δp : phctx) → (rs : rules) →
                    (τ : htyp) → (ξrs : constr) → Set where
     CTOneRule : ∀{Δp p e τ ξr Γp} →
                 Δp ⊢ p :: τ [ ξr ]⊣ Γp →
                 Δp ⊢ ((p => e) / nil) ::s τ [ ξr ]
     CTRules   : ∀{Δp p e rs τ ξr ξrs Γp} →
                 Δp ⊢ p :: τ [ ξr ]⊣ Γp →
                 Δp ⊢ rs ::s τ [ ξrs ] →
                 Δp ⊢ ((p => e) / rs) ::s τ [ ξr ∨ ξrs ]
                 
  -- rs is matched by expressions of type τ, emitting constraint ξrs.
  -- moreover, ξrs does not entail ξpre, i.e., rs is non-redundant
  -- assuming ξpre denotes the constraint given by all previously
  -- considered patterns
  data _⊢_::s_[_nr/_] : (Δp : phctx) → (rs : rules) → (τ : htyp) →
                        (ξpre : constr) → (ξrs : constr) → Set where
     CTOneRule : ∀{Δp p e τ ξpre ξr Γp} →
                 Δp ⊢ p :: τ [ ξr ]⊣ Γp →
                 (ξr c⊧̇ ξpre → ⊥) →
                 Δp ⊢ ((p => e) / nil) ::s τ [ ξpre nr/ ξr ]
     CTRules   : ∀{Δp p e rs τ ξpre ξr ξrs Γp} →
                 Δp ⊢ p :: τ [ ξr ]⊣ Γp →
                 (ξr c⊧̇ ξpre → ⊥) →
                 Δp ⊢ rs ::s τ [ ξpre ∨ ξr nr/ ξrs ] →
                 Δp ⊢ ((p => e) / rs) ::s τ [ ξpre nr/ ξr ∨ ξrs ]

  -- every expression of the same type as rs matches or may
  -- match at least one rule in rs
  data _exhaustive : (rs : rules) → Set where
    EXRules : ∀{Δp rs τ ξ} →
              Δp ⊢ rs ::s τ [ ξ ] →
              ·⊤ c⊧̇†? ξ →
              rs exhaustive

  -- no rule occurring in rs is redundant 
  data _nonredundant : (rs : rules) → Set where
    NRRules   : ∀{Δp rs τ ξ} →
                Δp ⊢ rs ::s τ [ ·⊥ nr/ ξ ] →
                rs nonredundant

  -- TODO: Should these be in a Δp ctx?
  mutual
    -- all match expressions occuring in e are exhaustive
    data _all-exhaustive : (e : ihexp) → Set where
      AEXNum    : ∀{n} →
                  (N n) all-exhaustive
      AEXVar    : ∀{x} →
                  (X x) all-exhaustive
      AEXLam    : ∀{x τ1 e} →
                  e all-exhaustive →
                  (·λ x ·[ τ1 ] e) all-exhaustive
      AEXAp     : ∀{e1 e2} →
                  e1 all-exhaustive →
                  e2 all-exhaustive →
                  (e1 ∘ e2) all-exhaustive
      AEXInl    : ∀{e τ2} →
                  e all-exhaustive →
                  (inl τ2 e) all-exhaustive
      AEXInr    : ∀{e τ1} →
                  e all-exhaustive →
                  (inr τ1 e) all-exhaustive        
      AEXMatch  : ∀{e τ rsz rs} →
                  e all-exhaustive →
                  erase-r rsz rs →
                  rs exhaustive →
                  rs branches-all-exhaustive →
                  (match e ·: τ of rsz) all-exhaustive
      AEXPair   : ∀{e1 e2} →
                  e1 all-exhaustive →
                  e2 all-exhaustive →
                  ⟨ e1 , e2 ⟩ all-exhaustive
      AEXFst    : ∀{e} →
                  e all-exhaustive →
                  (fst e) all-exhaustive
      AEXSnd    : ∀{e} →
                  e all-exhaustive →
                  (snd e) all-exhaustive
      AEXEHole  : ∀{u σ} →
                  ⦇-⦈⟨ u , σ ⟩ all-exhaustive
      AEXNEHole : ∀{e u σ} →
                  e all-exhaustive →
                  ⦇⌜ e ⌟⦈⟨ u , σ ⟩ all-exhaustive

    -- for each rule p => e in rs, all match expressions
    -- occurring in e are exhaustive
    data _branches-all-exhaustive : (rs : rules) → Set where
      AEXNoRules : nil branches-all-exhaustive
      AEXRules   : ∀{p e rs} →
                   e all-exhaustive →
                   rs branches-all-exhaustive →
                   ((p => e) / rs) branches-all-exhaustive
                
  mutual
    -- no match expression occurring in e contains redundant rules
    data _all-nonredundant : (e : ihexp) → Set where
      ANRNum       : ∀{n} →
                     (N n) all-nonredundant
      ANRVar       : ∀{x} →
                     (X x) all-nonredundant
      ANRLam       : ∀{x τ1 e} →
                     e all-nonredundant →
                     (·λ x ·[ τ1 ] e) all-nonredundant
      ANRAp        : ∀{e1 e2} →
                     e1 all-nonredundant →
                     e2 all-nonredundant →
                     (e1 ∘ e2) all-nonredundant
      ANRInl       : ∀{e τ2} →
                     e all-nonredundant →
                     (inl τ2 e) all-nonredundant
      ANRInr       : ∀{e τ1} →
                     e all-nonredundant →
                     (inr τ1 e) all-nonredundant        
      ANRMatchZPre : ∀{e τ rsz rs} →
                     e all-nonredundant →
                     erase-r rsz rs →
                     rs nonredundant →
                     rs branches-all-nonredundant →
                     (match e ·: τ of rsz) all-nonredundant
      ANRPair      : ∀{e1 e2} →
                     e1 all-nonredundant →
                     e2 all-nonredundant →
                     ⟨ e1 , e2 ⟩ all-nonredundant
      ANRFst       : ∀{e} →
                     e all-nonredundant →
                     (fst e) all-nonredundant
      ANRSnd       : ∀{e} →
                     e all-nonredundant →
                     (snd e) all-nonredundant
      ANREHole     : ∀{u σ} →
                     ⦇-⦈⟨ u , σ ⟩ all-nonredundant
      ANRNEHole    : ∀{e u σ} →
                     e all-nonredundant →
                     ⦇⌜ e ⌟⦈⟨ u , σ ⟩ all-nonredundant

    -- for each rule p => e in rs, no match expression
    -- occurring in e contains redundant rules
    data _branches-all-nonredundant : (rs : rules) → Set where
      ANRNoRules : nil branches-all-nonredundant
      ANRRules   : ∀{p e rs} →
                   e all-nonredundant →
                   rs branches-all-nonredundant →
                   ((p => e) / rs) branches-all-nonredundant
