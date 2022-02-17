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
    -- type assignment
    -- 
    -- note that the on-paper version of this judgement includes 
    -- only a single Δ context for both expression and pattern holes,
    -- and it is clear from the context which is being considered.
    -- however, since expression holes require hole closures while
    -- pattern holes only require the type of the hole, we must
    -- explicitly separate this into two contexts Δ and Δp here.
    data _,_,_⊢_::_ : (Γ : tctx) → (Δ : hctx) → (Δp : phctx) →
                      (e : ihexp) → (τ : htyp) → Set where
      TAUnit       : ∀{Γ Δ Δp} →
                     Γ , Δ , Δp ⊢ unit :: unit
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
                     Γ , Δ , Δp ⊢
                       match e ·: τ of (nil / r / rs) :: τ'
      TAMatchNZPre : ∀{Γ Δ Δp e τ τ' rs-pre r rs-post ξpre ξrest} →
                     Γ , Δ , Δp ⊢ e :: τ →
                     e final →
                     Γ , Δ , Δp ⊢ rs-pre ::s τ [ ξpre ]=> τ' →
                     Γ , Δ , Δp ⊢ (r / rs-post) ::s τ [ ξrest ]=> τ' →
                     (e ⊧̇†? ξpre → ⊥) →
                     Γ , Δ , Δp ⊢
                       match e ·: τ of (rs-pre / r / rs-post) :: τ'
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
                     Γ , Δ , Δp ⊢ σ :se: Γ' →
                     Γ , Δ , Δp ⊢ ⦇-⦈⟨ u , σ ⟩ :: τ
      TANEHole     : ∀{Γ Δ Δp u σ Γ' τ e τ'} →
                     (u , (Γ' , τ)) ∈ Δ →
                     Γ , Δ , Δp ⊢ σ :se: Γ' →
                     Γ , Δ , Δp ⊢ e :: τ' → 
                     Γ , Δ , Δp ⊢ ⦇⌜ e ⌟⦈⟨ u , σ ⟩ :: τ

    -- substitution environment typing
    -- 
    -- typing for hole closures a la Hazelnut
    data _,_,_⊢_:se:_ : (Γ : tctx) → (Δ : hctx) → (Δp : phctx) →
                       (σ : subst-env) → (Γ' : tctx) → Set where
      STAId    : ∀{Γ Δ Δp Γ'} →
                 ((x : Nat) (τ : htyp) →
                  (x , τ) ∈ Γ' →
                  (x , τ) ∈ Γ) →
                 Γ , Δ , Δp ⊢ Id Γ' :se: Γ'
      STASubst : ∀{Γ Δ Δp d y τ σ Γ'} →
                 (Γ ,, (y , τ)) , Δ , Δp ⊢ σ :se: Γ' →
                 Γ , Δ , Δp ⊢ d :: τ →
                 Γ , Δ , Δp ⊢ Subst d y σ :se: Γ'

    -- rule typing
    --
    -- the rule r transforms a final expression of type τ to a
    -- final expression of type τ', emitting the constraint ξ
    data _,_,_⊢_::_[_]=>_ : (Γ : tctx) → (Δ : hctx) → (Δp : phctx) →
                            (r : rule) → (τ : htyp) → (ξ : constr) →
                            (τ' : htyp) → Set where
      RTRule : ∀{Γ Δ Δp p e τ τ' ξ Γp} →
               Δp ⊢ p :: τ [ ξ ]⊣ Γp →
               Γ ## Γp →
               (Γ ∪ Γp) , Δ , Δp ⊢ e :: τ' →
               Γ , Δ , Δp ⊢ (p => e) :: τ [ ξ ]=> τ'

    -- rules typing
    --
    -- the rules rs transform a final expression of type τ to a final
    -- expression of type τ', emitting constraint ξrs
    data _,_,_⊢_::s_[_]=>_ : (Γ : tctx) → (Δ : hctx) → (Δp : phctx) →
                             (rs : rules) → (τ : htyp) →
                             (ξrs : constr) → (τ' : htyp) → Set where
      RTOneRule : ∀{Γ Δ Δp r τ ξr τ'} →
                  Γ , Δ , Δp ⊢ r :: τ [ ξr ]=> τ' →
                  Γ , Δ , Δp ⊢ (r / nil) ::s τ [ ξr ]=> τ' 
      RTRules   : ∀{Γ Δ Δp r rs τ ξr ξrs τ'} →
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
  -- and the typing judgement Γ , Δ , Δp ⊢ σ :se: Γσ tells us that
  -- any term which is well-typed in Γσ will be well-typed in Γ after
  -- applying σ. contrastingly, a list of substitutions θ is supposed
  -- to indicate a set of substitutions applied "simultaneously"
  -- as emitted by a single pattern match. for this reason,
  -- we don't extend Γ to Γ ,, (y , τ) in the recursive part of
  -- STExtend. as well, we require that the type Γθ records all typing
  -- assumptions about substituted variables in θ, while substitution
  -- environment only requires that the Id Γ case records a subset thereof
  data _,_,_⊢_:sl:_ : tctx → hctx → phctx →
                      subst-list → tctx → Set where
      STAEmpty  : ∀{Γ Δ Δp} →
                  Γ , Δ , Δp ⊢ [] :sl: ∅
      STAExtend : ∀{Γ Δ Δp θ Γθ d τ y} →
                  y # Γ →
                  Γ , Δ , Δp ⊢ θ :sl: Γθ →
                  Γ , Δ , Δp ⊢ d :: τ →
                  Γ , Δ , Δp ⊢ ((d , τ , y) :: θ) :sl: (Γθ ,, (y , τ))
                 
  -- ξ1 entails ξ2
  --
  -- note that, while suppressed on paper, the definition of
  -- entailment assumes a fixed type assignent for ξ1 and ξ2.
  -- this is needed since we lack type unicity for contraints
  data _·:_c⊧̇_ : (ξ1 : constr) → (τ : htyp) →
                 (ξ2 : constr) → Set where
    Entails : ∀{ξ1 ξ2 τ} →
              ξ1 :c: τ →
              ξ2 :c: τ →
              (∀{Δ Δp e} →
               ∅ , Δ , Δp ⊢ e :: τ →
               e val →
               e ⊧̇†? ξ1 →
               e ⊧̇ ξ2) →
              ξ1 ·: τ c⊧̇ ξ2

  -- ξ1 potentially entails ξ2
  data _·:_c⊧̇†?_ : (ξ1 : constr) → (τ : htyp) →
                   (ξ2 : constr) → Set where
    PotEntails : ∀{ξ1 ξ2 τ} →
                 ξ1 :c: τ →
                 ξ2 :c: τ →
                 (∀{Δ Δp e} →
                  ∅ , Δ , Δp ⊢ e :: τ →
                  e final →
                  e ⊧̇†? ξ1 →
                  e ⊧̇†? ξ2) →
                 ξ1 ·: τ c⊧̇†? ξ2

  -- ξ1 entails ξ2, where ξ1 and ξ2 are complete constraints
  data _·:_cc⊧_ : (ξ1 : comp-constr) → (τ : htyp) →
                  (ξ2 : comp-constr) → Set where
    Entails : ∀{ξ1 ξ2 τ} →
              ξ1 :cc: τ →
              ξ2 :cc: τ →
              (∀{Δ Δp e} →
               ∅ , Δ , Δp ⊢ e :: τ →
               e val →
               e ⊧ ξ1 →
               e ⊧ ξ2) →
              ξ1 ·: τ cc⊧ ξ2

  -- rs is matched by expressions of type τ, emitting constraint ξrs.
  --
  -- this is similar to rules typing, but does not check the type
  -- of branches and does not require a typing context.
  data _⊢_::s_[_] : (Δp : phctx) → (rs : rules) →
                    (τ : htyp) → (ξrs : constr) → Set where
     RTOneRule : ∀{Δp p e τ ξr Γp} →
                 Δp ⊢ p :: τ [ ξr ]⊣ Γp →
                 Δp ⊢ ((p => e) / nil) ::s τ [ ξr ]
     RTRules   : ∀{Δp p e rs τ ξr ξrs Γp} →
                 Δp ⊢ p :: τ [ ξr ]⊣ Γp →
                 Δp ⊢ rs ::s τ [ ξrs ] →
                 Δp ⊢ ((p => e) / rs) ::s τ [ ξr ∨ ξrs ]
                 
  -- rs is matched by expressions of type τ, emitting constraint ξrs.
  -- moreover, ξrs does not entail ξpre, i.e., rs is non-redundant
  -- assuming ξpre denotes the constraint given by all previously
  -- considered patterns
  data _⊢_::s_[_nr/_] : (Δp : phctx) → (rs : rules) → (τ : htyp) →
                        (ξpre : constr) → (ξrs : constr) → Set where
     RTOneRule : ∀{Δp p e τ ξpre ξr Γp} →
                 Δp ⊢ p :: τ [ ξr ]⊣ Γp →
                 (ξr ·: τ c⊧̇ ξpre → ⊥) →
                 Δp ⊢ ((p => e) / nil) ::s τ [ ξpre nr/ ξr ]
     RTRules   : ∀{Δp p e rs τ ξpre ξr ξrs Γp} →
                 Δp ⊢ p :: τ [ ξr ]⊣ Γp →
                 (ξr ·: τ c⊧̇ ξpre → ⊥) →
                 Δp ⊢ rs ::s τ [ ξpre ∨ ξr nr/ ξrs ] →
                 Δp ⊢ ((p => e) / rs) ::s τ [ ξpre nr/ ξr ∨ ξrs ]

  mutual
    -- all match expressions occuring in e are exhaustive
    data _⊢_exhaustive : (Δp : phctx) → (e : ihexp) → Set where
      EXUnit       : ∀{Δp} →
                     Δp ⊢ unit exhaustive
      EXNum        : ∀{Δp n} →
                     Δp ⊢ (N n) exhaustive
      EXVar        : ∀{Δp x} →
                     Δp ⊢ (X x) exhaustive
      EXLam        : ∀{Δp x τ1 e} →
                     Δp ⊢ e exhaustive →
                     Δp ⊢ (·λ x ·[ τ1 ] e) exhaustive
      EXAp         : ∀{Δp e1 e2} →
                     Δp ⊢ e1 exhaustive →
                     Δp ⊢ e2 exhaustive →
                     Δp ⊢ (e1 ∘ e2) exhaustive
      EXInl        : ∀{Δp e τ2} →
                     Δp ⊢ e exhaustive →
                     Δp ⊢ (inl τ2 e) exhaustive
      EXInr        : ∀{Δp e τ1} →
                     Δp ⊢ e exhaustive →
                     Δp ⊢ (inr τ1 e) exhaustive
      EXMatchZPre  : ∀{Δp e τ r rs ξ} →
                     Δp ⊢ e exhaustive →
                     Δp ⊢ (r / rs) ::s τ [ ξ ] →
                     ·⊤ ·: τ c⊧̇†? ξ →
                     Δp ⊢ (r / rs) exhaustive-targets →
                     Δp ⊢ (match e ·: τ of (nil / r / rs)) exhaustive
      EXMatchNZPre : ∀{Δp e τ rs-pre r rs-post ξpre ξrest} →
                     Δp ⊢ e exhaustive →
                     Δp ⊢ rs-pre ::s τ [ ξpre ] →
                     Δp ⊢ (r / rs-post) ::s τ [ ξrest ] →
                     ·⊤ ·: τ c⊧̇†? (ξpre ∨ ξrest) →
                     Δp ⊢ rs-pre exhaustive-targets →
                     Δp ⊢ (r / rs-post) exhaustive-targets →
                     Δp ⊢ (match e ·: τ of (rs-pre / r / rs-post)) exhaustive
      EXPair       : ∀{Δp e1 e2} →
                     Δp ⊢ e1 exhaustive →
                     Δp ⊢ e2 exhaustive →
                     Δp ⊢ ⟨ e1 , e2 ⟩ exhaustive
      EXFst        : ∀{Δp e} →
                     Δp ⊢ e exhaustive →
                     Δp ⊢ (fst e) exhaustive
      EXSnd        : ∀{Δp e} →
                     Δp ⊢ e exhaustive →
                     Δp ⊢ (snd e) exhaustive
      EXEHole      : ∀{Δp u σ} →
                     Δp ⊢ σ exhaustive-σ →
                     Δp ⊢ ⦇-⦈⟨ u , σ ⟩ exhaustive
      EXNEHole     : ∀{Δp e u σ} →
                     Δp ⊢ σ exhaustive-σ →
                     Δp ⊢ e exhaustive →
                     Δp ⊢ ⦇⌜ e ⌟⦈⟨ u , σ ⟩ exhaustive

    -- for each substituted expression d in σ, all match expressions
    -- occurring in d are exhaustive
    data _⊢_exhaustive-σ : (Δp : phctx) → (σ : subst-env) → Set where
      EXσId    : ∀{Δp Γ} →
                 Δp ⊢ (Id Γ) exhaustive-σ
      EXσSubst : ∀{Δp d y σ} →
                 Δp ⊢ σ exhaustive-σ →
                 Δp ⊢ d exhaustive →
                 Δp ⊢ (Subst d y σ) exhaustive-σ

    -- for each substituted expression d in θ, all match expressions
    -- occurring in d are exhaustive
    data _⊢_exhaustive-θ : (Δp : phctx) → (θ : subst-list) → Set where
      NRθEmpty  : ∀{Δp} →
                  Δp ⊢ [] exhaustive-θ
      NRθExtend : ∀{Δp d τ y θ} →
                  Δp ⊢ θ exhaustive-θ →
                  Δp ⊢ d exhaustive →
                  Δp ⊢ ((d , τ , y) :: θ) exhaustive-θ

    -- for each rule p => e in rs, all match expressions
    -- occurring in e are exhaustive
    data _⊢_exhaustive-targets : (Δp : phctx) → (rs : rules) → Set where
      EXNoRules : ∀{Δp} →
                   Δp ⊢ nil exhaustive-targets
      EXRules   : ∀{Δp p e rs} →
                   Δp ⊢ e exhaustive →
                   Δp ⊢ rs exhaustive-targets →
                   Δp ⊢ ((p => e) / rs) exhaustive-targets

  mutual
    -- no match expression occurring in e contains redundant rules
    data _⊢_nonredundant : (Δp : phctx) → (e : ihexp) → Set where
      NRUnit       : ∀{Δp} →
                     Δp ⊢ unit nonredundant
      NRNum        : ∀{Δp n} →
                     Δp ⊢ (N n) nonredundant
      NRVar        : ∀{Δp x} →
                     Δp ⊢ (X x) nonredundant
      NRLam        : ∀{Δp x τ1 e} →
                     Δp ⊢ e nonredundant →
                     Δp ⊢ (·λ x ·[ τ1 ] e) nonredundant
      NRAp         : ∀{Δp e1 e2} →
                     Δp ⊢ e1 nonredundant →
                     Δp ⊢ e2 nonredundant →
                     Δp ⊢ (e1 ∘ e2) nonredundant
      NRInl        : ∀{Δp e τ2} →
                     Δp ⊢ e nonredundant →
                     Δp ⊢ (inl τ2 e) nonredundant
      NRInr        : ∀{Δp e τ1} →
                     Δp ⊢ e nonredundant →
                     Δp ⊢ (inr τ1 e) nonredundant
      NRMatchZPre  : ∀{Δp e τ r rs ξ} →
                     Δp ⊢ e nonredundant →
                     Δp ⊢ (r / rs) ::s τ [ ·⊥ nr/ ξ ] →
                     Δp ⊢ (r / rs) nonredundant-targets →
                     Δp ⊢ (match e ·: τ of (nil / r / rs)) nonredundant
      NRMatchNZPre : ∀{Δp e τ rs-pre r rs-post ξpre ξrest} →
                     Δp ⊢ e nonredundant →
                     Δp ⊢ rs-pre ::s τ [ ·⊥ nr/ ξpre ] →
                     Δp ⊢ (r / rs-post) ::s τ [ ·⊥ ∨ ξpre nr/ ξrest ] →
                     Δp ⊢ rs-pre nonredundant-targets →
                     Δp ⊢ (r / rs-post) nonredundant-targets →
                     Δp ⊢ (match e ·: τ of (rs-pre / r / rs-post)) nonredundant
      NRPair       : ∀{Δp e1 e2} →
                     Δp ⊢ e1 nonredundant →
                     Δp ⊢ e2 nonredundant →
                     Δp ⊢ ⟨ e1 , e2 ⟩ nonredundant
      NRFst        : ∀{Δp e} →
                     Δp ⊢ e nonredundant →
                     Δp ⊢ (fst e) nonredundant
      NRSnd        : ∀{Δp e} →
                     Δp ⊢ e nonredundant →
                     Δp ⊢ (snd e) nonredundant
      NREHole      : ∀{Δp u σ} →
                     Δp ⊢ ⦇-⦈⟨ u , σ ⟩ nonredundant
      NRNEHole     : ∀{Δp e u σ} →
                     Δp ⊢ e nonredundant →
                     Δp ⊢ ⦇⌜ e ⌟⦈⟨ u , σ ⟩ nonredundant

    -- for each substituted expression d in σ, no match expression
    -- occurring in d contains redundant rules
    data _⊢_nonredundant-σ : (Δp : phctx) → (σ : subst-env) → Set where
      NRσId    : ∀{Δp Γ} →
                 Δp ⊢ (Id Γ) nonredundant-σ
      NRσSubst : ∀{Δp d y σ} →
                 Δp ⊢ σ nonredundant-σ →
                 Δp ⊢ d nonredundant →
                 Δp ⊢ (Subst d y σ) nonredundant-σ

    -- for each substituted expression d in θ, no match expression
    -- occurring in d contains redundant rules
    data _⊢_nonredundant-θ : (Δp : phctx) → (θ : subst-list) → Set where
      NRθEmpty  : ∀{Δp} →
                  Δp ⊢ [] nonredundant-θ
      NRθExtend : ∀{Δp d τ y θ} →
                  Δp ⊢ θ nonredundant-θ →
                  Δp ⊢ d nonredundant →
                  Δp ⊢ ((d , τ , y) :: θ) nonredundant-θ
    
    -- for each rule p => e in rs, no match expression
    -- occurring in e contains redundant rules
    data _⊢_nonredundant-targets : (Δp : phctx) → (rs : rules) → Set where
      NRNoRules : ∀{Δp} →
                  Δp ⊢ nil nonredundant-targets
      NRRules   : ∀{Δp p e rs} →
                  Δp ⊢ e nonredundant →
                  Δp ⊢ rs nonredundant-targets →
                  Δp ⊢ ((p => e) / rs) nonredundant-targets
