open import List
open import Prelude
open import complete-constraints-core
open import constraints-core
open import contexts
open import core
open import patterns-core
open import result-judgements

module statics-core where
  mutual
    data _,_⊢_::_ : (Γ : tctx) → (Δ : tctx) →
                    (e : ihexp) → (τ : htyp) → Set where
      TANum        : ∀{Γ Δ n} →
                     Γ , Δ ⊢ (N n) :: num
      TAVar        : ∀{Γ x τ Δ} →
                     (x , τ) ∈ Γ →
                     Γ , Δ ⊢ (X x) :: τ
      TALam        : ∀{Γ x τ1 Δ e τ2} →
                     x # Γ →
                     (Γ ,, (x , τ1)) , Δ ⊢ e :: τ2 →
                     Γ , Δ ⊢ (·λ x ·[ τ1 ] e) :: (τ1 ==> τ2)
      TAAp         : ∀{Γ Δ e1 e2 τ τ2} →
                     Γ , Δ ⊢ e1 :: (τ2 ==> τ) →
                     Γ , Δ ⊢ e2 :: τ2 →
                     Γ , Δ ⊢ (e1 ∘ e2) :: τ
      TAInl        : ∀{Γ Δ e τ1 τ2} →
                     Γ , Δ ⊢ e :: τ1 →
                     Γ , Δ ⊢ inl τ2 e :: τ1 ⊕ τ2
      TAInr        : ∀{Γ Δ e τ1 τ2} →
                     Γ , Δ ⊢ e :: τ2 →
                     Γ , Δ ⊢ inr τ1 e :: τ1 ⊕ τ2        
      TAMatchZPre  : ∀{Γ Δ e τ τ' r rs ξ} →
                     Γ , Δ ⊢ e :: τ →
                     Γ , Δ ⊢ (r / rs) ::s τ [ ξ ]=> τ' →
                     Γ , Δ ⊢ match e (nil / r / rs) :: τ'
      TAMatchNZPre : ∀{Γ Δ e τ τ' rs-pre r rs-post ξpre ξrest} →
                     Γ , Δ ⊢ e :: τ →
                     e final →
                     Γ , Δ ⊢ rs-pre ::s τ [ ξpre ]=> τ' →
                     Γ , Δ ⊢ (r / rs-post) ::s τ [ ξrest ]=> τ' →
                     (e ⊧̇†? ξpre → ⊥) →
                     Γ , Δ ⊢ match e (rs-pre / r / rs-post) :: τ'
      TAPair       : ∀{Γ Δ e1 e2 τ1 τ2} →
                     Γ , Δ ⊢ e1 :: τ1 →
                     Γ , Δ ⊢ e2 :: τ2 →
                     Γ , Δ ⊢ ⟨ e1 , e2 ⟩ :: (τ1 ⊠ τ2)
      TAFst        : ∀{Γ Δ e τ1 τ2} →
                     Γ , Δ ⊢ e :: (τ1 ⊠ τ2) →
                     Γ , Δ ⊢ (fst e) :: τ1
      TASnd        : ∀{Γ Δ e τ1 τ2} →
                     Γ , Δ ⊢ e :: (τ1 ⊠ τ2) →
                     Γ , Δ ⊢ (snd e) :: τ2
      TAEHole      : ∀{Γ Δ u τ} →
                     (u , τ) ∈ Δ →
                     Γ , Δ ⊢ ⦇-⦈[ u ] :: τ
      TANEHole     : ∀{Γ Δ e τ' u τ} →
                     (u , τ) ∈ Δ →
                     Γ , Δ ⊢ e :: τ' →
                     Γ , Δ ⊢ ⦇⌜ e ⌟⦈[ u ] :: τ

    -- r transforms a final expression of type τ to a final expression
    -- of type τ', emitting constraint ξ
    data _,_⊢_::_[_]=>_ : (Γ : tctx) → (Δ : tctx) → (r : rule) →
                          (τ : htyp) → (ξ : constr) → (τ' : htyp) → Set where
      CTRule : ∀{p e τ τ' ξ Γ Γp Δ Δp} →
               p :: τ [ ξ ]⊣ Γp , Δp →
               Γ ## Γp →
               Δ ## Δp →
               (Γ ∪ Γp) , (Δ ∪ Δp) ⊢ e :: τ' →
               Γ , Δ ⊢ (p => e) :: τ [ ξ ]=> τ'

    -- rs transforms a final expression of type τ to a final expression
    -- of type τ', emitting constraint ξrs
    data _,_⊢_::s_[_]=>_ : (Γ : tctx) → (Δ : tctx) → (rs : rules) →
                           (τ : htyp) → (ξrs : constr) →
                           (τ' : htyp) → Set where
      CTOneRule : ∀{Γ Δ r τ ξr τ'} →
                  Γ , Δ ⊢ r :: τ [ ξr ]=> τ' →
                  Γ , Δ ⊢ (r / nil) ::s τ [ ξr ]=> τ' 
      CTRules   : ∀{Γ Δ r rs τ ξr ξrs τ'} →
                  Γ , Δ ⊢ r :: τ [ ξr ]=> τ' →
                  Γ , Δ ⊢ rs ::s τ [ ξrs ]=> τ' →
                  Γ , Δ ⊢ (r / rs) ::s τ [ ξr ∨ ξrs ]=> τ'

  -- ξ1 entails ξ2
  data _c⊧̇_ : (ξ1 : constr) → (ξ2 : constr) → Set where
    Entails : ∀{ξ1 ξ2 τ} →
              ξ1 :c: τ →
              ξ2 :c: τ →
              (∀{Δ e} →
               ∅ , Δ ⊢ e :: τ →
               e val →
               e ⊧̇†? ξ1 →
               e ⊧̇ ξ2) →
              ξ1 c⊧̇ ξ2

  -- ξ1 potentially entails ξ2
  data _c⊧̇†?_ : (ξ1 : constr) → (ξ2 : constr) → Set where
    PotEntails : ∀{ξ1 ξ2 τ} →
                 ξ1 :c: τ →
                 ξ2 :c: τ →
                 (∀{Δ e} →
                  ∅ , Δ ⊢ e :: τ →
                  e final →
                  e ⊧̇†? ξ1 →
                  e ⊧̇†? ξ2) →
                 ξ1 c⊧̇†? ξ2

  -- ξ1 entails ξ2
  data _cc⊧_ : (ξ1 : comp-constr) → (ξ2 : comp-constr) → Set where
    Entails : ∀{ξ1 ξ2 τ} →
              ξ1 :cc: τ →
              ξ2 :cc: τ →
              (∀{Δ e} →
               ∅ , Δ ⊢ e :: τ →
               e val →
               e ⊧ ξ1 →
               e ⊧ ξ2) →
              ξ1 cc⊧ ξ2

  -- rs is matched by expressions of type τ, emitting constraint ξrs.
  data _::s_[_] : (rs : rules) → (τ : htyp) → (ξrs : constr) → Set where
     CTOneRule : ∀{p e τ ξr Γp Δp} →
                 p :: τ [ ξr ]⊣ Γp , Δp →
                 ((p => e) / nil) ::s τ [ ξr ]
     CTRules   : ∀{p e rs τ ξr ξrs Γp Δp} →
                 p :: τ [ ξr ]⊣ Γp , Δp →
                 rs ::s τ [ ξrs ] →
                 ((p => e) / rs) ::s τ [ ξr ∨ ξrs ]
                 
  -- rs is matched by expressions of type τ, emitting constraint ξrs.
  -- moreover, ξrs does not entail ξpre, i.e., rs is non-redundant
  -- assuming ξpre denotes the constraint given by all previously
  -- considered patterns
  data _::s_[_nr/_] : (rs : rules) → (τ : htyp) →
                      (ξpre : constr) → (ξrs : constr) → Set where
     CTOneRule : ∀{p e τ ξpre ξr Γp Δp} →
                 p :: τ [ ξr ]⊣ Γp , Δp →
                 (ξr c⊧̇ ξpre → ⊥) →
                 ((p => e) / nil) ::s τ [ ξpre nr/ ξr ]
     CTRules   : ∀{p e rs τ ξpre ξr ξrs Γp Δp} →
                 p :: τ [ ξr ]⊣ Γp , Δp →
                 (ξr c⊧̇ ξpre → ⊥) →
                 rs ::s τ [ ξpre ∨ ξr nr/ ξrs ] →
                 ((p => e) / rs) ::s τ [ ξpre nr/ ξr ∨ ξrs ]

  -- every expression of the same type as rs matches or may
  -- match at least one rule in rs
  data _exhaustive : (rs : rules) → Set where
    EXRules : ∀{rs τ ξ} →
              rs ::s τ [ ξ ] →
              ·⊤ c⊧̇†? ξ →
              rs exhaustive

  -- no rule occurring in rs is redundant 
  data _nonredundant : (rs : rules) → Set where
    NRRules   : ∀{rs τ ξ} →
                rs ::s τ [ ·⊥ nr/ ξ ] →
                rs nonredundant

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
      AEXMatch  : ∀{e rsz rs} →
                  e all-exhaustive →
                  erase-r rsz rs →
                  rs exhaustive →
                  rs branches-all-exhaustive →
                  (match e rsz) all-exhaustive
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
      AEXEHole  : ∀{u} →
                  ⦇-⦈[ u ] all-exhaustive
      AEXNEHole : ∀{e u} →
                  e all-exhaustive →
                  ⦇⌜ e ⌟⦈[ u ] all-exhaustive

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
      ANRMatchZPre : ∀{e rsz rs} →
                     e all-nonredundant →
                     erase-r rsz rs →
                     rs nonredundant →
                     rs branches-all-nonredundant →
                     (match e rsz) all-nonredundant
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
      ANREHole     : ∀{u} →
                     ⦇-⦈[ u ] all-nonredundant
      ANRNEHole    : ∀{e u} →
                     e all-nonredundant →
                     ⦇⌜ e ⌟⦈[ u ] all-nonredundant

    -- for each rule p => e in rs, no match expression
    -- occurring in e contains redundant rules
    data _branches-all-nonredundant : (rs : rules) → Set where
      ANRNoRules : nil branches-all-nonredundant
      ANRRules   : ∀{p e rs} →
                   e all-nonredundant →
                   rs branches-all-nonredundant →
                   ((p => e) / rs) branches-all-nonredundant
