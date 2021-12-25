open import Prelude
open import complete-constraints-core

-- duality of complete constraints is defined in the paper as a function
-- on complete constraints. because of the particular encoding of all the
-- judgments as datatypes and the agda semantics for pattern matching, it
-- is sometimes also convenient to have a judgemental form of duality. 
--
-- the core file gives the obvious encoding, viewing this function as a
-- jugement relating input and output as a datatype. this file argues that
-- this encoding is correct by showing a isomorphism with the function.
-- we also show tha,t as a corollary, the judgement is well moded at (∀, ∃!),
-- which is unsurprising if the jugement is written correctly.
--
-- taken together, these proofs allow us to move between the judgemental
-- form of duality and the function form when it's convenient.
--
-- while we do not have it, the argument given here is sufficiently strong
-- to produce an equality between these things in a system with the
-- univalence axiom, as described in the homotopy type theory book and the
-- associated work done in agda.
module judgemental-dual where
  --duality as a function, as written in the paper
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

  -- move from the judgmental form to the function form
  dual◆ : ∀{ξ ξbar} →
          dual ξ ξbar →
          (ξ ◆d == ξbar)
  dual◆ CDTruth = refl
  dual◆ CDFalsity = refl
  dual◆ CDNum = refl
  dual◆ CDNotNum = refl
  dual◆ (CDInl du) = ap1 (λ x → inl x ∨ inr ·⊤) (dual◆ du)
  dual◆ (CDInr du) = ap1 (λ x → inr x ∨ inl ·⊤) (dual◆ du)
  dual◆ (CDPair {ξ1 = ξ1} {ξ1bar = ξ1bar} {ξ2 = ξ2} {ξ2bar = ξ2bar} du1 du2) =
    (ap1 (λ x → (⟨ ξ1 , ξ2 ◆d ⟩ ∨ ⟨ x , ξ2 ⟩) ∨ ⟨ x , ξ2 ◆d ⟩) (dual◆ du1)) ·
    (ap1 (λ x → (⟨ ξ1 , x ⟩ ∨ ⟨ ξ1bar , ξ2 ⟩) ∨ ⟨ ξ1bar , x ⟩) (dual◆ du2))
  dual◆ (CDOr {ξ1 = ξ1} {ξ1bar = ξ1bar} {ξ2 = ξ2} {ξ2bar = ξ2bar} du1 du2) =
    (ap1 (λ x → (ξ1 ◆d) ∧ x) (dual◆ du2)) · (ap1 (λ x → x ∧ ξ2bar) (dual◆ du1))
  dual◆ (CDAnd {ξ1 = ξ1} {ξ1bar = ξ1bar} {ξ2 = ξ2} {ξ2bar = ξ2bar} du1 du2) =
    (ap1 (λ x → (ξ1 ◆d) ∨ x) (dual◆ du2)) · (ap1 (λ x → x ∨ ξ2bar) (dual◆ du1))
  
  -- move back from judgmental form to the function form
  ◆dual : (ξ ξbar : comp-constr) →
          (ξ ◆d == ξbar) →
          (dual ξ ξbar)
  ◆dual ·⊤ .(·⊤ ◆d) refl = CDTruth
  ◆dual ·⊥ .(·⊥ ◆d) refl = CDFalsity
  ◆dual (N n) .(N n ◆d) refl = CDNum
  ◆dual (N̸ n) .(N̸ n ◆d) refl = CDNotNum
  ◆dual (inl ξ) .(inl ξ ◆d) refl = CDInl (◆dual ξ (ξ ◆d) refl)
  ◆dual (inr ξ) .(inr ξ ◆d) refl = CDInr (◆dual ξ (ξ ◆d) refl)
  ◆dual ⟨ ξ1 , ξ2 ⟩ .(⟨ ξ1 , ξ2 ⟩ ◆d) refl =
    CDPair (◆dual ξ1 (ξ1 ◆d) refl) (◆dual ξ2 (ξ2 ◆d) refl)
  ◆dual (ξ1 ∨ ξ2) .((ξ1 ∨ ξ2) ◆d) refl =
    CDOr (◆dual ξ1 (ξ1 ◆d) refl) (◆dual ξ2 (ξ2 ◆d) refl)
  ◆dual (ξ1 ∧ ξ2) .((ξ1 ∧ ξ2) ◆d) refl =
    CDAnd (◆dual ξ1 (ξ1 ◆d) refl) (◆dual ξ2 (ξ2 ◆d) refl)
  
  -- judgemental duality only has one proof for
  -- relating the a term to its non-judgemental dual
  dual-contr : (ξ : comp-constr) →
               (x y : dual ξ (ξ ◆d)) →
               x == y
  dual-contr ·⊤ CDTruth CDTruth = refl
  dual-contr ·⊥ CDFalsity CDFalsity = refl
  dual-contr (N x) CDNum CDNum = refl
  dual-contr (N̸ x) CDNotNum CDNotNum = refl
  dual-contr (inl ξ) (CDInl x) (CDInl y) = ap1 CDInl (dual-contr ξ x y)
  dual-contr (inr ξ) (CDInr x) (CDInr y) = ap1 CDInr (dual-contr ξ x y)
  dual-contr ⟨ ξ1 , ξ2 ⟩ (CDPair x1 x2) (CDPair y1 y2) =
    (ap1 (λ x → CDPair x x2) (dual-contr ξ1 x1 y1)) ·
    (ap1 (λ x → CDPair y1 x) (dual-contr ξ2 x2 y2))
  dual-contr (ξ1 ∨ ξ2) (CDOr x1 x2) (CDOr y1 y2) = 
    (ap1 (λ x → CDOr x x2) (dual-contr ξ1 x1 y1)) ·
    (ap1 (λ x → CDOr y1 x) (dual-contr ξ2 x2 y2))
  dual-contr (ξ1 ∧ ξ2) (CDAnd x1 x2) (CDAnd y1 y2) =
    (ap1 (λ x → CDAnd x x2) (dual-contr ξ1 x1 y1)) ·
    (ap1 (λ x → CDAnd y1 x) (dual-contr ξ2 x2 y2))
  
  -- taken together, these four theorems demonstrate that both round-trips
  -- of the above functions are stable up to ==
  dual-rt1 : (ξ ξbar : comp-constr) →
             (x : ξ ◆d == ξbar) →
             (dual◆ (◆dual ξ ξbar x)) == x
  dual-rt1 ·⊤ .(·⊤ ◆d) refl = refl
  dual-rt1 ·⊥ .(·⊥ ◆d) refl = refl
  dual-rt1 (N n) .(N n ◆d) refl = refl
  dual-rt1 (N̸ n) .(N̸ n ◆d) refl = refl
  dual-rt1 (inl ξ) .(inl ξ ◆d) refl with dual◆ (◆dual ξ (ξ ◆d) refl)
  ... | refl = refl
  dual-rt1 (inr ξ) .(inr ξ ◆d) refl with dual◆ (◆dual ξ (ξ ◆d) refl)
  ... | refl = refl
  dual-rt1 ⟨ ξ1 , ξ2 ⟩ .(⟨ ξ1 , ξ2 ⟩ ◆d) refl
    with dual◆ (◆dual ξ1 (ξ1 ◆d) refl) | dual◆ (◆dual ξ2 (ξ2 ◆d) refl)
  ... | refl | refl = refl
  dual-rt1 (ξ1 ∨ ξ2) .((ξ1 ∨ ξ2) ◆d) refl
    with dual◆ (◆dual ξ1 (ξ1 ◆d) refl) | dual◆ (◆dual ξ2 (ξ2 ◆d) refl)
  ... | refl | refl = refl
  dual-rt1 (ξ1 ∧ ξ2) .((ξ1 ∧ ξ2) ◆d) refl
    with dual◆ (◆dual ξ1 (ξ1 ◆d) refl) | dual◆ (◆dual ξ2 (ξ2 ◆d) refl)
  ... | refl | refl = refl
  
  dual-rt2 : (ξ ξbar : comp-constr) →
             (x : dual ξ ξbar) →
             ◆dual ξ ξbar (dual◆ x) == x
  dual-rt2 ·⊤ .·⊥ CDTruth = refl
  dual-rt2 ·⊥ .·⊤ CDFalsity = refl
  dual-rt2 (N n) .(N̸ n) CDNum = refl
  dual-rt2 (N̸ n) .(N n) CDNotNum = refl
  dual-rt2 (inl ξ) .(inl _ ∨ inr ·⊤) (CDInl x)
    with dual◆ x
  ... | refl = ap1 (λ x → CDInl x) (dual-contr ξ (◆dual ξ (ξ ◆d) refl) x)
  dual-rt2 (inr ξ) .(inr _ ∨ inl ·⊤) (CDInr x)
    with dual◆ x
  ... | refl = ap1 (λ x → CDInr x) (dual-contr ξ (◆dual ξ (ξ ◆d) refl) x)
  dual-rt2 ⟨ ξ1 , ξ2 ⟩ .((⟨ ξ1 , _ ⟩ ∨ ⟨ _ , ξ2 ⟩) ∨ ⟨ _ , _ ⟩) (CDPair x1 x2)
    with dual◆ x1 | dual◆ x2
  ... | refl | refl =
    (ap1 (λ x → CDPair x (◆dual ξ2 (ξ2 ◆d) refl))
         (dual-contr ξ1 (◆dual ξ1 (ξ1 ◆d) refl) x1)) ·
    (ap1 (λ x → CDPair x1 x)
        (dual-contr ξ2 (◆dual ξ2 (ξ2 ◆d) refl) x2))
  dual-rt2 (ξ1 ∨ ξ2) .(_ ∧ _) (CDOr x1 x2)
    with dual◆ x1 | dual◆ x2
  ... | refl | refl =
    (ap1 (λ x → CDOr x (◆dual ξ2 (ξ2 ◆d) refl))
         (dual-contr ξ1 (◆dual ξ1 (ξ1 ◆d) refl) x1)) ·
    (ap1 (λ x → CDOr x1 x)
        (dual-contr ξ2 (◆dual ξ2 (ξ2 ◆d) refl) x2))
  dual-rt2 (ξ1 ∧ ξ2) .(_ ∨ _) (CDAnd x1 x2)
    with dual◆ x1 | dual◆ x2
  ... | refl | refl =
    (ap1 (λ x → CDAnd x (◆dual ξ2 (ξ2 ◆d) refl))
         (dual-contr ξ1 (◆dual ξ1 (ξ1 ◆d) refl) x1)) ·
    (ap1 (λ x → CDAnd x1 x)
        (dual-contr ξ2 (◆dual ξ2 (ξ2 ◆d) refl) x2))
  
  -- since both round trips are stable, these functions demonstrate
  -- isomorphisms between the judgemental and non-judgemental
  -- definitions of duality
  dual-iso : (ξ ξbar : comp-constr) →
             (ξ ◆d == ξbar) ≃ (dual ξ ξbar)
  dual-iso ξ ξbar = (◆dual ξ ξbar) , (dual◆ , dual-rt1 ξ ξbar , dual-rt2 ξ ξbar)

  -- this isomorphism supplies the argument that the judgement has mode
  -- (∀, !∃), where uniqueness comes from dual◆.
  dual-mode : (ξ : comp-constr) → Σ[ ξbar ∈ comp-constr ] (dual ξ ξbar)
  dual-mode ξ = (ξ ◆d) , ◆dual ξ (ξ ◆d) refl

  -- some translations and lemmas to move between the different
  -- forms. these are not needed to show that this is an ok encoding pair,
  -- but they are helpful when actually using it.

  -- even more specifically, the relation relates an expression to its
  -- functional dual
  rel◆d : (ξ : comp-constr) → (dual ξ (ξ ◆d))
  rel◆d ξ = ◆dual ξ (ξ ◆d) refl

  dual-det : ∀{ξ ξbar ξbar'} →
             dual ξ ξbar →
             dual ξ ξbar' →
             ξbar == ξbar'
  dual-det du du' with dual◆ du | dual◆ du'
  ... | refl | refl = refl

  eq-du-trans : ∀{ξ ξbar ξ'} →
                (ξ ◆d) == (ξ' ◆d) →
                dual ξ ξbar →
                dual ξ' ξbar
                
  eq-du-trans {ξ} {ξbar} {ξ'} eq du =
    tr (λ f → dual ξ' f) (dual-det (◆dual ξ (ξ' ◆d) eq) du) (rel◆d ξ')
