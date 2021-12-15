open import Nat
open import Prelude
open import core
open import contexts

module htype-decidable where
  arr-lemma : ∀{t1 t2 t3 t4} → t1 ==> t2 == t3 ==> t4 → t1 == t3 × t2 == t4
  arr-lemma refl = refl , refl

  sum-lemma : ∀{t1 t2 t3 t4} → t1 ⊕ t2 == t3 ⊕ t4 → t1 == t3 × t2 == t4
  sum-lemma refl = refl , refl
  
  prod-lemma : ∀{t1 t2 t3 t4} → t1 ⊠ t2 == t3 ⊠ t4 → t1 == t3 × t2 == t4
  prod-lemma refl = refl , refl
  
  htype-dec : (t1 t2 : htyp) → t1 == t2 + (t1 == t2 → ⊥)
  htype-dec num num = Inl refl
  htype-dec num ⦇-⦈ = Inr (λ ())
  htype-dec num (t1 ==> t2) = Inr (λ ())
  htype-dec num (t1 ⊕ t2) = Inr (λ ())
  htype-dec ⦇-⦈ num = Inr (λ ())
  htype-dec ⦇-⦈ ⦇-⦈ = Inl refl
  htype-dec ⦇-⦈ (t1 ==> t2) = Inr (λ ())
  htype-dec ⦇-⦈ (t1 ⊕ t2) = Inr (λ ())
  htype-dec (t1 ==> t2) num = Inr (λ ())
  htype-dec (t1 ==> t2) ⦇-⦈ = Inr (λ ())
  htype-dec (t1 ==> t2) (t3 ==> t4)
    with htype-dec t1 t3 | htype-dec t2 t4
  ... | Inl refl | Inl refl = Inl refl
  ... | Inl refl | Inr x₁   = Inr (λ x → x₁ (π2 (arr-lemma x)))
  ... | Inr x    | Inl refl = Inr (λ x₁ → x (π1 (arr-lemma x₁)))
  ... | Inr x    | Inr x₁   = Inr (λ x₂ → x (π1 (arr-lemma x₂)))
  htype-dec (t1 ==> t2) (t3 ⊕ t4) = Inr (λ ())
  htype-dec (t1 ⊕ t2) num = Inr (λ ())
  htype-dec (t1 ⊕ t2) ⦇-⦈ = Inr (λ ())
  htype-dec (t1 ⊕ t2) (t3 ==> t4) = Inr (λ ())
  htype-dec (t1 ⊕ t2) (t3 ⊕ t4)
    with htype-dec t1 t3 | htype-dec t2 t4
  ... | Inl refl | Inl refl = Inl refl
  ... | Inl refl | Inr x₁   = Inr (λ x → x₁ (π2 (sum-lemma x)))
  ... | Inr x    | Inl refl = Inr (λ x₁ → x (π1 (sum-lemma x₁)))
  ... | Inr x    | Inr x₁   = Inr (λ x₂ → x (π1 (sum-lemma x₂)))
  htype-dec num (t3 ⊠ t4) = Inr (λ ())
  htype-dec ⦇-⦈ (t3 ⊠ t4) = Inr (λ ())
  htype-dec (t1 ==> t2) (t3 ⊠ t4) = Inr (λ ())
  htype-dec (t1 ⊕ t2) (t3 ⊠ t4) = Inr (λ ())
  htype-dec (t1 ⊠ t2) num = Inr (λ ())
  htype-dec (t1 ⊠ t2) ⦇-⦈ = Inr (λ ())
  htype-dec (t1 ⊠ t2) (t3 ==> t4) = Inr (λ ())
  htype-dec (t1 ⊠ t2) (t3 ⊕ t4) = Inr (λ ())
  htype-dec (t1 ⊠ t2) (t3 ⊠ t4)
    with htype-dec t1 t3 | htype-dec t2 t4
  ... | Inl refl | Inl refl = Inl refl
  ... | Inl refl | Inr x₁   = Inr (λ x → x₁ (π2 (prod-lemma x)))
  ... | Inr x    | Inl refl = Inr (λ x₁ → x (π1 (prod-lemma x₁)))
  ... | Inr x    | Inr x₁   = Inr (λ x₂ → x (π1 (prod-lemma x₂)))
