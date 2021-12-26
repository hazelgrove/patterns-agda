open import Prelude
open import contexts
open import core
open import complete-constraints-core
open import complete-satisfy-exclusive
open import statics-core
open import value-judgements

module material-entailment where
  dual-same-type : ∀{ξ τ} →
                   ξ :cc: τ →
                   (ξ ◆d) :cc: τ
  dual-same-type CTTruth = CTFalsity
  dual-same-type CTFalsity = CTTruth
  dual-same-type CTNum = CTNotNum
  dual-same-type CTNotNum = CTNum
  dual-same-type (CTInl ct) =
    CTOr (CTInl (dual-same-type ct)) (CTInr CTTruth)
  dual-same-type (CTInr ct) =
    CTOr (CTInr (dual-same-type ct)) (CTInl CTTruth)
  dual-same-type (CTPair ct1 ct2) =
    CTOr (CTOr (CTPair ct1 (dual-same-type ct2))
               (CTPair (dual-same-type ct1) ct2))
               (CTPair (dual-same-type ct1) (dual-same-type ct2))
  dual-same-type (CTOr ct1 ct2) =
    CTAnd (dual-same-type ct1) (dual-same-type ct2)
  dual-same-type (CTAnd ct1 ct2) =
    CTOr (dual-same-type ct1) (dual-same-type ct2)

  same-type-dual : ∀{ξ τ} →
                   (ξ ◆d) :cc: τ →
                   ξ :cc: τ
  same-type-dual {ξ = ·⊤} CTFalsity = CTTruth
  same-type-dual {ξ = ·⊥} CTTruth = CTFalsity
  same-type-dual {ξ = N n} CTNotNum = CTNum
  same-type-dual {ξ = N̸ n} CTNum = CTNotNum
  same-type-dual {ξ = inl ξ} {τ = τ1 ⊕ τ2} (CTOr (CTInl dct1) dct2) =
    CTInl (same-type-dual dct1)
  same-type-dual {ξ = inr ξ} {τ = τ1 ⊕ τ2} (CTOr (CTInr dct1) dct2) =
    CTInr (same-type-dual dct1)
  same-type-dual {ξ = ⟨ ξ1 , ξ2 ⟩} {τ = τ1 ⊠ τ2}
                 (CTOr (CTOr (CTPair dct1 dct2) (CTPair dct3 dct4)) dct5) =
    CTPair dct1 dct4
  same-type-dual {ξ = ξ1 ∨ ξ2} (CTAnd dct1 dct2) =
    CTOr (same-type-dual dct1) (same-type-dual dct2)
  same-type-dual {ξ = ξ1 ∧ ξ2} (CTOr dct1 dct2) =
    CTAnd (same-type-dual dct1) (same-type-dual dct2)
  
  entailment-material : ∀{ξ1 ξ2} →
                        ξ1 cc⊧ ξ2 →
                        ·⊤ cc⊧ ((ξ1 ◆d) ∨ ξ2)
  entailment-material {ξ1 = ξ1} {ξ2 = ξ2} (Entails {τ = τ} ct1 ct2 ent) =
    Entails CTTruth (CTOr (dual-same-type ct1) ct2) material
    where
      material : ∀{Δ e} →
            ∅ , Δ ⊢ e :: τ →
            e val →
            e ⊧ ·⊤ →
            e ⊧ ((ξ1 ◆d) ∨ ξ2)
      material wt eval CSTruth
        with comp-satisfy-exclusive ct1 wt eval
      ... | Satisfy sat1 _ = CSOrR (ent wt eval sat1)
      ... | SatisfyDual _ satd1 = CSOrL satd1

  material-entailment : ∀{ξ1 ξ2} →
                        ·⊤ cc⊧ ((ξ1 ◆d) ∧ ξ2) →
                        ξ1 cc⊧ ξ2
  material-entailment {ξ1 = ξ1} {ξ2 = ξ2}
                      (Entails tct (CTAnd {τ = τ} ctd1 ct2) ment) =
    Entails (same-type-dual ctd1) ct2 ent
    where
      ent : ∀{Δ e} →
            ∅ , Δ ⊢ e :: τ →
            e val →
            e ⊧ ξ1 →
            e ⊧ ξ2
      ent wt eval sat1
        with ment wt eval CSTruth
      ... | CSAnd satd1 sat2 = sat2
