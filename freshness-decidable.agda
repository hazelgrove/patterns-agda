open import Nat
open import Prelude
open import core
open import freshness
open import patterns-core

module freshness-decidable where
  unbound-in-p-dec : (x : Nat) →
                     (p : pattrn) →
                     (unbound-in-p x p) + (unbound-in-p x p → ⊥)
  unbound-in-p-dec x (N n) = Inl UBPNum
  unbound-in-p-dec x (X y)
    with natEQ x y
  ... | Inl refl = Inr (λ{(UBPVar x≠x) → x≠x refl})
  ... | Inr x≠y = Inl (UBPVar x≠y)
  unbound-in-p-dec x (inl p)
    with unbound-in-p-dec x p
  ... | Inl ubp = Inl (UBPInl ubp)
  ... | Inr ¬ubp = Inr (λ{(UBPInl ubp) → ¬ubp ubp})
  unbound-in-p-dec x (inr p)
    with unbound-in-p-dec x p
  ... | Inl ubp = Inl (UBPInr ubp)
  ... | Inr ¬ubp = Inr (λ{(UBPInr ubp) → ¬ubp ubp})
  unbound-in-p-dec x ⟨ p1 , p2 ⟩
    with unbound-in-p-dec x p1
  ... | Inr ¬ubp1 = Inr λ{(UBPPair ubp1 ubp2) → ¬ubp1 ubp1}
  ... | Inl ubp1
    with unbound-in-p-dec x p2
  ... | Inr ¬ubp2 = Inr λ{(UBPPair ubp1 ubp2) → ¬ubp2 ubp2}
  ... | Inl ubp2 = Inl (UBPPair ubp1 ubp2)
  unbound-in-p-dec x wild = Inl UBPWild
  unbound-in-p-dec x ⦇-⦈[ w ] = Inl UBPEHole
  unbound-in-p-dec x ⦇⌜ p ⌟⦈[ w , τ ]
    with unbound-in-p-dec x p
  ... | Inl ubp = Inl (UBPNEHole ubp)
  ... | Inr ¬ubp = Inr (λ{(UBPNEHole ubp) → ¬ubp ubp})
  
  mutual
    fresh-dec : (x : Nat) →
                (e : ihexp) →
                (fresh x e) + (fresh x e → ⊥)
    fresh-dec x (N n) = Inl FNum
    fresh-dec x (X y)
      with natEQ x y
    ... | Inl refl = Inr λ{(FVar x≠x) → x≠x refl}
    ... | Inr x≠y = Inl (FVar x≠y)
    fresh-dec x (·λ y ·[ τ ] e)
      with natEQ x y
    ... | Inl refl = Inr λ{(FLam x≠x f) → x≠x refl}
    ... | Inr x≠y
      with fresh-dec x e
    ... | Inl frsh = Inl (FLam x≠y frsh)
    ... | Inr ¬frsh = Inr λ{(FLam x≠y f) → ¬frsh f}
    fresh-dec x (e1 ∘ e2)
      with fresh-dec x e1
    ... | Inr ¬frsh1 = Inr λ{(FAp frsh1 frsh2) → ¬frsh1 frsh1}
    ... | Inl frsh1
      with fresh-dec x e2
    ... | Inr ¬frsh2 = Inr λ{(FAp frsh1 frsh2) → ¬frsh2 frsh2}
    ... | Inl frsh2 = Inl (FAp frsh1 frsh2)
    fresh-dec x (inl τ e)
      with fresh-dec x e
    ... | Inl frsh = Inl (FInl frsh)
    ... | Inr ¬frsh = Inr λ{(FInl frsh) → ¬frsh frsh}
    fresh-dec x (inr τ e)
      with fresh-dec x e
    ... | Inl frsh = Inl (FInr frsh)
    ... | Inr ¬frsh = Inr λ{(FInr frsh) → ¬frsh frsh}
    fresh-dec x (match e rs)
      with fresh-dec x e
    ... | Inr ¬frsh = Inr λ{(FMatch frsh frshrs) → ¬frsh frsh}
    ... | Inl frsh
      with fresh-zrs-dec x rs
    ... | Inr ¬frshrs =
      Inr λ{(FMatch frsh frshrs) → ¬frshrs frshrs}
    ... | Inl frshrs = Inl (FMatch frsh frshrs)
    fresh-dec x ⟨ e1 , e2 ⟩
      with fresh-dec x e1
    ... | Inr ¬frsh1 = Inr λ{(FPair frsh1 frsh2) → ¬frsh1 frsh1}
    ... | Inl frsh1
      with fresh-dec x e2
    ... | Inr ¬frsh2 = Inr λ{(FPair frsh1 frsh2) → ¬frsh2 frsh2}
    ... | Inl frsh2 = Inl (FPair frsh1 frsh2)
    fresh-dec x (fst e)
      with fresh-dec x e
    ... | Inl frsh = Inl (FFst frsh)
    ... | Inr ¬frsh = Inr λ{(FFst frsh) → ¬frsh frsh}
    fresh-dec x (snd e)
      with fresh-dec x e
    ... | Inl frsh = Inl (FSnd frsh)
    ... | Inr ¬frsh = Inr λ{(FSnd frsh) → ¬frsh frsh}
    fresh-dec x ⦇-⦈[ u ] = Inl FEHole
    fresh-dec x ⦇⌜ e ⌟⦈[ u ]
      with fresh-dec x e
    ... | Inl frsh = Inl (FNEHole frsh)
    ... | Inr ¬frsh = Inr λ{(FNEHole frsh) → ¬frsh frsh}
    
    fresh-zrs-dec : (x : Nat) →
                    (zrs : zrules) →
                    (fresh-zrs x zrs) + (fresh-zrs x zrs → ⊥)
    fresh-zrs-dec x (rs-pre / r / rs-post)
      with fresh-rs-dec x rs-pre
    ... | Inr ¬frshpre =
      Inr λ{(FZRules frshpre (FRules frshr frshpost)) → ¬frshpre frshpre}
    ... | Inl frshpre
      with fresh-r-dec x r
    ... | Inr ¬frshr =
      Inr λ{(FZRules frshpre (FRules frshr frshpost)) → ¬frshr frshr}
    ... | Inl frshr
      with fresh-rs-dec x rs-post
    ... | Inr ¬frshpost =
      Inr λ{(FZRules frshpre (FRules frshr frshpost)) → ¬frshpost frshpost}
    ... | Inl frshpost = Inl (FZRules frshpre (FRules frshr frshpost))
    
    fresh-rs-dec : (x : Nat) →
                   (rs : rules) →
                   (fresh-rs x rs) + (fresh-rs x rs → ⊥)
    fresh-rs-dec x nil = Inl FNoRules
    fresh-rs-dec x (r / rs)
      with fresh-r-dec x r
    ... | Inr ¬frshr = Inr λ{(FRules frshr frshrs) → ¬frshr frshr}
    ... | Inl frshr
      with fresh-rs-dec x rs
    ... | Inr ¬frshrs =
      Inr λ{(FRules frshr frshrs) → ¬frshrs frshrs}
    ... | Inl frshrs = Inl (FRules frshr frshrs)
    
    fresh-r-dec : (x : Nat) →
                  (r : rule) →
                  (fresh-r x r) + (fresh-r x r → ⊥)
    fresh-r-dec x (p => e)
      with unbound-in-p-dec x p
    ... | Inr ¬ub = Inr λ{(FRule ub frsh) → ¬ub ub}
    ... | Inl ub
      with fresh-dec x e
    ... | Inr ¬frsh = Inr λ{(FRule ub frsh) → ¬frsh frsh}
    ... | Inl frsh = Inl (FRule ub frsh)
