open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness

module exchange where
  -- exchanging just two disequal elements produces the same context
  swap-little : {A : Set} {x y : Nat} {τ1 τ2 : A} → (x ≠ y) →
    ((■ (x , τ1)) ,, (y , τ2)) == ((■ (y , τ2)) ,, (x , τ1))
  swap-little {A} {x} {y} {τ1} {τ2} neq = ∪comm (■ (y , τ2))
                                                (■ (x , τ1))
                                                (disjoint-singles (flip neq))

  -- really the dynamics-core of all the exchange arguments: contexts with two
  -- disequal elements exchanged are the same. we reassociate the unions,
  -- swap as above, and then associate them back.
  --
  -- note that this is generic in the contents of the context. the proofs
  -- below show the exchange properties that we actually need in the
  -- various other proofs; the remaning exchange properties for both Δ and
  -- Γ positions for all the other hypothetical judgements are exactly in
  -- this pattern.
  swap : {A : Set} {x y : Nat} {τ1 τ2 : A} (Γ : A ctx) (x≠y : x == y → ⊥) →
         ((Γ ,, (x , τ1)) ,, (y , τ2)) == ((Γ ,, (y , τ2)) ,, (x , τ1))
  swap {A} {x} {y} {τ1} {τ2} Γ neq = funext eq
    where
      eq : (z : Nat) →  ((Γ ,, (x , τ1)) ,, (y , τ2)) z == ((Γ ,, (y , τ2)) ,, (x , τ1)) z
      eq z with natEQ y z
      ... | Inr y≠z with natEQ x z
      ... | Inl refl = refl
      ... | Inr x≠z with natEQ y z
      ... | Inl refl = abort (y≠z refl)
      ... | Inr y≠z' = refl
      eq z | Inl refl with natEQ x z
      ... | Inl refl = abort (neq refl)
      ... | Inr x≠z with natEQ z z
      ... | Inl refl = refl
      ... | Inr z≠z = abort (z≠z refl)
