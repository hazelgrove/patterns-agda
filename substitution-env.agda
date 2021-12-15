open import List
open import Nat
open import Prelude
open import contexts
open import core

module substitution-env where
  -- identity substitution, substitition environments
  data env : Set where
    Id    : (Γ : tctx) → env
    Subst : (d : ihexp) → (y : Nat) → env → env

  env-to-data : env → (List (ihexp × Nat)) × tctx
  env-to-data (Id Γ) = [] , Γ
  env-to-data (Subst d y θ) with env-to-data θ
  ... | subs , Γ = (d , y) :: subs , Γ

  data-to-env : List (ihexp × Nat) → tctx → env
  data-to-env [] Γ = Id Γ
  data-to-env ((d , y) :: subs) Γ = Subst d y (data-to-env subs Γ)

  data-to-env-to-data : ∀(subs : List (ihexp × Nat)) (Γ : tctx) →
                        env-to-data (data-to-env subs Γ) == (subs , Γ)
  data-to-env-to-data [] Γ = refl
  data-to-env-to-data (sub :: subs) Γ rewrite data-to-env-to-data subs Γ = refl

  env-to-data-to-env : ∀(θ : env) →
                       uncurry data-to-env (env-to-data θ) == θ
  env-to-data-to-env (Id Γ) = refl
  env-to-data-to-env (Subst d y θ) rewrite env-to-data-to-env θ = refl

  -- take the union of two substitution environments
  -- warning: this assumes all mentioned variables are unique,
  -- or else this is not symmetric. due to the implementation of
  -- unions of contexts, the elements of θ1 are preferred, and
  -- we also arbitrarily choose to apply substitutions of θ1 first
  add-ids : tctx → env → env
  add-ids Γ (Id Γ') = Id (Γ ∪ Γ')
  add-ids Γ (Subst d y θ) = Subst d y (add-ids Γ θ)
  
  _⊎_ : env → env → env
  θ1 ⊎ θ2 with env-to-data θ1 | env-to-data θ2
  ... | subs1 , Γ1 | subs2 , Γ2 = data-to-env (subs2 ++ subs1) (Γ1 ∪ Γ2)
