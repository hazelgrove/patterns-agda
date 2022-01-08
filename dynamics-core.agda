open import Nat
open import Prelude
open import contexts
open import core
open import freshness
open import freshness-decidable
open import lemmas-freshness
open import patterns-core
open import result-judgements
open import statics-core
open import substitution-env

module dynamics-core where
  -- e' is one of the possible values of e
  data _∈[_]values_ : (e' : ihexp) → (Δ : tctx) →
                      (e : ihexp) → Set where
    IVVal   : ∀{Δ e τ} →
              e val →
              ∅ , Δ ⊢ e :: τ →
              e ∈[ Δ ]values e
    IVIndet : ∀{Δ e e' τ} →
              e notintro →
              ∅ , Δ ⊢ e :: τ →
              e' val →
              ∅ , Δ ⊢ e' :: τ →
              e' ∈[ Δ ]values e
    IVInl   : ∀{Δ e1 e1' τ2 τ} →
              (inl τ2 e1) indet →
              ∅ , Δ ⊢ inl τ2 e1 :: τ →
              e1' ∈[ Δ ]values e1 →
              (inl τ2 e1') ∈[ Δ ]values (inl τ2 e1)
    IVInr   : ∀{Δ e2 e2' τ1 τ} →
              (inr τ1 e2) indet →
              ∅ , Δ ⊢ inr τ1 e2 :: τ →
              e2' ∈[ Δ ]values e2 →
              (inr τ1 e2') ∈[ Δ ]values (inr τ1 e2)
    IVPair  : ∀{Δ e1 e1' e2 e2' τ} →
              ⟨ e1 , e2 ⟩ indet →
              ∅ , Δ ⊢ ⟨ e1 , e2 ⟩ :: τ →
              e1' ∈[ Δ ]values e1 →
              e2' ∈[ Δ ]values e2 →
              ⟨ e1' , e2' ⟩ ∈[ Δ ]values ⟨ e1 , e2 ⟩

  -- substitution
  mutual
    [_/_]r : ihexp → Nat → rule → rule
    [ d / y ]r (p => e) with unbound-in-p-dec y p
    ... | Inl _ = p => ([ d / y ] e)
    ... | Inr _ = p => e

    [_/_]rs : ihexp → Nat → rules → rules
    [ d / y ]rs nil = nil
    [ d / y ]rs (r / rs) =
      ([ d / y ]r r) / ([ d / y ]rs rs)

    [_/_]zrs : ihexp → Nat → zrules → zrules
    [ d / y ]zrs (rs-pre / r / rs-post) =
      ([ d / y ]rs rs-pre) / ([ d / y ]r r) / ([ d / y ]rs rs-post)
      
    [_/_]_ : ihexp → Nat → ihexp → ihexp
    [ d / y ] (N n) = N n
    [ d / y ] X x
      with natEQ x y
    [ d / y ] X .y | Inl refl = d
    [ d / y ] X x  | Inr x≠y = X x
    [ d / y ] (·λ x ·[ τ ] d')
      with natEQ x y
    [ d / y ] (·λ .y ·[ τ ] d') | Inl refl = ·λ y ·[ τ ] d'
    [ d / y ] (·λ x ·[ τ ] d')  | Inr x≠y =
      ·λ x ·[ τ ] ( [ d / y ] d')
    [ d / y ] (d1 ∘ d2) = ([ d / y ] d1) ∘ ([ d / y ] d2)
    [ d / y ] (inl τ d') = inl τ ([ d / y ] d')
    [ d / y ] (inr τ d') = inr τ ([ d / y ] d')
    [ d / y ] match d' rs = match ([ d / y ] d') ([ d / y ]zrs rs) 
    [ d / y ] ⟨ d1 , d2 ⟩ = ⟨ [ d / y ] d1 , [ d / y ] d2 ⟩
    [ d / y ] (fst d') = fst ([ d / y ] d')
    [ d / y ] (snd d') = snd ([ d / y ] d')
    [ d / y ] ⦇-⦈[ u ] = ⦇-⦈[ u ]
    [ d / y ] ⦇⌜ d' ⌟⦈[ u ] =  ⦇⌜ [ d / y ] d' ⌟⦈[ u ]

  -- apply a substitution
  apply-env : env → ihexp → ihexp
  apply-env (Id Γ) d = d
  apply-env (Subst d y σ) d' = [ d / y ] ( apply-env σ d')
  
  -- e takes a step to e'
  data _↦_ : (e : ihexp) → (e' : ihexp) → Set where
    ITApFun  : ∀{e1 e1' e2} →
               e1 ↦ e1' →
               (e1 ∘ e2) ↦ (e1' ∘ e2)
    ITApArg  : ∀{e1 e2 e2'} →
               e1 val →
               e2 ↦ e2' →
               (e1 ∘ e2) ↦ (e1 ∘ e2')
    ITAp     : ∀{x τ e1 e2} →
               e2 val →
               ((·λ x ·[ τ ] e1) ∘ e2) ↦ ([ e2 / x ] e1)
    ITPairL  : ∀{e1 e1' e2} →
               e1 ↦ e1' →
               ⟨ e1 , e2 ⟩ ↦ ⟨ e1' , e2 ⟩
    ITPairR  : ∀{e1 e2 e2'} →
               e1 val →
               e2 ↦ e2' →
               ⟨ e1 , e2 ⟩ ↦ ⟨ e1 , e2' ⟩
    ITFst    : ∀{e1 e2} →
               ⟨ e1 , e2 ⟩ final →
               fst ⟨ e1 , e2 ⟩ ↦ e1
    ITSnd    : ∀{e1 e2} →
               ⟨ e1 , e2 ⟩ final →
               snd ⟨ e1 , e2 ⟩ ↦ e2
    ITInl    : ∀{e e' τ} →
               e ↦ e' →
               inl τ e ↦ inl τ e'
    ITInr    : ∀{e e' τ} →
               e ↦ e' →
               inr τ e ↦ inr τ e'
    ITExpMatch  : ∀{e e' rs} →
                  e ↦ e' →
                  match e rs ↦ match e' rs
    ITSuccMatch : ∀{e θ rs-pre pr er rs-post} →
                  e final →
                  e ▹ pr ⊣ θ →
                  match e (rs-pre / (pr => er) / rs-post) ↦
                    apply-env θ er
    ITFailMatch : ∀{e rs pr er rss r' rs'} →
                  e final →
                  e ⊥▹ pr →
                  erase-r (rs / (pr => er) / nil) rss →
                  match e (rs / (pr => er) / (r' / rs')) ↦
                    match e (rss / r' / rs')
    ITNEHole : ∀{e e' u} →
               e ↦ e' →
               ⦇⌜ e ⌟⦈[ u ] ↦ ⦇⌜ e' ⌟⦈[ u ]
