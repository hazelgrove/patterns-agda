
open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import exchange
open import freshness
open import lemmas-contexts
open import lemmas-freshness
open import patterns-core
open import statics-core
open import result-judgements

module weakening where
  mutual
    weaken-ta-∪Γ : ∀{Γ' Γ Δ e τ} →
                   (∀{x} →
                    dom Γ' x →
                    fresh x e) →
                    Γ , Δ ⊢ e :: τ →
                   (Γ' ∪ Γ) , Δ ⊢ e :: τ
    weaken-ta-∪Γ frsh TANum = TANum
    weaken-ta-∪Γ {Γ' = Γ'} {Γ = Γ} {τ = τ} frsh (TAVar {x = x} x∈Γ)
      with Γ' x in Γ'x
    ... | None = TAVar (dom-r-union Γ' Γ x τ x∈Γ Γ'x)
    ... | Some τ'
      with frsh (τ' , Γ'x)
    ... | FVar x≠x = abort (x≠x refl)
    weaken-ta-∪Γ {Γ' = Γ'} {Γ = Γ} {Δ = Δ} {e = ·λ x ·[ τ1 ] e}
                 frsh (TALam {τ2 = τ2} x#Γ wt)
      with Γ' x in Γ'x
    ... | Some τ'
      with frsh (τ' , Γ'x)
    ... | FLam x≠x f = abort (x≠x refl)
    weaken-ta-∪Γ {Γ' = Γ'} {Γ = Γ} {Δ = Δ} {e = ·λ x ·[ τ1 ] e}
                 frsh (TALam {τ2 = τ2} x#Γ wt)
        | None =
      TALam (apart-parts Γ' Γ x Γ'x x#Γ)
            (tr (λ qq → qq , Δ ⊢ e :: τ2) eq
                (weaken-ta-∪Γ frsh' wt))
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FLam z≠x f = f
        
        eq : Γ' ∪ (Γ ,, (x , τ1)) == (Γ' ∪ Γ) ,, (x , τ1)
        eq = ! (∪-assoc Γ' (■ (x , τ1)) Γ) ·
             (ap1 (λ qq → qq ∪ Γ)
                  (∪-comm Γ' (■ (x , τ1))
                         (##-comm (apart-singleton-disjoint Γ'x))) ·
              (∪-assoc (■ (x , τ1)) Γ' Γ))
    weaken-ta-∪Γ {Γ' = Γ'} {e = e1 ∘ e2} frsh (TAAp wt1 wt2) =
      TAAp (weaken-ta-∪Γ frsh1 wt1)
           (weaken-ta-∪Γ frsh2 wt2)
      where
        frsh1 : ∀{z} →
                dom Γ' z →
                fresh z e1
        frsh1 z∈Γ' with frsh z∈Γ'
        ... | FAp f1 f2 = f1
        frsh2 : ∀{z} →
                dom Γ' z →
                fresh z e2
        frsh2 z∈Γ' with frsh z∈Γ'
        ... | FAp f1 f2 = f2
    weaken-ta-∪Γ {Γ' = Γ'} {e = inl τ1 e} frsh (TAInl wt) =
      TAInl (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FInl f = f
    weaken-ta-∪Γ {Γ' = Γ'} {e = inr τ e} frsh (TAInr wt) = 
      TAInr (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FInr f = f
    weaken-ta-∪Γ {Γ' = Γ'} {e = match e (nil / r / rs)}
                 frsh (TAMatchZPre wt rst) =
      TAMatchZPre (weaken-ta-∪Γ frsh' wt)
                  (weaken-rules-∪Γ frshr rst)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FMatch f frs = f
        frshr : ∀{z} →
                dom Γ' z →
                fresh-rs z (r / rs)
        frshr z∈Γ' with frsh z∈Γ'
        ... | FMatch f (FZRules FNoRules (FRules fr frs)) = FRules fr frs
    weaken-ta-∪Γ {Γ' = Γ'} {e = match e (rs-pre / r / rs-post)}
                 frsh (TAMatchNZPre wt fin pret postt ¬red) =
      TAMatchNZPre (weaken-ta-∪Γ frsh' wt)
                   fin
                   (weaken-rules-∪Γ frshpre pret)
                   (weaken-rules-∪Γ frshpost postt)
                   ¬red
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FMatch f frs = f
        frshpre : ∀{z} →
                  dom Γ' z →
                  fresh-rs z rs-pre
        frshpre z∈Γ' with frsh z∈Γ'
        ... | FMatch f (FZRules fpre (FRules fr fpost)) = fpre
        frshpost : ∀{z} →
                   dom Γ' z →
                   fresh-rs z (r / rs-post)
        frshpost z∈Γ' with frsh z∈Γ'
        ... | FMatch f (FZRules fpre (FRules fr fpost)) = FRules fr fpost
    weaken-ta-∪Γ {Γ' = Γ'} {e = ⟨ e1 , e2 ⟩} frsh (TAPair wt1 wt2) = 
      TAPair (weaken-ta-∪Γ frsh1 wt1)
           (weaken-ta-∪Γ frsh2 wt2)
      where
        frsh1 : ∀{z} →
                dom Γ' z →
                fresh z e1
        frsh1 z∈Γ' with frsh z∈Γ'
        ... | FPair f1 f2 = f1
        frsh2 : ∀{z} →
                dom Γ' z →
                fresh z e2
        frsh2 z∈Γ' with frsh z∈Γ'
        ... | FPair f1 f2 = f2
    weaken-ta-∪Γ {Γ' = Γ'} {e = fst e} frsh (TAFst wt) =
      TAFst (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FFst f = f 
    weaken-ta-∪Γ {Γ' = Γ'} {e = snd e} frsh (TASnd wt) =
      TASnd (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FSnd f = f 
    weaken-ta-∪Γ frsh (TAEHole u∈Δ) = TAEHole u∈Δ
    weaken-ta-∪Γ {Γ' = Γ'} {e = ⦇⌜ e ⌟⦈[ u ]} frsh (TANEHole u∈Δ wt) =
      TANEHole u∈Δ
               (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FNEHole f = f

    weaken-rules-∪Γ : ∀{Γ' Γ Δ rs τ1 ξ τ2} →
                      (∀{x} →
                       dom Γ' x →
                       fresh-rs x rs) →
                      Γ , Δ ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                      (Γ' ∪ Γ) , Δ ⊢ rs ::s τ1 [ ξ ]=> τ2
    weaken-rules-∪Γ {Γ' = Γ'} frsh (CTOneRule {r = p => e} rt) =
      CTOneRule (weaken-rule-∪Γ frsh' rt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh-r z (p => e)
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FRules fr frs = fr
    weaken-rules-∪Γ {Γ' = Γ'} frsh (CTRules {r = r} {rs = rs} rt rst) =
      CTRules (weaken-rule-∪Γ frshr rt)
              (weaken-rules-∪Γ frshrs rst)
      where
        frshr : ∀{z} →
                dom Γ' z →
                fresh-r z r
        frshr z∈Γ' with frsh z∈Γ'
        ... | FRules f frs = f
        frshrs : ∀{z} →
                 dom Γ' z →
                 fresh-rs z rs
        frshrs z∈Γ' with frsh z∈Γ'
        ... | FRules f frs = frs
    
    weaken-rule-∪Γ : ∀{Γ' Γ Δ r τ1 ξ τ2} →
                     (∀{x} →
                      dom Γ' x →
                      fresh-r x r) →
                     Γ , Δ ⊢ r :: τ1 [ ξ ]=> τ2 →
                     (Γ' ∪ Γ) , Δ ⊢ r :: τ1 [ ξ ]=> τ2
    weaken-rule-∪Γ {Γ' = Γ'} {Γ = Γ} {Δ = Δ} {τ2 = τ2} frsh
                   (CTRule {e = e} {Γp = Γp} {Δp = Δp} pt Γ##Γp Δ##Δp wt) =
      CTRule pt
             (disjoint-parts Γ'##Γp Γ##Γp)
             Δ##Δp
             (tr (λ qq → qq , Δ ∪ Δp ⊢ e :: τ2)
                 (! (∪-assoc Γ' Γ Γp))
                 (weaken-ta-∪Γ frsh' wt))
      where
        Γ'##Γp : Γ' ## Γp
        Γ'##Γp = disj1 , disj2
          where
            disj1 : (x : Nat) →
                    dom Γ' x →
                    x # Γp
            disj1 x x∈Γ' with frsh x∈Γ'
            ... | FRule ub f = unbound-in-p-apart-Γp pt ub
            disj2 : (x : Nat) →
                    dom Γp x →
                    x # Γ'
            disj2 x x∈Γp
              with Γ' x in Γ'x
            ... | None = refl
            ... | Some τ1 
              with disj1 x (τ1 , Γ'x)
            ... | x#Γp = abort (some-not-none (! (π2 x∈Γp) · x#Γp))

        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FRule ub f = f
    
    -- Commutativity of union requires disjointness, so we
    -- make use of th identity
    -- Γ ∪ Γ' = Γ ⊔ (Γ' \ Γ) = (Γ' \ Γ) ⊔ Γ
    weaken-ta-Γ∪ : ∀{Γ Γ' Δ e τ} →
                   (∀{x} →
                    dom Γ' x →
                    fresh x e) →
                   Γ , Δ ⊢ e :: τ →
                   (Γ ∪ Γ') , Δ ⊢ e :: τ
    weaken-ta-Γ∪ {Γ = Γ} {Γ' = Γ'} {Δ = Δ} {e = e} {τ = τ} frsh wt =
      tr (λ qq → qq , Δ ⊢ e :: τ)
         (! (union-with-diff Γ Γ' ·
             ∪-comm Γ (Γ' ∖ Γ) (r-disjoint-diff-r Γ' Γ)))
         (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom (Γ' ∖ Γ) z →
                fresh z e
        frsh' {z = z} (τ , z∈Γ'∖Γ) =
          frsh (τ , dom-diff-dom-l {Γ1 = Γ'} {Γ2 = Γ} z∈Γ'∖Γ)
         
    -- convenience function
    weaken-ta-Γ : ∀{Γ x τ' Δ e τ} →
                  fresh x e →
                  Γ , Δ ⊢ e :: τ →
                  (Γ ,, (x , τ')) , Δ ⊢ e :: τ
    weaken-ta-Γ {x = x} {τ' = τ'} {e = e} frsh wt =
      weaken-ta-∪Γ frsh' wt
      where
        frsh' : ∀{z} →
                dom (■ (x , τ')) z →
                fresh z e
        frsh' d with dom-singleton-eq d
        ... | refl = frsh
        
  mutual
    weaken-ta-∪Δ : ∀{Γ Δ' Δ e τ} →
                   (∀{u} →
                    dom Δ' u →
                    hole-fresh u e) →
                   Γ , Δ ⊢ e :: τ →
                   Γ , (Δ' ∪ Δ) ⊢ e :: τ
    weaken-ta-∪Δ frsh TANum = TANum
    weaken-ta-∪Δ frsh (TAVar x∈Γ) = TAVar x∈Γ
    weaken-ta-∪Δ {Δ' = Δ'} {e = ·λ x ·[ τ1 ] e}
                 frsh (TALam x#Γ wt) =
      TALam x#Γ
            (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFLam hf = hf
    weaken-ta-∪Δ {Δ' = Δ'} {e = e1 ∘ e2} frsh (TAAp wt1 wt2) =
      TAAp (weaken-ta-∪Δ frsh1 wt1)
           (weaken-ta-∪Δ frsh2 wt2)
      where
        frsh1 : ∀{z} →
                dom Δ' z →
                hole-fresh z e1
        frsh1 z∈Δ' with frsh z∈Δ'
        ... | HFAp hf1 hf2 = hf1
        frsh2 : ∀{z} →
                dom Δ' z →
                hole-fresh z e2
        frsh2 z∈Δ' with frsh z∈Δ'
        ... | HFAp hf1 hf2 = hf2
    weaken-ta-∪Δ {Δ' = Δ'} {e = inl τ1 e} frsh (TAInl wt) =
      TAInl (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFInl hf = hf
    weaken-ta-∪Δ {Δ' = Δ'} {e = inr τ1 e} frsh (TAInr wt) =
      TAInr (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFInr hf = hf
    weaken-ta-∪Δ {Δ' = Δ'} {e = match e (nil / r / rs)}
                 frsh (TAMatchZPre wt rst) =
      TAMatchZPre (weaken-ta-∪Δ frsh' wt)
                  (weaken-rules-∪Δ frshr rst)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFMatch hf hfrs = hf
        frshr : ∀{z} →
                dom Δ' z →
                hole-fresh-rs z (r / rs)
        frshr z∈Δ' with frsh z∈Δ'
        ... | HFMatch hf (HFZRules HFNoRules (HFRules hfr hfrs)) =
          HFRules hfr hfrs
    weaken-ta-∪Δ {Δ' = Δ'} {e = match e (rs-pre / r / rs-post)}
                 frsh (TAMatchNZPre wt fin pret postt ¬red) =
      TAMatchNZPre (weaken-ta-∪Δ frsh' wt)
                   fin
                   (weaken-rules-∪Δ frshpre pret)
                   (weaken-rules-∪Δ frshpost postt)
                   ¬red
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFMatch hf hfrs = hf
        frshpre : ∀{z} →
                  dom Δ' z →
                  hole-fresh-rs z rs-pre
        frshpre z∈Δ' with frsh z∈Δ'
        ... | HFMatch hf (HFZRules hfpre (HFRules hfr hfpost)) = hfpre
        frshpost : ∀{z} →
                   dom Δ' z →
                   hole-fresh-rs z (r / rs-post)
        frshpost z∈Δ' with frsh z∈Δ'
        ... | HFMatch hf (HFZRules hfpre (HFRules hfr hfpost)) =
          HFRules hfr hfpost
    weaken-ta-∪Δ {Δ' = Δ'} {e = ⟨ e1 , e2 ⟩} frsh (TAPair wt1 wt2) =
      TAPair (weaken-ta-∪Δ frsh1 wt1)
             (weaken-ta-∪Δ frsh2 wt2)
      where
        frsh1 : ∀{z} →
                dom Δ' z →
                hole-fresh z e1
        frsh1 z∈Δ' with frsh z∈Δ'
        ... | HFPair hf1 hf2 = hf1
        frsh2 : ∀{z} →
                dom Δ' z →
                hole-fresh z e2
        frsh2 z∈Δ' with frsh z∈Δ'
        ... | HFPair hf1 hf2 = hf2
    weaken-ta-∪Δ {Δ' = Δ'} {e = fst e} frsh (TAFst wt) = 
      TAFst (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFFst hf = hf
    weaken-ta-∪Δ {Δ' = Δ'} {e = snd e} frsh (TASnd wt) =
      TASnd (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFSnd hf = hf
    weaken-ta-∪Δ {Δ' = Δ'} {Δ = Δ} frsh (TAEHole {u = u} {τ = τ} u∈Δ)
      with Δ' u in Δ'u
    ... | Some τ'
      with frsh (τ' , Δ'u)
    ... | HFEHole u≠u = abort (u≠u refl)
    weaken-ta-∪Δ {Δ' = Δ'} {Δ = Δ} frsh (TAEHole {u = u} {τ = τ} u∈Δ)
        | None = TAEHole (dom-r-union Δ' Δ u τ u∈Δ Δ'u)
    weaken-ta-∪Δ {Δ' = Δ'} {Δ = Δ} frsh (TANEHole {u = u} {τ = τ} u∈Δ wt)
      with Δ' u in Δ'u
    ... | Some τ'
      with frsh (τ' , Δ'u)
    ... | HFNEHole u≠u hf = abort (u≠u refl)
    weaken-ta-∪Δ {Δ' = Δ'} {Δ = Δ} {e = ⦇⌜ e ⌟⦈[ u ]}
                 frsh (TANEHole {τ = τ} u∈Δ wt)
        | None =
      TANEHole (dom-r-union Δ' Δ u τ u∈Δ Δ'u)
               (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFNEHole z≠u hf = hf
        
    weaken-rules-∪Δ : ∀{Γ Δ' Δ rs τ1 ξ τ2} →
                      (∀{u} →
                       dom Δ' u →
                       hole-fresh-rs u rs) →
                      Γ , Δ ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                      Γ , (Δ' ∪ Δ) ⊢ rs ::s τ1 [ ξ ]=> τ2
    weaken-rules-∪Δ {Δ' = Δ'} frsh (CTOneRule {r = p => e} rt) =
      CTOneRule (weaken-rule-∪Δ frsh' rt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh-r z (p => e)
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFRules hfr hfrs = hfr
    weaken-rules-∪Δ {Δ' = Δ'} frsh (CTRules {r = r} {rs = rs} rt rst) =
      CTRules (weaken-rule-∪Δ frshr rt)
              (weaken-rules-∪Δ frshrs rst)
      where
        frshr : ∀{z} →
                dom Δ' z →
                hole-fresh-r z r
        frshr z∈Δ' with frsh z∈Δ'
        ... | HFRules f frs = f
        frshrs : ∀{z} →
                 dom Δ' z →
                 hole-fresh-rs z rs
        frshrs z∈Δ' with frsh z∈Δ'
        ... | HFRules hf hfrs = hfrs
        
    weaken-rule-∪Δ : ∀{Γ Δ' Δ r τ1 ξ τ2} →
                     (∀{u} →
                      dom Δ' u →
                      hole-fresh-r u r) →
                     Γ , Δ ⊢ r :: τ1 [ ξ ]=> τ2 →
                     Γ , (Δ' ∪ Δ) ⊢ r :: τ1 [ ξ ]=> τ2
    weaken-rule-∪Δ {Γ = Γ} {Δ' = Δ'} {Δ = Δ} {τ2 = τ2} frsh
                   (CTRule {e = e} {Γp = Γp} {Δp = Δp} pt Γ##Γp Δ##Δp wt) =
      CTRule pt
             Γ##Γp
             (disjoint-parts Δ'##Δp Δ##Δp)
             (tr (λ qq → (Γ ∪ Γp) , qq ⊢ e :: τ2)
                 (! (∪-assoc Δ' Δ Δp))
                 (weaken-ta-∪Δ frsh' wt))
      where
        Δ'##Δp : Δ' ## Δp
        Δ'##Δp = disj1 , disj2
          where
            disj1 : (x : Nat) →
                    dom Δ' x →
                    x # Δp
            disj1 x x∈Δ' with frsh x∈Δ'
            ... | HFRule hub hf = hole-unbound-in-p-apart-Δp pt hub
            disj2 : (x : Nat) →
                    dom Δp x →
                    x # Δ'
            disj2 x x∈Δp
              with Δ' x in Δ'x
            ... | None = refl
            ... | Some τ1 
              with disj1 x (τ1 , Δ'x)
            ... | x#Δp = abort (some-not-none (! (π2 x∈Δp) · x#Δp))

        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFRule hub hf = hf

    -- Commutativity of union requires disjointness, so we
    -- make use of the identity
    -- Δ ∪ Δ' = Δ ⊔ (Δ' \ Δ) = (Δ' \ Δ) ⊔ Δ
    weaken-ta-Δ∪ : ∀{Γ Δ Δ' e τ} →
                   (∀{u} →
                    dom Δ' u →
                    hole-fresh u e) →
                   Γ , Δ ⊢ e :: τ →
                   Γ , (Δ ∪ Δ') ⊢ e :: τ
    weaken-ta-Δ∪ {Γ = Γ} {Δ = Δ} {Δ' = Δ'} {e = e} {τ = τ} frsh wt =
      tr (λ qq → Γ , qq ⊢ e :: τ)
         (! (union-with-diff Δ Δ' ·
             ∪-comm Δ (Δ' ∖ Δ) (r-disjoint-diff-r Δ' Δ)))
         (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom (Δ' ∖ Δ) z →
                hole-fresh z e
        frsh' {z = z} (τ , z∈Δ'∖Δ) =
          frsh (τ , dom-diff-dom-l {Γ1 = Δ'} {Γ2 = Δ} z∈Δ'∖Δ)
         
    -- convenience function
    weaken-ta-Δ : ∀{Γ Δ u τ' e τ} →
                  hole-fresh u e →
                  Γ , Δ ⊢ e :: τ →
                  Γ , (Δ ,, (u , τ')) ⊢ e :: τ
    weaken-ta-Δ {u = u} {τ' = τ'} {e = e} frsh wt =
      weaken-ta-∪Δ frsh' wt
      where
        frsh' : ∀{z} →
                dom (■ (u , τ')) z →
                hole-fresh z e
        frsh' d with dom-singleton-eq d
        ... | refl = frsh
