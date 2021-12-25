open import Prelude

module Nat where
  data Nat : Set where
    Z : Nat
    1+ : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}

  -- the succ operation is injective
  1+inj : (x y : Nat) → (1+ x == 1+ y) → x == y
  1+inj Z .0 refl = refl
  1+inj (1+ x) .(1+ x) refl = refl

  -- equality of naturals is decidable. we represent this as computing a
  -- choice of units, with inl <> meaning that the naturals are indeed the
  -- same and inr <> that they are not.
  natEQ : (x y : Nat) → ((x == y) + ((x == y) → ⊥))
  natEQ Z Z = Inl refl
  natEQ Z (1+ y) = Inr (λ ())
  natEQ (1+ x) Z = Inr (λ ())
  natEQ (1+ x) (1+ y) with natEQ x y
  natEQ (1+ x) (1+ .x) | Inl refl = Inl refl
  ... | Inr b = Inr (λ x₁ → b (1+inj x y x₁))

  -- nat equality as a predicate. this saves some very repetetive casing.
  natEQp : (x y : Nat) → Set
  natEQp x y with natEQ x y
  natEQp x .x | Inl refl = ⊥
  natEQp x y | Inr x₁ = ⊤
  
  _nat+_ : Nat → Nat → Nat
  Z nat+ y = y
  1+ x nat+ y = 1+ (x nat+ y)

  max : Nat → Nat → Nat
  max Z n = n
  max (1+ m) Z = 1+ m
  max (1+ m) (1+ n) = 1+ (max m n)

  max-is-arg : (m n : Nat) →
               (max m n == m) + (max m n == n)
  max-is-arg Z n = Inr refl
  max-is-arg (1+ m) Z = Inl refl
  max-is-arg (1+ m) (1+ n)
    with max-is-arg m n
  ... | Inl max=m = Inl (ap1 (λ qq → 1+ qq) max=m)
  ... | Inr max=n = Inr (ap1 (λ qq → 1+ qq) max=n)

  max-comm : (m n : Nat) →
             (max m n == max n m)
  max-comm Z Z = refl
  max-comm Z (1+ n) = refl
  max-comm (1+ m) Z = refl
  max-comm (1+ m) (1+ n)
    with max-comm m n
  ... | xmn=xnm = ap1 (λ qq → 1+ qq) xmn=xnm

  data _<_ : Nat → Nat → Set where
    z<1+ : ∀{n} → Z < (1+ n)
    1+<1+ : ∀{m n} → m < n → (1+ m) < (1+ n)

  n<1+n : (n : Nat) →
          n < (1+ n)
  n<1+n Z = z<1+
  n<1+n (1+ n) = 1+<1+ (n<1+n n)

  <→≠ : ∀{n m} →
        n < m →
        n ≠ m
  <→≠ (1+<1+ m<m) refl = <→≠ m<m refl

  max<→arg1< : ∀{m n x} →
               max m n < x →
               m < x
  max<→arg1< {m = Z} {n = Z} z<1+ = z<1+
  max<→arg1< {m = Z} {n = 1+ n} (1+<1+ max<x) = z<1+
  max<→arg1< {m = 1+ m} {n = Z} (1+<1+ max<x) = 1+<1+ max<x
  max<→arg1< {m = 1+ m} {n = 1+ n} (1+<1+ max<x) = 1+<1+ (max<→arg1< max<x)

  max<→arg2< : ∀{m n x} →
               max m n < x →
               n < x
  max<→arg2< {m = Z} {n = Z} z<1+ = z<1+
  max<→arg2< {m = Z} {n = 1+ n} (1+<1+ max<x) = 1+<1+ max<x
  max<→arg2< {m = 1+ m} {n = Z} (1+<1+ max<x) = z<1+
  max<→arg2< {m = 1+ m} {n = 1+ n} (1+<1+ max<x) = 1+<1+ (max<→arg2< max<x)
