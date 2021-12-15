open import Prelude
open import Nat

module List where
  -- lets us omit a bunch of parens
  infixr 5 _::_
  infixr 5 _++_

  -- standard definition of polymorphic lists
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  {-# BUILTIN LIST List #-}
  
  -- shorthand notation for small lists
  [_] : {A : Set} → A → List A
  [ x ] = x :: []
  
  -- list append. efficiency who?
  _++_ : {A : Set} → List A → List A → List A
  [] ++ l2 = l2
  (x :: l1) ++ l2 = x :: (l1 ++ l2)

  -- list reverse. efficiency who?
  reverse : {A : Set} → List A → List A
  reverse [] = []
  reverse (x :: l) = l ++ [ x ]
  
