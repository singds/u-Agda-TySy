{-# OPTIONS --allow-unsolved-metas #-}
infixl 10 _+_
infixl 9  _≡_


data ⊥ : Set where

data Opt : {A : Set} → Set where
    none : {A : Set} → Opt {A}
    some : {A : Set} → A → Opt {A}

-- Negation
¬_ : Set → Set
¬ X = X → ⊥ 

-- From a value of type ⊥ (bottom) I can derive whatever I want.
-- Actually there are no values of type ⊥.
absurd : {A : Set} → ⊥ → A
absurd ()

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}
-- to use the rewrite keyword

_≢_ : {A : Set} → A → A → Set
x ≢ y = ((x ≡ y) → ⊥)

-- disjoint union
data _⊎_ (A B : Set) : Set where
  left   : A → A ⊎ B
  right : B → A ⊎ B

-- If you know that can't be a proof of B, you can get a proof of A
⊎-getA : {A B : Set} → A ⊎ B → (B → ⊥) → A
⊎-getA (left x) f = x
⊎-getA (right x) f with f x
... | ()

-- If you know that can't be a proof of A, you can get a proof of B
⊎-getB : {A B : Set} → A ⊎ B → (A → ⊥) → B
⊎-getB (left x) f with f x
... | ()
⊎-getB (right x) f = x

-- Existential quantifier
-- B is a set that is dependent on A
data ∃ (A : Set) (B : A → Set) : Set where
  exists : (a : A) (b : B a) → ∃ A B

-- A holds and B holds
-- There must be a proof of A and a proof of B
data _&_ (A : Set) (B : Set) : Set where
  _and_ : (a : A) (b : B) → A & B

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

one = succ zero

-- Congruence
cong : {A B : Set} {x y : A} → (f : A → B) → (x ≡ y) → (f x ≡ f y)
cong f refl = refl

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

symm≢ : {A : Set} {x y : A} → x ≢ y → y ≢ x
symm≢ p1 = λ p2 → p1 (symm p2)

-- If the successors of two numbers are equals, then the two numbers are equal
succ-eq-pred-eq : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-eq-pred-eq refl = refl

-- Comparator for natual numbers
-- Given two numbers it provides either a proof that those number are equals or
-- a proof that those numbers are not equal.
_≡?_ : (x : ℕ) → (y : ℕ) → ((x ≡ y) ⊎ (x ≢ y))
zero ≡? zero = left refl
zero ≡?  (succ y) = right (λ ())
(succ x) ≡? zero = right (λ ())
(succ x) ≡? (succ y) with x ≡? y
... | left p  = left (cong succ p)
... | right p = right λ pSuccEq → p (succ-eq-pred-eq pSuccEq)

-- The comparison of an element with itself always results in a proof of equality.
-- Comparing x with x, you can't get a proof that x ≢ x
x≡x : (x : ℕ) → ((x ≡? x) ≡ left refl)
x≡x zero = refl
x≡x (succ x) with x ≡? x
x≡x (succ x) | left refl = refl
... | right p = absurd (p refl)

-- Sum of natural numbers
_+_ : ℕ → ℕ → ℕ
zero + b   = b
succ a + b = succ (a + b)

pred : ℕ → ℕ
pred zero = zero
pred (succ a) = a

_-_ : ℕ → ℕ → ℕ
a - zero = a
a - (succ b) = (pred a) - b

symm+ : (x y : ℕ) → x + y ≡ y + x
symm+ = {!!}


data _≤_ : ℕ → ℕ → Set where
  x≤x : (x : ℕ) → x ≤ x
  x≤succ : (x : ℕ) → (y : ℕ)  → x ≤ y → x ≤ (succ y)

_>_ : ℕ → ℕ → Set
x > y = ¬ (x ≤ y)

data _<_ : ℕ → ℕ → Set where
  base< : (x : ℕ) → x < (succ x)
  step< : (x : ℕ) → (y : ℕ)  → x < y → x < (succ y)

_≥_ : ℕ → ℕ → Set
x ≥ y = ¬ (x < y)

lemma-zero-≤ : (x : ℕ) → zero ≤ x
lemma-zero-≤ zero = x≤x zero
lemma-zero-≤ (succ x) = x≤succ zero x (lemma-zero-≤ x)

lemma-succ-≤ : (x : ℕ) (y : ℕ) → x ≤ y → (succ x) ≤ (succ y)
lemma-succ-≤ x x (x≤x x) = x≤x (succ x)
lemma-succ-≤ x (succ y) (x≤succ x y p) = x≤succ (succ x) (succ y) (lemma-succ-≤ x y p)

lemma-pred1-≤ : (x : ℕ) (y : ℕ) → succ x ≤ y → x ≤ y
lemma-pred1-≤ x (succ x) (x≤x (succ x)) = x≤succ x x (x≤x x)
lemma-pred1-≤ x (succ y) (x≤succ (succ x) y p) = x≤succ x y (lemma-pred1-≤ x y p)

lemma-pred-≤ : (x : ℕ) (y : ℕ) → (succ x) ≤ (succ y) → x ≤ y
lemma-pred-≤ x x (x≤x (succ x)) = x≤x x
lemma-pred-≤ x y (x≤succ (succ x) y p) = lemma-pred1-≤ x y p

lemma-succ-> : (x : ℕ) (y : ℕ) → x > y → (succ x) > (succ y)
lemma-succ-> x y x>y = λ p → x>y (lemma-pred-≤ x y p)

-- Zero is always less than a number of the form succ something
lemma-zero-<-succ : (x : ℕ) → zero < succ x
lemma-zero-<-succ zero = base< zero
lemma-zero-<-succ (succ x) = step< zero (succ x) (lemma-zero-<-succ x)

-- If x < y, then (x + 1) < (y + 1)
lemma-succ-<-succ : (x : ℕ) → (y : ℕ) → x < y → (succ x) < (succ y)
lemma-succ-<-succ x (succ x) (base< x) = base< (succ x)
lemma-succ-<-succ x (succ y) (step< x y p) = step< (succ x) (succ y) (lemma-succ-<-succ x y p)

lemma-succ-< : (x : ℕ) → (y : ℕ) → (succ x) < y → x < y
lemma-succ-< x (succ (succ x)) (base< (succ x)) = step< x (succ x) (base< x)
lemma-succ-< x (succ y) (step< (succ x) y p) = step< x y (lemma-succ-< x y p)

lemma-pred-< : (x : ℕ) → (y : ℕ) → (succ x) < (succ y) → x < y
lemma-pred-< x (succ x) (base< (succ x)) = base< x
lemma-pred-< x y (step< (succ x) y p) = lemma-succ-< x y p

lemma-pred-≥-pred : (x : ℕ) → (y : ℕ) → (succ x) ≥ (succ y) → x ≥ y
lemma-pred-≥-pred x y p = λ p1 → p (lemma-succ-<-succ x y p1)


lemma-pred-<' : (x : ℕ) → (y : ℕ)
                → pred x < y
                → x < succ y
lemma-pred-<' zero .(succ zero) (base< .zero) = step< zero (succ zero) (base< zero)
lemma-pred-<' (succ x) .(succ x) (base< .x) = base< (succ x)
lemma-pred-<' x .(succ y) (step< .(pred x) y p)    = step< x (succ y) (lemma-pred-<' x y p)

lemma-pred-≥ : (x : ℕ) → (y : ℕ)
             → x ≥ succ (y)
             → pred x ≥ y
lemma-pred-≥ x y p = λ p1 → p (lemma-pred-<' x y p1)

lemma-≥-1 : (x : ℕ) → (y : ℕ)
          → x ≥ succ y
          → x ≥ y
lemma-≥-1 x y p = λ p1 → p (step< x y p1)

lemma->-1 : (x : ℕ) → (y : ℕ)
          → x ≥ succ y
          → x > zero
lemma->-1 x y p = {!!}



_≤?_ : (x : ℕ) → (y : ℕ) → ((x ≤ y) ⊎ (x > y))
zero ≤? zero = left (x≤x zero)
zero ≤? succ y = left (lemma-zero-≤ (succ y))
succ x ≤? zero = right (λ ())
succ x ≤? succ y with x ≤? y
... | left x≤y = left (lemma-succ-≤ x y x≤y)
... | right x>y = right (lemma-succ-> x y x>y)

_<?_ : (x : ℕ) → (y : ℕ) → ((x < y) ⊎ (x ≥ y))
zero <? zero = right (λ ())
zero <? succ y = left (lemma-zero-<-succ y)
succ x <? zero = right (λ ())
succ x <? succ y with x <? y
... | left p = left (lemma-succ-<-succ x y p)
... | right p = right λ p1 → p (lemma-pred-< x y p1)

max : ℕ → ℕ → ℕ
max a b with a ≤? b
... | left a≤b = b
... | right a>b = a


opt-eq : {A : Set} {x y : A} → some x ≡ some y → x ≡ y
opt-eq refl = refl

opt-eq1 : {A : Set} {x y : A} → x ≡ y → some x ≡ some y
opt-eq1 refl = refl



x-ge-x-neq-x-gt : {x n : ℕ} → x ≥ n → x ≢ n → x > n
x-ge-x-neq-x-gt p1 p2 = {!   !}
