--{-# OPTIONS --allow-unsolved-metas #-}

data ⊥ : Set where

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
  and : (a : A) (b : B) → A & B

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

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

data List {A : Set} : Set where
  []  : List {A}
  _∷_ : (x : A) → (xs : List {A}) → List {A} 

-- List concatenation
_++_ : {A : Set} → List {A} → List {A} → List {A}
[] ++ l2       = l2
(x ∷ l1) ++ l2 = x ∷ (l1 ++ l2)

-- Remove the given element from a list of integers
_remove_ : List → (x : ℕ) → List
[] remove x = []
(x ∷ xs) remove y with x ≡? y
... | left p = xs remove y                -- x equals y
... | right p = x ∷ (xs remove y)      -- x not equals y


-- The element x is in the list
data _∈_ {A : Set} : (x : A) → List → Set where
  in-head : (x : A) (xs : List) → x ∈ (x ∷ xs)
  in-tail : (x y : A) (xs : List) → x ∈ xs → x ∈ (y ∷ xs)

data _≤_ : ℕ → ℕ → Set where
  x≤x : (x : ℕ) → x ≤ x
  x≤succ : (x : ℕ) → (y : ℕ)  → x ≤ y → x ≤ (succ y)

_>_ : ℕ → ℕ → Set
x > y = ¬ (x ≤ y)

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

_≤?_ : (x : ℕ) → (y : ℕ) → ((x ≤ y) ⊎ (x > y))
zero ≤? zero = left (x≤x zero)
zero ≤? succ y = left (lemma-zero-≤ (succ y))
succ x ≤? zero = right (λ ())
succ x ≤? succ y with x ≤? y
... | left x≤y = left (lemma-succ-≤ x y x≤y)
... | right x>y = right (lemma-succ-> x y x>y)

-- Get the max value of a list
getMax : List {ℕ} → ℕ
getMax [] = zero
getMax (x ∷ xs) with x ≤? (getMax xs)
... | left p    = getMax xs
... | right p  = x

max : ℕ → ℕ → ℕ
max a b with a ≤? b
... | left a≤b = b
... | right a>b = a

-- xs ++ [] = xs
lemma-list1 : {A : Set} (xs : List {A}) → (xs ++ []) ≡ xs
lemma-list1 [] = refl
lemma-list1 (x ∷ xs) = cong (λ y → x ∷ y) (lemma-list1 xs)

lemma-in-not-first : {A : Set} (z x : A) (xs : List) → ¬ (z ∈ (x ∷ xs)) → ¬ (z ∈ xs)
lemma-in-not-first z x xs p1 = λ p2 → p1 (in-tail z x xs p2)

in-first-in-concat : {A : Set} (z : A) (xs : List) (ys : List) →  z ∈ xs → z ∈ (xs ++ ys)
in-first-in-concat x (x ∷ xs) ys (in-head x xs) = in-head x (xs ++ ys)
in-first-in-concat x (y ∷ xs) ys (in-tail x y xs p) = in-tail x y (xs ++ ys) (in-first-in-concat x xs ys p)

in-second-in-concat : {A : Set} (z : A) (xs : List) (ys : List) →  z ∈ ys → z ∈ (xs ++ ys)
in-second-in-concat z [] ys p = p
in-second-in-concat z (x ∷ xs) ys p = in-tail z x (xs ++ ys) (in-second-in-concat z xs ys p)

not-in-concat-not-in-first : {A : Set} (z : A) (xs : List) (ys : List) →  ¬ (z ∈ (xs ++ ys)) → ¬ (z ∈ xs)
not-in-concat-not-in-first z xs ys p = λ inFirst → p (in-first-in-concat z xs ys inFirst)

not-in-concat-not-in-second : {A : Set} (z : A) (xs : List) (ys : List) →  ¬ (z ∈ (xs ++ ys)) → ¬ (z ∈ ys)
not-in-concat-not-in-second z xs ys p = λ inSecond → p (in-second-in-concat z xs ys inSecond)


