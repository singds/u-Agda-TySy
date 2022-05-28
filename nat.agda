{-# OPTIONS --allow-unsolved-metas #-}
open import basic

infixl 10 _+_


-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

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



-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

one = succ zero
two = succ (succ zero)

_+_ : ℕ → ℕ → ℕ
zero   + b  = b
succ a + b  = succ (a + b)

pred : ℕ → ℕ
pred zero     = zero
pred (succ a) = a

_-_ : ℕ → ℕ → ℕ
a - zero     = a
a - (succ b) = (pred a) - b


symm+ : (x y : ℕ) → x + y ≡ y + x
symm+ = {!!}




-- If the successors of two numbers are equals, then the two numbers are equal
-- x+1 ≡ y+1   ⇒   x ≡ y
eq-plus-one-lr : {x y : ℕ} → succ x ≡ succ y → x ≡ y
eq-plus-one-lr refl = refl

-- 
-- Comparator for natual numbers.
-- Given two numbers it provides either a proof that those number are equals or
-- a proof that those numbers are not equal.
_≡?_ : (x : ℕ) → (y : ℕ) → ((x ≡ y) ⊎ (x ≢ y))
zero     ≡? zero       = left refl
zero     ≡? (succ y)   = right (λ ())
(succ x) ≡? zero       = right (λ ())
(succ x) ≡? (succ y) with x ≡? y
... | left  p          = left (cong succ p)
... | right p          = right λ p1 → p (eq-plus-one-lr p1)


-- The comparison of an element with itself always results in a proof of equality.
-- Comparing x with x, you can't get a proof that x ≢ x
x≡x : (x : ℕ) → ((x ≡? x) ≡ left refl)
x≡x zero = refl
x≡x (succ x) with x ≡? x
x≡x (succ x) | left refl = refl
... | right p = absurd (p refl)



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

lemma-pred-> : (x : ℕ) (y : ℕ) → (succ x) > (succ y) → x > y
lemma-pred-> x y p = λ p1 → p (lemma-succ-≤ x y p1)

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

lemma-pred-<-2 : (x : ℕ) (y : ℕ) → succ x < succ y → x < succ y
lemma-pred-<-2 x .(succ x) (base< .(succ x)) = step< x (succ x) (base< x)
lemma-pred-<-2 x y (step< .(succ x) .y p) = {!!}

lemma-pred-<-3 : (x : ℕ) (y : ℕ) → succ x < y → (x < y)
lemma-pred-<-3 x (succ y) p = lemma-pred-<-2 x y p

lemma-≥-2 : (x : ℕ) → (y : ℕ)
          → x ≥ y
          → succ x ≥ y
lemma-≥-2 x y p = λ p1 → p (lemma-pred-<-3 x y p1)

lemma->-1 : (x : ℕ) → (y : ℕ)
          → x ≥ succ y
          → x > zero
lemma->-1 x y p = {!!}

0<0-to-⊥ : zero < zero → ⊥
0<0-to-⊥ ()

x<x-to-⊥ : (x : ℕ) → x < x → ⊥
x<x-to-⊥ zero ()
x<x-to-⊥ (succ x) = λ p → x<x-to-⊥ x (lemma-pred-< x x p)

x≡y-to-x≥y : (x y : ℕ) → x ≡ y → x ≥ y
x≡y-to-x≥y x x refl = λ p → x<x-to-⊥ x p

x-x≡0 : (x y : ℕ) → x ≡ y → (x - y) ≡ zero
x-x≡0 zero     zero     refl = refl
x-x≡0 (succ x) (succ x) refl = x-x≡0 x x refl


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



x-ge-x-neq-x-gt : {x n : ℕ} → x ≥ n → x ≢ n → x > n
x-ge-x-neq-x-gt p1 p2 = {!!}

eq-minus-succ : (a : ℕ) (b : ℕ)
  → a ≥ b
  → succ (a - b) ≡ succ a - b
eq-minus-succ a        zero     p1 = refl
eq-minus-succ zero     (succ b) p1 = absurd (p1 (lemma-zero-<-succ b))
eq-minus-succ (succ a) (succ b) p1 = eq-minus-succ a b (lemma-pred-≥-pred a b p1)
