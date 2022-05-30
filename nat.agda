{-# OPTIONS --allow-unsolved-metas #-}
open import basic

infixl 10 _+_


-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data _≤_ : ℕ → ℕ → Set where
  base≤ : (x : ℕ) → x ≤ x
  step≤ : (x : ℕ) → (y : ℕ)  → x ≤ y → x ≤ (succ y)

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

x+0≡x : (x : ℕ) → x + zero ≡ x
x+0≡x zero     = refl
x+0≡x (succ x) = cong succ (x+0≡x x)

symm+ : (x y : ℕ) → x + y ≡ y + x
symm+ x zero     = x+0≡x x
symm+ zero     (succ y) = cong succ (symm (x+0≡x y))
symm+ (succ x) (succ y) = begin
  succ (x + succ y)   ≡⟨ cong succ (symm+ x (succ y))  ⟩
  succ (succ y + x)   ≡⟨⟩
  succ (succ (y + x)) ≡⟨ cong (λ v → succ (succ v)) (symm+ y x) ⟩
  succ (succ (x + y)) ≡⟨⟩
  succ (succ x + y)   ≡⟨ cong succ (symm+ (succ x) y) ⟩
  succ (y + succ x) ∎

-- succ (x + succ y)
-- ≡ succ (succ y + x)      by simm+
-- ≡ succ (succ (y + x))    by def of sum
-- ≡ succ (succ (x + y))    by simm+
-- ≡ succ (succ x + y)      by def of sum
-- ≡ succ (y + succ x)      by symm+




-- If the successors of two numbers are equals, then the two numbers are equal
-- x+1 ≡ y+1   ⇒   x ≡ y
x+1≡x+1-to-x≡y : {x y : ℕ} → succ x ≡ succ y → x ≡ y
x+1≡x+1-to-x≡y refl = refl

-- Zero is always less than a number of the form succ something.
0<x+1 : (x : ℕ) → zero < succ x
0<x+1 zero = base< zero
0<x+1 (succ x) = step< zero (succ x) (0<x+1 x)

-- x < y   ⇒   (x+1) < (y+1)
x<y-to-x+1<y+1 : (x : ℕ) (y : ℕ) → x < y → (succ x) < (succ y)
x<y-to-x+1<y+1 x (succ x) (base< x) = base< (succ x)
x<y-to-x+1<y+1 x (succ y) (step< x y p) = step< (succ x) (succ y) (x<y-to-x+1<y+1 x y p)

-- (x+1) < y   ⇒   x < y
x+1<y-to-x<y : (x : ℕ) (y : ℕ) → (succ x) < y → x < y
x+1<y-to-x<y x (succ (succ x)) (base< (succ x)) = step< x (succ x) (base< x)
x+1<y-to-x<y x (succ y) (step< (succ x) y p)    = step< x y (x+1<y-to-x<y x y p)

-- (x+1) < (y+1)   ⇒   x < y
x+1<y+1-to-x<y : (x : ℕ) (y : ℕ) → (succ x) < (succ y) → x < y
x+1<y+1-to-x<y x (succ x) (base< (succ x)) = base< x
x+1<y+1-to-x<y x y (step< (succ x) y p)    = x+1<y-to-x<y x y p

-- 0 ≤ x    for any x
0≤x : (x : ℕ) → zero ≤ x
0≤x zero     = base≤ zero
0≤x (succ x) = step≤ zero x (0≤x x)

-- x ≤ y   ⇒   (x+1) ≤ (y+1)
x≤y-to-x+1≤y+1 : (x : ℕ) (y : ℕ) → x ≤ y → (succ x) ≤ (succ y)
x≤y-to-x+1≤y+1 x x (base≤ x)            = base≤ (succ x)
x≤y-to-x+1≤y+1 x (succ y) (step≤ x y p) = step≤ (succ x) (succ y) (x≤y-to-x+1≤y+1 x y p)

-- (x+1) ≤ y   ⇒   x ≤ y
x+1≤y-to-x≤y : (x : ℕ) (y : ℕ) → succ x ≤ y → x ≤ y
x+1≤y-to-x≤y x (succ x) (base≤ (succ x))     = step≤ x x (base≤ x)
x+1≤y-to-x≤y x (succ y) (step≤ (succ x) y p) = step≤ x y (x+1≤y-to-x≤y x y p)

-- (x+1) ≤ (y+1)   ⇒   x ≤ y
x+1≤y+1-to-x≤y : (x : ℕ) (y : ℕ) → (succ x) ≤ (succ y) → x ≤ y
x+1≤y+1-to-x≤y x x (base≤ (succ x))     = base≤ x
x+1≤y+1-to-x≤y x y (step≤ (succ x) y p) = x+1≤y-to-x≤y x y p

-- x > y   ⇒   (x+1) > (y+1)
x>y-to-x+1>y+1 : (x : ℕ) (y : ℕ) → x > y → (succ x) > (succ y)
x>y-to-x+1>y+1 x y x>y = λ p → x>y (x+1≤y+1-to-x≤y x y p)

-- (x+1) > (y+1)   ⇒   x > y
x+1>y+1-to-x>y : (x : ℕ) (y : ℕ) → (succ x) > (succ y) → x > y
x+1>y+1-to-x>y x y p = λ p1 → p (x≤y-to-x+1≤y+1 x y p1)

-- (x+1) ≥ (y+1)   ⇒   x ≥ y
x+1≥y+1-to-x≥y : (x : ℕ) (y : ℕ) → (succ x) ≥ (succ y) → x ≥ y
x+1≥y+1-to-x≥y x y p = λ p1 → p (x<y-to-x+1<y+1 x y p1)

-- x-1 < y   ⇒   x < y+1
x-1<y-to-x<y+1 : (x : ℕ) (y : ℕ) → pred x < y → x < succ y
x-1<y-to-x<y+1 zero .(succ zero) (base< .zero)      = step< zero (succ zero) (base< zero)
x-1<y-to-x<y+1 (succ x) .(succ x) (base< .x)        = base< (succ x)
x-1<y-to-x<y+1 x .(succ y) (step< .(pred x) y p)    = step< x (succ y) (x-1<y-to-x<y+1 x y p)

-- x ≥ y+1   ⇒   x-1 ≥ y
x≥y+1-to-x-1≥y : (x : ℕ) (y : ℕ) → x ≥ succ (y) → pred x ≥ y
x≥y+1-to-x-1≥y x y p = λ p1 → p (x-1<y-to-x<y+1 x y p1)

-- x ≥ y+1   ⇒   x ≥ y
x≥y+1-to-x≥y : (x : ℕ) (y : ℕ) → x ≥ succ y → x ≥ y
x≥y+1-to-x≥y x y p = λ p1 → p (step< x y p1)

-- x+1 < y   ⇒   x < y+1
x+1<y-to-x<y+1 : (x y : ℕ) → succ x < y → x < succ y
x+1<y-to-x<y+1 x .(succ (succ x)) (base< .(succ x)) = step< x (succ (succ x)) (step< x (succ x) (base< x))
x+1<y-to-x<y+1 x .(succ y) (step< .(succ x) y p)    = step< x (succ y) (x+1<y-to-x<y+1 x y p)

-- x+1 < y+1   ⇒   x < y+1
x+1<y+1-to-x<y+1 : (x : ℕ) (y : ℕ) → succ x < succ y → x < succ y
x+1<y+1-to-x<y+1 x .(succ x) (base< .(succ x))  = step< x (succ x) (base< x)
x+1<y+1-to-x<y+1 x y (step< (succ x) y p)       = x+1<y-to-x<y+1 x y p

-- x ≥ y   ⇒   x+1 ≥ y
x≥y-to-x+1≥y : (x : ℕ) → (y : ℕ) → x ≥ y → succ x ≥ y
x≥y-to-x+1≥y x y p = λ p1 → p (x+1<y-to-x<y x y p1)

x<y-to-x≢y : {x y : ℕ} → x < y → x ≢ y
x<y-to-x≢y (base< x) ()
x<y-to-x≢y (step< x y p) p1 = {!!}

x>y-to-x≢y : {x y : ℕ} → x > y → x ≢ y
x>y-to-x≢y = {!!}

x≥y-to-x+1>y : {x y : ℕ} → x ≥ y → succ x > y
x≥y-to-x+1>y = {!!}

-- 0 < 0 is absurd
0<0-to-⊥ : zero < zero → ⊥
0<0-to-⊥ ()

-- x < x is absurd
x<x-to-⊥ : (x : ℕ) → x < x → ⊥
x<x-to-⊥ zero ()
x<x-to-⊥ (succ x) = λ p → x<x-to-⊥ x (x+1<y+1-to-x<y x x p)

-- x+1 > 0   for any x
x+1>0 : (x : ℕ) → succ x > zero
x+1>0 zero     = λ ()
x+1>0 (succ x) = λ ()

-- x ≥ y+1   ⇒   x > zero
x≥y+1-to-x≥0 : (x : ℕ) → (y : ℕ) → x ≥ succ y → x > zero
x≥y+1-to-x≥0 zero     y p = absurd (p (0<x+1 y))
x≥y+1-to-x≥0 (succ x) y p = x+1>0 x

x≡y-to-x≥y : (x y : ℕ) → x ≡ y → x ≥ y
x≡y-to-x≥y x x refl = λ p → x<x-to-⊥ x p

x≡y-to-x-y≡0 : (x y : ℕ) → x ≡ y → (x - y) ≡ zero
x≡y-to-x-y≡0 zero     zero     refl = refl
x≡y-to-x-y≡0 (succ x) (succ x) refl = x≡y-to-x-y≡0 x x refl

-- Equality test for natural numbers.
-- Given two numbers it provides either a proof that those number are equals or
-- a proof that those numbers are not equal.
_≡?_ : (x : ℕ) → (y : ℕ) → ((x ≡ y) ⊎ (x ≢ y))
zero     ≡? zero       = left refl
zero     ≡? (succ y)   = right (λ ())
(succ x) ≡? zero       = right (λ ())
(succ x) ≡? (succ y) with x ≡? y
... | left  p          = left (cong succ p)
... | right p          = right λ p1 → p (x+1≡x+1-to-x≡y p1)

_<?_ : (x : ℕ) → (y : ℕ) → ((x < y) ⊎ (x ≥ y))
zero   <? zero         = right (λ ())
zero   <? succ y       = left (0<x+1 y)
succ x <? zero         = right (λ ())
succ x <? succ y with x <? y
... | left  p          = left (x<y-to-x+1<y+1 x y p)
... | right p          = right λ p1 → p (x+1<y+1-to-x<y x y p1)

_≤?_ : (x : ℕ) → (y : ℕ) → ((x ≤ y) ⊎ (x > y))
zero   ≤? zero         = left (base≤ zero)
zero   ≤? succ y       = left (0≤x (succ y))
succ x ≤? zero         = right (λ ())
succ x ≤? succ y with x ≤? y
... | left  x≤y        = left (x≤y-to-x+1≤y+1 x y x≤y)
... | right x>y        = right (x>y-to-x+1>y+1 x y x>y)

-- The comparison of an element with itself always results in a proof of equality.
-- Comparing x with x, you always get an element of x≡x.
x≡x : (x : ℕ) → ((x ≡? x) ≡ left refl)
x≡x zero        = refl
x≡x (succ x) with x ≡? x
... | left refl = refl
... | right p   = absurd (p refl)

max : ℕ → ℕ → ℕ
max a b with a ≤? b
... | left  a≤b = b
... | right a>b = a

0≥x+1-to-⊥ : (x : ℕ) → zero ≥ succ x → ⊥
0≥x+1-to-⊥ zero     p = p (base< zero)
0≥x+1-to-⊥ (succ x) p = 0≥x+1-to-⊥ x (λ z → p (step< zero (succ x) z))

x+1≢y+1-to-x≢y : {x y : ℕ} → succ x ≢ succ y → x ≢ y
x+1≢y+1-to-x≢y p = λ p1 → p (cong succ p1)

-- x ≥ y and x ≢ y   ⇒   x > y
x≥y-and-x≢y-to-x>y : {x y : ℕ} → x ≥ y → x ≢ y → x > y
x≥y-and-x≢y-to-x>y {zero}   {zero}   p1 p2 = absurd (p2 refl)
x≥y-and-x≢y-to-x>y {zero}   {succ y} p1 p2 = absurd (0≥x+1-to-⊥ y p1)
x≥y-and-x≢y-to-x>y {succ x} {zero}   p1 p2 = λ ()
x≥y-and-x≢y-to-x>y {succ x} {succ y} p1 p2 = x>y-to-x+1>y+1 x y (x≥y-and-x≢y-to-x>y (x+1≥y+1-to-x≥y x y p1) (x+1≢y+1-to-x≢y p2))

-- a ≥ b   ⇒   (a - b) + 1 ≡ (a+1) - b
-- This is not true for a < b.
-- (2 - 3) + 1 = 1 while (2 + 1) - 3 = 0    because    (2-3) = 0
eq-minus-succ : (a : ℕ) (b : ℕ) → a ≥ b → succ (a - b) ≡ succ a - b
eq-minus-succ a        zero     p1 = refl
eq-minus-succ zero     (succ b) p1 = absurd (p1 (0<x+1 b))
eq-minus-succ (succ a) (succ b) p1 = eq-minus-succ a b (x+1≥y+1-to-x≥y a b p1)
