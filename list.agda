{-# OPTIONS --allow-unsolved-metas #-}
open import basic
open import nat

infixr 11 _∷_

-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

data List {A : Set} : Set where
  []  : List
  _∷_ : (x : A) → (xs : List {A}) → List

-- The element x is in the list
data _∈_ {A : Set} : (x : A) → List → Set where
  in-head : (x : A)   (xs : List)            → x ∈ (x ∷ xs)
  in-tail : (x y : A) (xs : List)  → x ∈ xs  → x ∈ (y ∷ xs)

_∉_ : {A : Set} (x : A) → List → Set
x ∉ xs = ((x ∈ xs) → ⊥)


-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

-- List concatenation
_++_ : {A : Set} → List {A} → List {A} → List {A}
[] ++ ys        = ys
(x ∷ xs) ++ ys  = x ∷ (xs ++ ys)

-- Compute the lenght of a list.
len : {A : Set} → List {A} → ℕ
len []       = zero
len (x ∷ xs) = succ (len xs)

-- Remove all the numbers euqal to x from the list
_remove_ : List → (x : ℕ) → List
[] remove x   = []
(x ∷ xs) remove y with x ≡? y
... | left  p = xs remove y            -- x equals y
... | right p = x ∷ (xs remove y)      -- x not equals y

-- Get an element by index.
-- Returns an option that is none when the index is too big.
getIdx : {A : Set} → List {A} → ℕ → Opt {A}
getIdx [] n              = none
getIdx (x ∷ xs) zero     = some x
getIdx (x ∷ xs) (succ n) = getIdx xs n

-- Get the max value in a list of natural numbers.
-- Zero is returned if the list is empty.
getMax : List {ℕ} → ℕ
getMax []      = zero
getMax (x ∷ xs) with x ≤? (getMax xs)
... | left  p  = getMax xs
... | right p  = x

-- Decrement all numbers of the list.
decAll : List {ℕ} → List {ℕ}
decAll [] = []
decAll (x ∷ xs) = pred x ∷ decAll xs



-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

-- x ∉ (x ∷ xs)   ⇒   z ∉ xs
not-in-list-not-in-tail : {A : Set} (z x : A) (xs : List) → z ∉ (x ∷ xs) → z ∉ xs
not-in-list-not-in-tail z x xs p1 = λ p2 → p1 (in-tail z x xs p2)

-- z ∈ xs   ⇒   z ∈ (xs ++ ys)
in-first-in-concat : {A : Set} (z : A) (xs : List) (ys : List) → z ∈ xs → z ∈ (xs ++ ys)
in-first-in-concat x (x ∷ xs) ys (in-head x xs)     = in-head x (xs ++ ys)
in-first-in-concat x (y ∷ xs) ys (in-tail x y xs p) = in-tail x y (xs ++ ys) (in-first-in-concat x xs ys p)

-- z ∈ ys   ⇒   z ∈ (xs ++ ys)
in-second-in-concat : {A : Set} (z : A) (xs : List) (ys : List) → z ∈ ys → z ∈ (xs ++ ys)
in-second-in-concat z []       ys p  = p
in-second-in-concat z (x ∷ xs) ys p  = in-tail z x (xs ++ ys) (in-second-in-concat z xs ys p)

-- z ∉ (xs ++ ys)   ⇒   z ∉ xs
not-in-concat-not-in-first : {A : Set} (z : A) (xs : List) (ys : List) → z ∉ (xs ++ ys) → z ∉ xs
not-in-concat-not-in-first z xs ys p = λ inFirst → p (in-first-in-concat z xs ys inFirst)

-- z ∉ (xs ++ ys)   ⇒   z ∉ ys
not-in-concat-not-in-second : {A : Set} (z : A) (xs : List) (ys : List) →  z ∉ (xs ++ ys) → z ∉ ys
not-in-concat-not-in-second z xs ys p = λ inSecond → p (in-second-in-concat z xs ys inSecond)

-- x+1 ∈ xs   ⇒   x ∈ (decAll xs)
succ-in-list-in-dec : {x : ℕ} {xs : List {ℕ}}
    → succ x ∈ xs
    → x ∈ (decAll xs)
succ-in-list-in-dec {x} (in-head (succ _) xs)           = in-head x (decAll xs)
succ-in-list-in-dec {x} {xs} (in-tail (succ _) y xs' p) = in-tail x (pred y) (decAll xs') (succ-in-list-in-dec p)

-- x ∉ (decAll xs)   ⇒   x+1 ∉ xs
notin-dec-not-succ-in-list : {x : ℕ} {xs : List {ℕ}}
    → x ∉ (decAll xs)
    → succ x ∉ xs
notin-dec-not-succ-in-list p = λ p1 → p (succ-in-list-in-dec p1)

-- x+1 ∈ xs   ⇒   x ∈ (decAll (xs \ 0))
succ-in-list-in-dec' : {x : ℕ} {xs : List {ℕ}}
    → succ x ∈ xs
    → x ∈ (decAll (xs remove zero))
succ-in-list-in-dec' {x} {.(succ x ∷ xs)} (in-head .(succ x) xs) = in-head x (decAll (xs remove zero))
succ-in-list-in-dec' {x} {.(y ∷ xs)} (in-tail .(succ x) y xs p) with y ≡? zero 
... | left  p1 = succ-in-list-in-dec' p
... | right p1 = in-tail x (pred y) (decAll (xs remove zero)) (succ-in-list-in-dec' p)

-- x ∉ (decAll (xs \ 0))   ⇒   x+1 ∉ xs
notin-dec-not-succ-in-list' : {x : ℕ} {xs : List {ℕ}}
    → x ∉ (decAll (xs remove zero))
    → succ x ∉ xs
notin-dec-not-succ-in-list' p = λ p1 → p (succ-in-list-in-dec' p1) 

-- xs ++ [] ≡ xs
xs++[]≡xs : {A : Set} → (xs : List {A}) → xs ++ [] ≡ xs
xs++[]≡xs [] = refl
xs++[]≡xs (x ∷ xs) = cong (λ list → x ∷ list) (xs++[]≡xs xs)



-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

-- xs ++ [] = xs
eq-list-concat-empty : {A : Set} → (xs : List {A}) → (xs ++ []) ≡ xs
eq-list-concat-empty [] = refl
eq-list-concat-empty (x ∷ xs) = cong (λ y → x ∷ y) (eq-list-concat-empty xs)

-- v ∉ (x ∷ [])   ⇒   v ≢ x
-- If v is not in a list with the single element x, then v ≢ x.
neq-the-first : {v x : ℕ}    → v ∉ (x ∷ [])    → v ≢ x
neq-the-first {v} {x} p1 with v ≡? x
... | left  p rewrite p = absurd (p1 (in-head x []))
... | right p           = p

-- (x ∷ xs)[i] ≡ x[i - 1]    when i > 0
eq-idx-not-first : {A : Set}
  → (x : A)
  → (xs : List {A})
  → (i : ℕ)
  → i > zero
  → getIdx (x ∷ xs) i ≡ getIdx xs (pred i)
eq-idx-not-first x xs zero p1    = absurd (p1 (base≤ zero))
eq-idx-not-first x xs (succ i) p1  = refl

-- (xs ++ ys)[i] ≡ xs[i]   when i < len(xs)      (for any ys)
eq-idx-in-first : {A : Set}
    → (xs : List {A})
    → (ys : List {A})
    → (i : ℕ)
    → i < len xs
    → getIdx (xs ++ ys) i ≡ getIdx xs i
eq-idx-in-first (x ∷ xs) ys zero     p1  = refl
eq-idx-in-first (x ∷ xs) ys (succ i) p1  = eq-idx-in-first xs ys i (x+1<y+1-to-x<y i (len xs) p1)

-- xs[i] ≡ (xs ++ ys)[i]   when i < len(xs)      (for any ys)
eq-idx-in-first-in-concat : {A : Set}
    → (xs : List {A})
    → (ys : List {A})
    → (i : ℕ)
    → i < len xs
    → getIdx xs i ≡ getIdx (xs ++ ys) i
eq-idx-in-first-in-concat (x ∷ xs) ys zero     p1  = refl
eq-idx-in-first-in-concat (x ∷ xs) ys (succ i) p1  = eq-idx-in-first-in-concat xs ys i (x+1<y+1-to-x<y i (len xs) p1)

-- (xs ++ ys)[i] ≡ ys[i - len xs]    when i ≥ len xs
eq-idx-in-second : {A : Set}
  → (xs : List {A})
  → (ys : List {A})
  → (i : ℕ)
  → i ≥ len xs
  → getIdx (xs ++ ys) i ≡ getIdx (ys) (i - (len xs))
eq-idx-in-second []       ys i p1     = refl
eq-idx-in-second (x ∷ xs) ys i p1     = begin
  getIdx (x ∷ (xs ++ ys)) i         ≡⟨ eq-idx-not-first x (xs ++ ys) i (x≥y+1-to-x≥0 i (len xs) p1) ⟩
  getIdx (xs ++ ys) (pred i)        ≡⟨ eq-idx-in-second xs ys (pred i) (x≥y+1-to-x-1≥y i (len xs) p1) ⟩
  getIdx (ys) ((pred i) - (len xs)) ∎

-- (xs ++ (x ∷ ys))[i] ≡ (xs ++ ys)[i - 1]    when i > len xs
eq-idx-second-rem-from-center : {A : Set}
    → (xs : List {A})
    → (x : A)
    → (ys : List {A})
    → (i : ℕ)
    → i > len(xs)
    → getIdx (xs ++ (x ∷ ys)) i ≡ getIdx (xs ++ ys) (pred i)
eq-idx-second-rem-from-center xs x ys i p = {!!}
-- getIdx (xs ++ (x ∷ ys)) i
-- ≡ getIdx (x ∷ ys) (i - len xs)   by eq-idx-in-second
-- ≡ getIdx ys (pred (i - len xs))  by eq-not-first
-- ≡ getIdx ys (pred i - len xs)    by eq-minus-succ
-- ≡ ?

-- xs[i] ≡ none      when i ≥ len xs
eq-idx-too-big : {A : Set}
  → (xs : List {A})
  → (i : ℕ)
  → i ≥ len xs
  → getIdx xs i ≡ none
eq-idx-too-big []       zero     p1   = refl
eq-idx-too-big (x ∷ xs) zero     p1   = absurd (p1 (0<x+1 (len xs)))
eq-idx-too-big []       (succ i) p1   = refl
eq-idx-too-big (x ∷ xs) (succ i) p1   = eq-idx-too-big xs i (x+1≥y+1-to-x≥y i (len xs) p1)

-- (xs ++ ys)[i] ≡ (xs ++ (y ∷ ys))[i+1]      when x ≥ len xs
eq-idx-add-one-mid : {A : Set}
  → (xs : List {A})
  → (ys : List {A})
  → (y : A)
  → (i : ℕ)
  → i ≥ len xs
  → getIdx (xs ++ ys) i ≡ getIdx (xs ++ (y ∷ ys)) (succ i)
eq-idx-add-one-mid xs ys y i p1 = begin
  getIdx (xs ++ ys) i                  ≡⟨ eq-idx-in-second xs ys i p1  ⟩
  getIdx ys (i - len(xs))              ≡⟨⟩
  getIdx (y ∷ ys) (succ (i - len(xs))) ≡⟨ cong (λ k → getIdx (y ∷ ys) k) (eq-minus-succ i (len xs) p1) ⟩
  getIdx (y ∷ ys) ((succ i) - len(xs)) ≡⟨ symm (eq-idx-in-second xs (y ∷ ys) (succ i) (x≥y-to-x+1≥y i (len xs) p1) ) ⟩
  getIdx (xs ++ (y ∷ ys)) (succ i) ∎
-- getIdx (xs ++ ys) i
-- ≡ getIdx ys (i - len(xs))                 by eq-idx-in-second
-- ≡ getIdx (y ∷ ys) (succ (i - len(xs)))    by definition of getIdx
-- ≡ getIdx (y ∷ ys) ((succ i) - len(xs))    by eq-minus-succ
-- ≡ getIdx (xs ++ (y ∷ ys)) (succ i)        by symm eq-idx-in-second

-- xs[i] ≡ (x ∷ xs)[i+1]
eq-idx-add-one : {A : Set}
  → (x : A)
  → (xs : List {A})
  → (i : ℕ)
  → getIdx (xs) i ≡ getIdx (x ∷ xs) (succ i)
eq-idx-add-one x xs i = refl





