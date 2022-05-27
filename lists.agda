open import basics

infixr 11 _∷_

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

-- Get the max value of a list
getMax : List {ℕ} → ℕ
getMax [] = zero
getMax (x ∷ xs) with x ≤? (getMax xs)
... | left p    = getMax xs
... | right p  = x

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

get-index : {A : Set} → List {A} → ℕ → Opt {A}
get-index [] n = none
get-index (x ∷ xs) zero = some x
get-index (x ∷ xs) (succ n) = get-index xs n

get-index-not-0 : {A : Set} {x y : A} {xs : List {A}} (n : ℕ) → get-index (x ∷ xs) n ≡ some y → n ≢ zero → get-index xs (pred n) ≡ some y
get-index-not-0 zero p1 p2 = absurd (p2 refl)
get-index-not-0 (succ n) p1 p2 = p1

list-elem-+1 : {A : Set} {xs : List {A}} {x : ℕ} {v y : A} → get-index xs x ≡ some v → get-index (y ∷ xs) (succ x) ≡ some v
list-elem-+1 {A} {x ∷ xs} p = p

len : {A : Set} → List {A} → ℕ
len [] = zero
len (x ∷ xs) = succ (len xs)


-- If an element is at index <i> of xs ++ ys and <i> < len(xs), then the same element is at index <i> of xs
get-index-in-first : {A : Set} {xs ys : List {A}} {x : ℕ} {v : A} → x < len xs → get-index (xs ++ ys) x ≡ some v  → get-index xs x ≡ some v
get-index-in-first {A} {x ∷ xs} {ys} {zero} p1 p2  = p2
get-index-in-first {A} {x ∷ xs} {ys} {succ n} p1 p2 = get-index-in-first (lemma-pred-< n (len xs) p1) p2

-- If an element is at index <i> of list xs, then it is at index <i> of list xs ++ ys for any ys
pos-first-pos-concat : {A : Set} {xs ys : List {A}} {n : ℕ} {v : A} → get-index xs n ≡ some v  → get-index (xs ++ ys) n ≡ some v
pos-first-pos-concat {A} {x ∷ xs} {ys} {zero} p1 = p1
pos-first-pos-concat {A} {x ∷ xs} {ys} {succ n} p1 = pos-first-pos-concat {A} {xs} {ys} p1

