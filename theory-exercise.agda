
infixl 20 _∷_

-- natural numbers
data Nat : Set where
  zero  : Nat
  succ  : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

-- eliminator for natural numbers
ElNat : {M : Nat → Set}
    → (t : Nat)
    → M zero
    → ((x : Nat) → M x → M (succ x))
    → M t
ElNat zero     c e = c
ElNat (succ t) c e = e t (ElNat t c e)

-- lists
data List (A : Set) : Set where
    []  : List A
    _∷_ : List A → A → List A

-- eliminator on lists
-- there is an error in the definition of the list eliminator in the notes
-- i have to define all operations in terms of this unique function
ElList : {A : Set} {M : (List A) → Set}
    → (xs : List A)                                     -- xs
    → M []                                              -- b
    → ((xs : List A) → (x : A) → (M xs) → (M (xs ∷ x))) -- e
    → M xs
ElList []       b e = b
ElList (xs ∷ x) b e = e xs x (ElList xs b e)

-- disjoint union
data _⨄_ : Set → Set → Set where
    inl : {A B : Set} → A → A ⨄ B
    inr : {A B : Set} → B → A ⨄ B

-- eliminator fro disjoint union
El+ : {A B : Set} {M : A ⨄ B → Set}
    → (t : A ⨄ B)
    → ((x : A) → M (inl {A} {B} x))
    → ((y : B) → M (inr {A} {B} y))
    → M t
El+ (inl x) ex ey = ex x
El+ (inr y) ex ey = ey y


-- Unit
data N₁ : Set where
    * : N₁


-- ex 2 on lists
append : {A : Set} → List A → List A → List A
append xs ys = ElList ys xs (λ l v r → r ∷ v)

test1 = append ([] ∷ 1 ∷ 2) ([] ∷ 3 ∷ 4)
test2 = append [] ([] ∷ 3 ∷ 4)
test3 = append ([] ∷ 1 ∷ 2) []
test4 = append {Nat} [] []

-- es 3 on natural numbers
-- define sum for natural numbers such that x + 0 ≡ x
_+₁_ : Nat → Nat → Nat
a +₁ b = ElNat b a (λ x r → succ r)

-- es 5
-- define multiplication for natural numbers
_·_ : Nat → Nat → Nat
a · b = ElNat b 0 (λ x r → a +₁ r)

-- es 6 (ok)
-- define the predecessor of a natural number such that
-- pred(0) = 0
-- pred(succ(n)) = n
pred : Nat → Nat
pred n = ElNat n 0 (λ x r → x)


-- es 2 on disjoint union
-- show that exists terms
-- dec : N₁ ⨄ Nat → Nat
-- cod : Nat → N₁ ⨄ Nat
-- such that for all n
-- dec(cod(0)) = 0
-- dec(cod(n)) = n
-- cod(dec(inl(*))) = inl(*)
-- cod(dec(inr(n))) = inr(n)
dec : N₁ ⨄ Nat → Nat
dec t = El+ t (λ x → 0) (λ x → x)

cod : Nat → N₁ ⨄ Nat
cod n = ElNat n (inl *) (λ x r → inr (succ x))
