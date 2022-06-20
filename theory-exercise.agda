
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
data _⊎_ : Set → Set → Set where
    inl : {A B : Set} → A → A ⊎ B
    inr : {A B : Set} → B → A ⊎ B

-- eliminator fro disjoint union
El+ : {A B : Set} {M : A ⊎ B → Set}
    → (t : A ⊎ B)
    → ((x : A) → M (inl {A} {B} x))
    → ((y : B) → M (inr {A} {B} y))
    → M t
El+ (inl x) ex ey = ex x
El+ (inr y) ex ey = ey y

-- Unit
data N₁ : Set where
    * : N₁

-- eliminator for singleton
El-N₁ : {M : N₁ → Set}
      → (t : N₁)
      → (c : M *)
      → M t
El-N₁ * c = c

-- propositional equality
data Id : (A : Set) → A → A → Set where
    id : {A : Set} → (a : A) → Id A a a

-- eliminator for propositional equality
-- When I know that two elements are equal, then If I apply the same function
-- to both the elements I get two elements that are equal.
El-id : {A : Set} {M : (z₁ : A) → (z₂ : A) → (z3 : Id A z₁ z₂) → Set }
    {a : A} {b : A}
    → (t : Id A a b)
    → ((x : A) → M x x (id x))
    → M a b t
El-id (id a) e = e a


-- -----------------------------------------------------------------------------
-- ex 2 list (ok)
append : {A : Set} → List A → List A → List A
append xs ys = ElList ys xs (λ l v r → r ∷ v)

test1 = append ([] ∷ 1 ∷ 2) ([] ∷ 3 ∷ 4)
test2 = append [] ([] ∷ 3 ∷ 4)
test3 = append ([] ∷ 1 ∷ 2) []
test4 = append {Nat} [] []


-- -----------------------------------------------------------------------------
-- ex 3 nat (ok)
--
-- define sum for natural numbers such that x + 0 ≡ x
_+₁_ : Nat → Nat → Nat
x +₁ r = ElNat r x (λ w₁ r₁ → succ r₁)


-- -----------------------------------------------------------------------------
-- ex 5 nat (ok)
--
-- define multiplication for natural numbers
_·_ : Nat → Nat → Nat
x · y = ElNat y 0 (λ w r → x +₁ r)


-- -----------------------------------------------------------------------------
-- ex 6 (ok)
--
-- define the predecessor of a natural number such that
-- pred(0) = 0
-- pred(succ(n)) = n
pred : Nat → Nat
pred n = ElNat n 0 (λ x r → x)


-- -----------------------------------------------------------------------------
-- ex 2 disjoint union (ok)
--
-- show that exists terms
-- dec : N₁ ⨄ Nat → Nat
-- cod : Nat → N₁ ⨄ Nat
-- such that for all n
-- dec(cod(0)) = 0
-- dec(cod(n)) = n
-- cod(dec(inl(*))) = inl(*)
-- cod(dec(inr(n))) = inr(n)
dec : N₁ ⊎ Nat → Nat
dec t = El+ t (λ x → 0) (λ x → x)

cod : Nat → N₁ ⊎ Nat
cod n = ElNat n (inl *) (λ x r → inr (succ x))


-- -----------------------------------------------------------------------------
-- es 3 propositional equality
--
h2 : {z₁ z₂ : Nat} → Id Nat z₁ z₂ → Id Nat (succ z₁) (succ z₂)
h2 p = El-id p (λ x → id (succ x))


-- -----------------------------------------------------------------------------
-- es 8 propositional equality
--
pf : (w : N₁) → Id N₁ * w
pf w = El-N₁ {λ x → Id N₁ * x} w (id *)


-- -----------------------------------------------------------------------------
-- es 9 propositional equality
--
pf₁ : (x w : N₁) → Id N₁ x w
pf₁ x w = El-N₁ {λ k → Id N₁ k w} x (pf w)


-- -----------------------------------------------------------------------------
-- ex 3 disjoint union ?
--
-- given B type [Γ] and C type [Γ] and b ∈ B [Γ] define a term
-- pr(z) ∈ B [x ∈ B ⨄ C] such that
-- pr(inl(x)) = x ∈ B [x ∈ B]
-- pr(inr(y)) = b ∈ B [y ∈ C]
pr : {B C : Set} → B ⊎ C → B → B
pr t b = El+ t (λ x → x) (λ x → b)
