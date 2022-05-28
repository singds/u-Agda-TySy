infixl 9  _≡_
infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin_


-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

-- Empty type
data ⊥ : Set where

-- Optional type
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

-- Equality
data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}
-- To use the <rewrite> keyword

_≢_ : {A : Set} → A → A → Set
x ≢ y = ((x ≡ y) → ⊥)

-- Disjoint union
data _⊎_ (A B : Set) : Set where
  left   : A → A ⊎ B
  right : B → A ⊎ B

-- Existential quantifier
-- B is a set that is dependent on A
data ∃ (A : Set) (B : A → Set) : Set where
  exists : (a : A) (b : B a) → ∃ A B

-- A holds and B holds
-- There must be a proof of A and a proof of B
data _&_ (A : Set) (B : Set) : Set where
  _and_ : (a : A) (b : B) → A & B



-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

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



-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

-- Congruence
cong : {A B : Set} {x y : A} → (f : A → B) → (x ≡ y) → (f x ≡ f y)
cong f refl = refl

-- Symmetry
symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

-- Transitivity
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

_≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
x ≡⟨⟩ q = q

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p


symm≢ : {A : Set} {x y : A} → x ≢ y → y ≢ x
symm≢ p = λ p1 → p (symm p1)



-- -----------------------------------------------------------------------------
-- -----------------------------------------------------------------------------

-- some x ≡ some y   ⇒   x ≡ y
eq-opt-some-to-val : {A : Set} {x y : A} → some x ≡ some y → x ≡ y
eq-opt-some-to-val refl = refl

-- x ≡ y   ⇒   some x ≡ some y
eq-opt-val-to-some : {A : Set} {x y : A} → x ≡ y → some x ≡ some y
eq-opt-val-to-some refl = refl

