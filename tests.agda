open import basic
open import nat
open import list
open import type-system


-- -----------------------------------------------------------------------------
-- -------------------------------- THIS FILE CONTAINS USELESS STUFF, DON'T READ
--
-- This proof shows that:
-- if ∀ Γ we have that ∀ t the judgement HasType Γ m t is not derivable,
-- then does not exists a peir (Γ,t) such that the same judgement is derivable.
--
-- Think about this proof with  A = Env, B = Type, C = λ Γ t → HasType Γ m t
--
imply-prove : {A B : Set} {C : A → B → Set}
            → ((a : A) → (b : B) → C a b → ⊥)
            → (∃ (A & B) (λ { (x , y) → C x y }) → ⊥)
imply-prove p = λ { (exists (a , b) pc) → p a b pc }


-- the bottom type is clearly an empty domain
false-to-false : ⊥ → ⊥
false-to-false ()

-- -----------------------------------------------------------------------------
data foo1 : ℕ → Set where
  c1 : foo1 0

data foo2 : ℕ → Set where
  c2 : foo2 1

fun-foo : (n : ℕ) → foo1 n → foo2 n → HasType [] true Nat
fun-foo 0 c1 ()
