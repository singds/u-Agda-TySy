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
