open import basic
open import nat
open import list
open import type-system

-- -----------------------------------------------------------------------------
-- ------------------------------------------- EXAMPLES OF EVALUATION JUDGEMENTS

ev-1 : (fun Bool (var 0)) app true
  ⇒ true
ev-1 = e-beta Bool (var zero) true v-true

ev-2 : fun Bool (if (var 0) then (num 1) else (num 2)) app true
  ⇒ if true then (num 1) else (num 2)
ev-2 = e-beta Bool (if var zero then num 1 else num 2) true v-true

ev-3 : if true then (num 1) else (num 2)
  ⇒ num 1
ev-3 = e-if-true (num 1) (num 2)

ev-4 : fun Bool (if (var 0) then (num 1) else (num 2)) app true
  ⇒* num 1
ev-4 = e-trans
  (e-trans
    (e-refl (fun Bool (if (var 0) then (num 1) else (num 2)) app true))
    (e-beta Bool (if var zero then num 1 else num 2) true v-true))
  (e-if-true (num 1) (num 2))

ev-5 : ((fun Bool (var zero)) app (fun Bool (var zero)))
    ⇒ (fun Bool (var zero))
ev-5 = e-beta Bool (var zero)
        (fun Bool (var zero))
        (v-fun Bool (var zero))


-- -----------------------------------------------------------------------------
-- ------------------------------------------------ EXAMPLES OF WELL TYPED TERMS

-- Prove that
--     ∅ ⊢ λ x:Bool. x : Bool → Bool
-- is derivable.
ty-1 : HasType [] (fun Bool (var 0)) (Tarrow Bool Bool)
ty-1 = t-fun (t-var refl)

-- Prove that
--     x:Nat,y:Bool ⊢ λ z:Nat. x : Nat → Nat
-- is derivable.
ty-2 : HasType (Bool ∷ Nat ∷ []) (fun Nat (var 2)) (Tarrow Nat Nat)
ty-2 = t-fun (t-var refl)


-- -----------------------------------------------------------------------------
-- -------------------------------------------- EXAMPLES OF TERMS NOT WELL TYPED

-- -----------------------------------------------------------------------------
-- Prove that the term:
--     λ x:Bool → Nat. λ y:Bool. if y then x else (x + y)
--     λ Bool → Nat. λ Bool. if (var 0) then (num 1) else ((var x) +ₙ (var y))
-- is not well typed.
--
-- More precisely: prove that does not exists a type T such that the judgement
-- ∅ ⊢ M : T is derivable.
--
-- The proof term is obtained by only doing pattern matching on input proofs.
-- The proof term is unreadable, but it is there.
ty-⊥-1-term = fun (Tarrow Bool Nat) (fun Bool (if (var 0) then (num 1) else ((var 1) +ₙ (var 0))))
ty-⊥-1 : ∃ Type (λ t → HasType [] ty-⊥-1-term t)
       → ⊥
ty-⊥-1 (exists (Tarrow (Tarrow Bool Nat) .(Tarrow Bool Nat)) (t-fun (t-fun (t-if (t-var refl) t-nat (t-sum (t-var ()) p4)))))
--                                                                                                                ^
--                                                                                                                |
--                                                                   note here the presence of the absurd pattern |
-- see absurd pattern in official doc.
-- https://agda.readthedocs.io/en/v2.6.0.1/language/function-definitions.html#absurd-patterns


-- -----------------------------------------------------------------------------
-- Prove that the term:
--     λ x:Bool. x + 0
--     λ Bool. (var 0) + (num 0)
ty-⊥-2-term = fun Bool (var 0 +ₙ num 0)
ty-⊥-2 : ∃ Type (λ t → HasType [] ty-⊥-2-term t)
       → ⊥
ty-⊥-2 (exists (Tarrow Bool .Nat) (t-fun (t-sum (t-var ()) t-nat)))
--                                     absurd pattern  ^
