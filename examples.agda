open import basic
open import nat
open import list
open import type-system


-- -----------------------------------------------------------------------------
-- ------------------------------------------- EXAMPLES OF EVALUATION JUDGEMENTS

-- Prove that
--     (λ x:Bool. x) true ⇒* true
ev-1 : (fun Bool (var 0)) app true
  ⇒* true
ev-1 = begin⇒
  (fun Bool (var 0)) app true ⇒⟨ e-beta v-true ⟩
  true ⇒∎

-- Prove that
--     (λ x:Bool. if x then 1 else 2) true ⇒* 1
ev-2 : fun Bool (if var 0 then num 1 else num 2) app true
  ⇒* num 1
ev-2 = begin⇒
  fun Bool (if var 0 then num 1 else num 2) app true  ⇒⟨ e-beta v-true ⟩
  if true then num 1 else num 2                       ⇒⟨ e-if-true ⟩
  num 1 ⇒∎

-- Prove that
--     (λ x:Bool. if x then 1 else 2) false ⇒* 1
ev-3 : fun Bool (if var 0 then num 1 else num 2) app false
  ⇒* num 2
ev-3 = begin⇒
  fun Bool (if var 0 then num 1 else num 2) app false  ⇒⟨ e-beta v-false ⟩
  if false then num 1 else num 2                       ⇒⟨ e-if-false ⟩
  num 2 ⇒∎  

-- Prove that
--    (λ x:Bool. x) (λ x:Bool. x) ⇒* (λ x:Bool. x)
ev-4 : (fun Bool (var 0)) app (fun Bool (var 0))
    ⇒* fun Bool (var 0)
ev-4 =  begin⇒
  (fun Bool (var 0)) app (fun Bool (var 0))            ⇒⟨ e-beta v-fun ⟩
  fun Bool (var 0) ⇒∎


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
ty-⊥-1-term = fun (Tarrow Bool Nat) (fun Bool (if var 0 then num 1 else (var 1 +ₙ var 0)))
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
