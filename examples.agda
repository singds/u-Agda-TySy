open import basic
open import nat
open import list
open import type-system

-- examples of evaluation
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


-- examples of typing
ty-1 : HasType [] (fun Bool (var 0)) (Tarrow Bool Bool)
ty-1 = t-fun (t-var refl)

ty-2 : HasType (Bool ∷ Nat ∷ []) (fun Nat (var 2)) (Tarrow Nat Nat)
ty-2 = t-fun (t-var refl)
