open import type-system

ev-ex-1 : ((fun Bool (var zero)) app (fun Bool (var zero))) ⇒ (fun Bool (var zero))
ev-ex-1 = e-beta Bool (var zero) (fun Bool (var zero))
            (v-fun Bool (var zero))
