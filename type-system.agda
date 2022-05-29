open import basic
open import nat
open import list

-- Language types
data Type : Set where
  Bool     : Type
  Nat      : Type
  Tarrow   : Type → Type → Type
  

-- Language terms
data Term : Set where
  true    :                              Term
  false   :                              Term
  num     : (n : ℕ)                    → Term
  var     : (x : ℕ)                    → Term
  _app_   : (e1 : Term) → (e2 : Term)  → Term
  fun     : (t : Type) → (e1 : Term)   → Term

-- The environment is a list of types. No variable names are saved in the env.
Env = List {Type}

data HasType : Env → Term → Type → Set where
  t-true  : {Γ : Env}
            → HasType Γ true Bool

  t-false : {Γ : Env}
            → HasType Γ false Bool

  t-nat   : {Γ : Env} {n : ℕ}
            → HasType Γ (num n) Nat

  t-var   : {Γ : Env} {x : ℕ} {t : Type}
            → (getIdx Γ x) ≡ some t
            → HasType Γ (var x) t

  t-app   : {Γ : Env} {e1 e2 : Term} {t1 t2 : Type}
            → (p1 : HasType Γ e1 (Tarrow t1 t2))
            → (p2 : HasType Γ e2 t1)
            → HasType Γ (e1 app e2) t2
            
  t-fun   : {Γ : Env} {t1 t2 : Type} {e1 : Term}
            → (p : HasType (t1 ∷  Γ) e1 t2)
            → HasType Γ (fun t1 e1) (Tarrow t1 t2)

-- Definition of terms that are values.
data Value : Term → Set where
  v-true  :                          Value true
  v-false :                          Value false
  v-fun   : (t : Type) (e : Term) →  Value (fun t e)

-- Free variables of a term.
fv : Term → List {ℕ}
fv true        = []
fv false       = []
fv (num n)     = []
fv (var x)     = x ∷ []
fv (m1 app m2) = (fv m1) ++ (fv m2)
fv (fun t m)   = decAll ((fv m) remove zero)

lemma-invertion-var : {Γ : Env} {x : ℕ} {t : Type}
            → HasType Γ (var x) t
            → (getIdx Γ x) ≡ some t
lemma-invertion-var (t-var p) = p

lemma-invertion-app : {Γ : Env} {m1 m2 : Term} {t : Type}
            → HasType Γ (m1 app m2) t
            → ∃ Type (λ t1 → (HasType Γ m1 (Tarrow t1 t)) & (HasType Γ m2 t1))
lemma-invertion-app (t-app {Γ} {m1} {m2} {t1} {t2} p1 p2) = exists t1 (p1 and p2)

lemma-invertion-fun : {Γ : Env} {m : Term} {t1 t : Type}
            → HasType Γ (fun t1 m) t
            → ∃ Type (λ t2 → (t ≡ (Tarrow t1 t2)) & HasType (t1 ∷ Γ) m t2)
lemma-invertion-fun (t-fun {Γ} {t1} {t2} p) = exists t2 (refl and p)


shift : ℕ → ℕ → Term → Term
shift d c (var x) with x <? c
... | left  p         = var x
... | right p         = var (x + d)
shift d c (e1 app e2) = (shift d c e1) app  (shift d c e2)
shift d c (fun t e1)  = fun t (shift d (succ c) e1)
shift d c true        = true
shift d c false       = false
shift d c (num n)     = num n


shift-back : ℕ → ℕ → Term → Term
shift-back d c (var x) with x <? c
... | left  p              = var x
... | right p              = var (x - d)
shift-back d c (e1 app e2) = (shift-back d c e1) app  (shift-back d c e2)
shift-back d c (fun t e1)  = fun t (shift-back d (succ c) e1)
shift-back d c true        = true
shift-back d c false       = false
shift-back d c (num n)     = num n


-- Substitution [j:=s]m.
-- Substitute the variable j with the term s in m.
subst : ℕ → Term → Term → Term
subst j s (var x) with x ≡? j
... | left  p          = s
... | right p          = var x
subst j s (e1 app e2)  = (subst j s e1) app (subst j s e2)
subst j s (fun t e1)   = fun t (subst (succ j) (shift one zero s) e1)
subst j s true         = true
subst j s false        = false
subst j s (num n)      = num n

-- Evaluation judgement. 
data _⇒_ : Term → Term → Set where
  e-app1    : (m1 m1' m2 : Term)
              (p1 :  m1 ⇒ m1')
              → (m1 app m2) ⇒ (m1' app m2)

  e-app2    : (v1 m2 m2' : Term)
              (p1 : Value v1)
              (p1 : m2 ⇒ m2')
              → (v1 app m2) ⇒ (v1 app m2')

  e-beta    : (t : Type)
              (e1 v2 : Term)
              → Value v2
              → ((fun t e1) app v2) ⇒ shift-back one zero (subst zero (shift one zero v2) e1)


-- Γ,Γ₁ ⊢ m : tm
-- ⇒ Γ,tu,Γ₁ ⊢ ↑[1,len(Γ₁)] m : tm
weakening-2 : {Γ : Env} {Γ₁ : Env} {m : Term} {tm tu : Type}
        → HasType (Γ₁ ++ Γ) m tm
        → HasType (Γ₁ ++ (tu ∷ Γ)) (shift one (len Γ₁) m) tm
        
weakening-2 t-true  = t-true
weakening-2 t-false = t-false
weakening-2 t-nat   = t-nat
weakening-2 {Γ} {Γ₁} {var x} (t-var p) with x <? (len Γ₁)
weakening-2 {Γ} {Γ₁} {m} {tm} {tu} (t-var {_} {i} p1)
    | left  p2
        rewrite eq-idx-in-first Γ₁ Γ i p2
              | eq-idx-in-first-in-concat Γ₁ (tu ∷ Γ) i p2 = t-var p1
weakening-2 {Γ} {Γ₁} {var x} {tm} {tu} (t-var p) | right p2
  rewrite symm+ x (succ zero) | eq-idx-add-one-mid Γ₁ Γ tu x p2  = t-var p
weakening-2 (t-app p1 p2)            = t-app (weakening-2 p1) (weakening-2 p2) 
weakening-2 (t-fun p)                = t-fun (weakening-2 p)


-- Γ ⊢ m : t
-- ⇒ Γ,tu ⊢ ↑[1,0] m : t
weakening : {Γ : Env} {m : Term} {t tu : Type}
        → HasType Γ m t
        → HasType (tu ∷ Γ) (shift one zero m) t

weakening t-true  = t-true
weakening t-false = t-false
weakening t-nat   = t-nat
weakening {Γ} {var x} (t-var p) with x <? zero
... | right p2 rewrite symm+ x (succ zero) = t-var p
weakening (t-app p1 p2)                    = t-app (weakening p1) (weakening p2)
weakening {Γ} {fun tx m} (t-fun p)         = t-fun (weakening-2 {Γ} {tx ∷ []} {m} p)


-- Γ,S,Γ₁ ⊢ M : T
-- Γ,S,Γ₁ ⊢ N : S
-- ⇒ Γ,S ⊢ M{len(Γ₁):=S} : T
substitution : {Γ Γ₁ : Env} {S T : Type} {M N : Term}
        → HasType (Γ₁ ++ (S ∷ Γ)) M T
        → HasType (Γ₁ ++ (S ∷ Γ)) N S
        → HasType (Γ₁ ++ (S ∷ Γ)) (subst (len Γ₁) N M) T

substitution t-true  p2 = t-true
substitution t-false p2 = t-false
substitution t-nat   p2 = t-nat
substitution {Γ} {Γ₁} {S} (t-var {_} {x} p1) p2 with x ≡? (len Γ₁)
... | left  p
      rewrite eq-idx-in-second Γ₁ (S ∷ Γ) x (x≡y-to-x≥y x (len Γ₁) p)
            | x≡y-to-x-y≡0 x (len Γ₁) p
            | eq-opt-some-to-val p1 = p2
... | right p                  = t-var p1
substitution (t-app p1 p2) p3  = t-app (substitution p1 p3) (substitution p2 p3)
substitution (t-fun p1) p2     = t-fun (substitution p1 (weakening p2))



-- Γ,S,Γ₁ ⊢ M : T
-- len(Γ₁) ∉ fv(M)
-- ⇒ Γ,Γ₁ ⊢ ↑ -1 len(Γ₁) M : T
back-one : {t : Type} (Γ : Env) (tu : Type) (Γ₁ : Env) (m : Term)
        → HasType (Γ₁ ++ (tu ∷ Γ)) m t
        → ¬ (len (Γ₁) ∈ (fv m))
        → HasType (Γ₁ ++ Γ) (shift-back one (len Γ₁) m) t

back-one Γ tu Γ₁ true    t-true  p2 = t-true
back-one Γ tu Γ₁ false   t-false p2 = t-false
back-one Γ tu Γ₁ (num n) t-nat   p2 = t-nat
back-one Γ tu Γ₁ (var x) (t-var p1) p2 with x <? len(Γ₁)
... | left  p
      rewrite eq-idx-in-first Γ₁ (tu ∷ Γ) x p
            | eq-idx-in-first-in-concat Γ₁ Γ x p = t-var p1
-- TODO use eq-idx-second-rem-from-center instead of index-rem-from-center
... | right p = t-var (index-rem-from-center x p1 x->-len)
    where
    x-not-len : x ≢ len(Γ₁)
    x-not-len = symm≢  (neq-the-first p2)

    x->-len : x > len(Γ₁)
    x->-len = x≥y-and-x≢y-to-x>y p x-not-len

back-one Γ tu Γ₁ (m1 app m2) (t-app p1 p2) p3 = 
    t-app
        (back-one Γ tu Γ₁ m1 p1 (not-in-concat-not-in-first  (len Γ₁) (fv m1) (fv m2) p3))
        (back-one Γ tu Γ₁ m2 p2 (not-in-concat-not-in-second (len Γ₁) (fv m1) (fv m2) p3))
back-one Γ tu Γ₁ (fun tx m) (t-fun p1) p2 = t-fun (back-one Γ tu (tx ∷ Γ₁) m p1 (notin-dec-not-succ-in-list' p2))




type-preservation : {Γ : Env} {m m' : Term} {t : Type}
  → HasType Γ m t
  → m ⇒ m'
  → HasType Γ m' t
type-preservation (t-app p1 p3) (e-app1 m1 m1' m2 p2) = t-app (type-preservation p1 p2) p3
type-preservation (t-app p1 p3) (e-app2 v1 m2 m2' p2 p4) = t-app p1 (type-preservation p3 p4)
type-preservation {Γ} (t-app {_} {_} {_} {t1} {t2} (t-fun p1) p3) (e-beta t e1 v2 x) =
  back-one Γ t1 [] subst-term (substitution p1 (weakening p3)) zero-!in-fv-subst-term
  where
  subst-term : Term
  subst-term = subst zero (shift (succ zero) zero v2) e1

  zero-!in-fv-subst-term : ¬ (zero ∈ fv subst-term)
  zero-!in-fv-subst-term = {!!}


-- M{x:=N} is the substitution of the variable x with the term N
--
-- ROADMAP TO TYPE PRESERVATION
-- Γ ⊢ N : S                              ⇒ Γ,S ⊢ N : S                   weakening
-- Γ,S,Γ₁ ⊢ M : T     Γ,S,Γ₁ ⊢ N : S      ⇒ Γ,S ⊢ M{len(Γ₁):=S} : T       substitution
-- Γ,S,Γ₁ ⊢ M : T     len(Γ₁) ∉ fv(M)     ⇒ Γ,Γ₁ ⊢ ↑[-1,len(Γ₁)] M : T    back one
-- 0 ∉ fv  M{0 := ↑[1,0] S}
--
-- With weakening, substitution and back-one we can proove type preservation.



ev-ex-1 : ((fun Bool (var zero)) app (fun Bool (var zero))) ⇒ (fun Bool (var zero))
ev-ex-1 = e-beta Bool (var zero) (fun Bool (var zero))
            (v-fun Bool (var zero))

 
