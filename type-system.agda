
data ⊥ : Set where


-- From a value of type ⊥ (bottom) I can derive whatever I want.
-- Actually there are no values of type ⊥.
absurd : {A : Set} → ⊥ → A
absurd ()

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

_≢_ : {A : Set} → A → A → Set
x ≢ y = ((x ≡ y) → ⊥)


data _⊎_ (A B : Set) : Set where
  left : A → A ⊎ B
  right : B → A ⊎ B

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

-- existential quantifier
-- B is a set that is dependent on A
data ∃ (A : Set) (B : A → Set) : Set where
  exists : (a : A) (b : B a) → ∃ A B


-- A holds and B holds
-- there must be a proof of A and a proof of B
data _&_ (A : Set) (B : Set) : Set where
  and : (a : A) (b : B) → A & B

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Congruence
cong : {A B : Set} {x y : A} → (f : A → B) → (x ≡ y) → (f x ≡ f y)
cong f refl = refl

-- If the successors of two numbers are equals, then the two numbers are equal
-- This can't be generalized right ???
succ-eq-pred-eq : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-eq-pred-eq refl = refl

-- Comparator for natual numbers
-- Given two numbers it provides either a proof that those number are equals or
-- a proof that those numbers are not equal.
comp-ℕ : (x : ℕ) → (y : ℕ) → ((x ≡ y) ⊎ (x ≢ y))
comp-ℕ zero zero = left refl
comp-ℕ zero (succ y) = right (λ ())
comp-ℕ (succ x) zero = right (λ ())
comp-ℕ (succ x) (succ y) with comp-ℕ x y
... | left p  = left (cong succ p)
... | right p = right λ pSuccEq → p (succ-eq-pred-eq pSuccEq)

-- The comparison of an element with itself always results in a proof of equality.
-- Comparing x with x, you can't get a proof that x ≢ x
comp-ℕ-xx : (x : ℕ) → (comp-ℕ x x ≡ left refl)
comp-ℕ-xx zero = refl
comp-ℕ-xx (succ x) with comp-ℕ x x
comp-ℕ-xx (succ x) | left refl = refl
... | right p = absurd (p refl)

_+_ : ℕ → ℕ → ℕ
zero + b   = b
succ a + b = succ (a + b)

-- Language types
data Type : Set where
  Bool   : Type
  Nat    : Type
  Tarrow : Type → Type → Type

-- Language terms
data Term : Set where
  true  : Term
  false : Term
  num   : ℕ → Term                    -- number
  var   : ℕ → Term                    -- variable
  plus  : Term → Term → Term          -- sum between natural numbers
  if    : Term → Term → Term → Term   -- if e1 then e1 else e3
  app   : Term → Term → Term          -- function application
  fun   : ℕ → Type → Term → Term      -- labda abstraction


data List {A : Set} : Set where
  []  : List {A}
  _∷_ : (x : A) → (xs : List {A}) → List {A} 


-- List concatenation
_++_ : {A : Set} → List {A} → List {A} → List {A}
[] ++ l2       = l2
(x ∷ l1) ++ l2 = x ∷ (l1 ++ l2)


-- Remove the given element from a list of integers
rem-ℕ : List → (x : ℕ) → List
rem-ℕ [] x = []
rem-ℕ (x ∷ l) y with comp-ℕ x y
... | left p = rem-ℕ l y             -- x equals y
... | right p = x ∷ (rem-ℕ l y)      -- x not equals y


-- Proposition: the element x is in the list
data in-list {A : Set} : (x : A) → List → Set where
  in-head : (x : A) (l : List) → in-list x (x ∷ l)
  in-tail : (x y : A) (l : List) (p : in-list x l) → in-list x (y ∷ l) 


-- Get the free vriables of a term
fv : Term → List {ℕ}
fv true          = []
fv false         = []
fv (num x)       = []
fv (var x)       = x ∷ []
fv (plus m1 m2)  = (fv m1) ++ (fv m2)
fv (if e1 e2 e3) = ((fv e1) ++ (fv e2)) ++ (fv e3)
fv (app e1 e2)   = (fv e1) ++ (fv e2)
fv (fun x t e)   = rem-ℕ (fv e) x 


-- The type environment
-- TODO with this definition we can add a variable that is already in the environment,
-- we should prevent this.
data Env : Set where
  []       : Env
  env-add  : ℕ → Type  → Env → Env


-- Proposition: the provided environment contains the binding from the provided variable to the provided type.
-- m-first = match the first
-- m-tail  = match the tail
data EnvContains : ℕ → Type → Env → Set where
  m-first : (x : ℕ) (t : Type) (Γ : Env) → EnvContains x t (env-add x t Γ)
  m-tail  : {Γ : Env} {x : ℕ} {t : Type} (y  : ℕ) (ty : Type) → EnvContains x t (Γ) → EnvContains x t (env-add y ty Γ)

-- Typing rules
-- HasType is the set that contains the proofs that the term M has the type T in the environment E
--             E      M       T        E = environment   M = term   T = type
data HasType : Env → Term → Type → Set where
  t-true  : {Γ : Env} → HasType Γ true Bool
  t-false : {Γ : Env} → HasType Γ false Bool
  t-num   : {Γ : Env} (n : ℕ) → HasType Γ (num n) Nat
  t-sum   : {Γ : Env} {n1 n2 : Term}
            (p1 : HasType Γ n1 Nat) (p2 : HasType Γ n2 Nat) → HasType Γ (plus n1 n2) Nat
  t-if    : {Γ : Env} {e1 e2 e3 : Term} {t : Type}
            (p1 : HasType Γ e1 Bool) (p2 : HasType Γ e2 t) (p3 : HasType Γ e3 t) → HasType Γ (if e1 e2 e3) t
  t-app   : {Γ : Env} {e1 e2 : Term} {t1 t2 : Type}
            (p1 : HasType Γ e1 (Tarrow t1 t2)) (p2 : HasType Γ e2 t1) → HasType Γ (app e1 e2) t2
  t-fun   : {Γ : Env} {x : ℕ} {t1 t2 : Type} {e1 : Term}
            (p : HasType (env-add x t1 Γ) e1 t2) → HasType Γ (fun x t1 e1) (Tarrow t1 t2)
  t-var   : {Γ : Env} {x : ℕ} {t : Type}
            (inEvn : EnvContains x t Γ) → HasType Γ (var x) t


data Value : Term → Set where
  v-true  : Value true
  v-false : Value false
  v-num   : (n : ℕ) → Value (num n)
  v-fun   : (x : ℕ) (t : Type) (e : Term) →  Value (fun x t e)

NotValue : Term → Set
NotValue m = ((Value m) → ⊥)

-- Given a term returns a proof that this term is a value or a proof that this
-- term is not a value
is-value : (m : Term) → Value m ⊎ NotValue m
is-value true          = left v-true
is-value false         = left v-false
is-value (num x)       = left (v-num x)
is-value (var x)       = right (λ ())
is-value (plus m m₁)   = right (λ ())
is-value (if m m₁ m₂)  = right (λ ())
is-value (app m m₁)    = right (λ ())
is-value (fun x t m)   = left (v-fun x t m)

-- Substitution
-- occurences of the variable x are substituted with the term m in term t, producing a new term  
subst : ℕ → Term → Term → Term
subst x m true           = true
subst x m false          = false
subst x m (num n)        = num n
subst x m (var y) with comp-ℕ x y
... | left p = m         -- case x equals y
... | right p = var y    -- case x not equals y
subst x m (plus e1 e2)   = plus (subst x m e1) (subst x m e2)
subst x m (if e1 e2 e3)  = if (subst x m e1) (subst x m e2) (subst x m e3)
subst x m (app e1 e2)    = app (subst x m e1) (subst x m e2)
subst x m (fun y t e)    = fun y t (subst x m e) -- ???
-- y should not appear in fv(e) ???
-- the substitution in this case should not be defined.
-- we define it anyway, we force this to not happen in the typing rules
-- here we have to deal with alpha equivalence
-- we should introduce alpha conversion when y appears in fv (m)

-- Evaluation in a single step
data EvalTo : Term → Term → Set where
  e-sum-l    : (m1 m1' m2 : Term) (pl : EvalTo m1 m1') → EvalTo (plus m1 m2) (plus m1' m2)
  e-sum-r    : (n1 : ℕ) (m2 m2' : Term) (pr : EvalTo m2 m2') → EvalTo (plus (num n1) m2) (plus (num n1) m2')
  e-sum      : (n1 n2 : ℕ) → EvalTo (plus (num n1) (num n2)) (num (n1 + n2))
  e-if-guard : (m1 m1' m2 m3 : Term) (p1 : EvalTo m1 m1') → EvalTo (if m1 m2 m3) (if m1' m2 m3)
  e-if-true  : (m2 m3 : Term) → EvalTo (if true m2 m3) m2
  e-if-false : (m2 m3 : Term) → EvalTo (if false m2 m3) m3
  -- beta reduction
  -- how can i say that an element is not in a list ?
  e-beta     : (x : ℕ) (t : Type) (e1 v2 : Term) (pv : Value v2) → EvalTo (app (fun x t e1) v2) (subst x v2 e1)
  e-app1     : (m1 m1' m2 : Term) (p1 : EvalTo m1 m1') → EvalTo (app m1 m2) (app m1' m2)
  e-app2     : (v1 m2 m2' : Term) (p1 : Value v1) (p1 : EvalTo m2 m2') → EvalTo (app v1 m2) (app v1 m2')

-- Evaluation in multiple steps
-- reflexive and transitive closure
data EvalTo* : Term → Term → Set where
  e-refl : (e1 : Term) → EvalTo* e1 e1                                          -- reflexivity
  e-trans : (e1 e2 e3 : Term) → EvalTo* e1 e2 → EvalTo* e2 e3 → EvalTo* e1 e3   -- transitivity



-- INVERTION LEMMAS
-- invertion lemma for bool terms 
lemma-inversion-true : {Γ : Env} {t : Type} → HasType Γ true t → t ≡ Bool
lemma-inversion-true t-true = refl

lemma-inversion-false : {Γ : Env} {t : Type} → HasType Γ false t → t ≡ Bool
lemma-inversion-false t-false = refl

-- invertion lemma for sum term 
lemma-inversion-nat : {Γ : Env} {m1 m2 : Term} {t : Type} → HasType Γ (plus m1 m2) t → t ≡ Nat
lemma-inversion-nat (t-sum p1 p2) = refl

lemma-inversion-nat-m1 : {Γ : Env} {m1 m2 : Term} {t : Type} → HasType Γ (plus m1 m2) t → HasType Γ m1 Nat
lemma-inversion-nat-m1 (t-sum p1 p2) = p1

lemma-inversion-nat-m2 : {Γ : Env} {m1 m2 : Term} {t : Type} → HasType Γ (plus m1 m2) t → HasType Γ m2 Nat
lemma-inversion-nat-m2 (t-sum p1 p2) = p2

-- invertion lemma for if then else term
lemma-inversion-if-e1 : {Γ : Env} {e1 e2 e3 : Term} {t : Type} → HasType Γ (if e1 e2 e3) t → HasType Γ e1 Bool
lemma-inversion-if-e1 (t-if p1 p2 p3) = p1

lemma-inversion-if-e2 : {Γ : Env} {e1 e2 e3 : Term} {t : Type} → HasType Γ (if e1 e2 e3) t → HasType Γ e2 t
lemma-inversion-if-e2 (t-if p1 p2 p3) = p2

lemma-inversion-if-e3 : {Γ : Env} {e1 e2 e3 : Term} {t : Type} → HasType Γ (if e1 e2 e3) t → HasType Γ e3 t
lemma-inversion-if-e3 (t-if p1 p2 p3) = p3

-- invertion lemma for variable term
lemma-invertion-var : {Γ : Env} {x : ℕ} {t : Type} → HasType Γ (var x) t → EnvContains x t Γ
lemma-invertion-var (t-var p) = p     -- p is the proof that "Γ" contains "x"

lemma-invertion-app : {Γ : Env} {m1 m2 : Term} {t : Type} → HasType Γ (app m1 m2) t → ∃ Type (λ t1 → (HasType Γ m1 (Tarrow t1 t)) & (HasType Γ m2 t1))
lemma-invertion-app (t-app {Γ} {m1} {m2} {t1} {t2} p1 p2) = exists t1 (and p1 p2)

lemma-invertion-fun : {Γ : Env} {m : Term} {x : ℕ} {t1 t : Type} → HasType Γ (fun x t1 m) t → ∃ Type (λ t2 → (t ≡ (Tarrow t1 t2)) & HasType (env-add x t1 Γ) m t2)
lemma-invertion-fun (t-fun {Γ} {x} {t1} {t2} {m} p) = exists t2 (and refl p)



-- CANONICAL FORMS LEMMAS
-- if v is a value of type Bool then v is ewither true or false
lemma-canon-bool : {Γ : Env} {m : Term} → Value m → (HasType Γ m Bool) →
          (m ≡ true) ⊎ (m ≡ false)
lemma-canon-bool pv (t-true) = left refl
lemma-canon-bool pv (t-false) = right refl

lemma-canon-nat : {Γ : Env} {m : Term} → Value m → (HasType Γ m Nat) →
          ∃ ℕ (λ n → m ≡ num n)
lemma-canon-nat pv (t-num n) = exists n refl

lemma-canon-arrow : {Γ : Env} {t1 t2 : Type} {m : Term} → Value m → (HasType Γ m (Tarrow t1 t2)) →
          ∃ ℕ (λ x → (∃ Term (λ m1 → m ≡ (fun x t1 m1))))
lemma-canon-arrow pv (t-fun {Γ} {x} {t1} {t2} {e1} pt) = exists x (exists e1 refl)



-- PROGRESS THEOREM
progress : {m : Term} {t : Type} → HasType [] m t → (Value m) ⊎ (∃ Term (λ m' → EvalTo m m'))

progress t-true = left v-true

progress t-false = left v-false

progress (t-num n) = left (v-num n)

progress (t-fun {[]} {x} {t1} {t2} {e1} p) = left (v-fun x t1 e1)

progress (t-sum {Γ} {n1} {n2} n1HasTypeNat n2HasTypeNat) with is-value n1 | is-value n2
... | right n1NotValue | _ = right evTo -- n1 is not a value
    where
    n1ValueOrEval = progress n1HasTypeNat
    ∃n1' = ⊎-getB n1ValueOrEval n1NotValue
    
    get-evTo : (∃ Term (λ n1' → EvalTo n1 n1')) → ∃ Term (λ m → EvalTo (plus n1 n2) m)
    get-evTo (exists n1' n1→n1') = exists (plus n1' n2) (e-sum-l n1 n1' n2 n1→n1')

    evTo = get-evTo ∃n1'

... | left n1Value | right n2NotValue = right evTo
    where
    ∃x1 = lemma-canon-nat n1Value n1HasTypeNat

    n2ValueOrEval = progress n2HasTypeNat
    ∃n2' = ⊎-getB n2ValueOrEval n2NotValue
    
    get-evTo : (∃ ℕ (λ x1 → n1 ≡ num x1)) → (∃ Term (λ n2' → EvalTo n2 n2')) → ∃ Term (λ m → EvalTo (plus n1 n2) m)
    get-evTo (exists x1 p1) (exists n2' p2) rewrite p1 = exists (plus (num x1) n2') (e-sum-r x1 n2 n2' p2)
    
    evTo = get-evTo ∃x1 ∃n2'

... | left n1Value | left n2Value = right evTo
    where

    -- I prooved that n1 ≡ num x1
    -- I prooved that n2 ≡ num x2
    -- Agda wonts a proof that ∃ m' such that (plus n1 n2) evaluates to m'
    -- I can easily produce a proof that ∃ m' such that (plus (num x1) (num x2)) m'
    -- So I rewrite the goal using the equality I have
    -- With rewriting Agda understands that every type dependent on n1 is
    -- definitinally equivalent to the same type where n1 is replaced with (num x1)
    n1≡num = lemma-canon-nat n1Value n1HasTypeNat
    n2≡num = lemma-canon-nat n2Value n2HasTypeNat

    get-evTo : (∃ ℕ (λ x → (n1 ≡ (num x)))) → (∃ ℕ (λ x → (n2 ≡ (num x)))) → ∃ Term (λ m → EvalTo (plus n1 n2) m)
    get-evTo (exists x1 p1) (exists x2 p2) rewrite p1 | p2 = exists (num (x1 + x2)) (e-sum x1 x2)

    evTo = get-evTo n1≡num n2≡num


progress (t-if {[]} {e1} {e2} {e3} e1HasTypeBool p2 p3) with is-value e1
... | left e1Value = right evTo
    where
    e1TrueOrFalse = lemma-canon-bool e1Value e1HasTypeBool
    
    get-evTo : (g : Term) → (g ≡ true) ⊎ (g ≡ false) → ∃ Term (λ m → EvalTo (if g e2 e3) m)
    get-evTo g (left gEqTrue) rewrite gEqTrue = exists e2 (e-if-true e2 e3)
    get-evTo g (right gEqFalse) rewrite gEqFalse = exists e3 (e-if-false e2 e3)

    evTo = get-evTo e1 e1TrueOrFalse

... | right e1NotValue = right evTo
    where
    e1ValueOrEval = progress e1HasTypeBool
    ∃e1' = ⊎-getB e1ValueOrEval e1NotValue
    
    get-evTo : ∃ Term (λ e1' → EvalTo e1 e1') → ∃ Term (λ m → EvalTo (if e1 e2 e3) m)
    get-evTo (exists e1' p1) = exists (if e1' e2 e3) (e-if-guard e1 e1' e2 e3 p1)

    evTo = get-evTo ∃e1'

progress (t-app {[]} {e1} {e2} {t1} {_} e1HasTypeT1T2 e2HasTypeT1) with is-value e1 | is-value e2
... | right e1NotValue | _ = right evTo
    where
    e1ValueOrEval = progress e1HasTypeT1T2
    ∃e1' = ⊎-getB e1ValueOrEval e1NotValue

    get-evTo : ∃ Term (λ e1' → EvalTo e1 e1') → ∃ Term (λ m → EvalTo (app e1 e2) m)
    get-evTo (exists e1' p) = exists (app e1' e2) (e-app1 e1 e1' e2 p)

    evTo = get-evTo ∃e1'
    
... | left e1Value | right e2NotValue = right evTo
    where
    e2ValueOrEval = progress e2HasTypeT1
    ∃e2' = ⊎-getB e2ValueOrEval e2NotValue

    get-evTo : ∃ Term (λ e2' → EvalTo e2 e2') → ∃ Term (λ m → EvalTo (app e1 e2) m)
    get-evTo (exists e2' e2→e2') = exists (app e1 e2') (e-app2 e1 e2 e2' e1Value e2→e2')

    evTo = get-evTo ∃e2'

... | left e1Value | left e2Value = right evTo
    where

    ∃e1≡Fun = lemma-canon-arrow e1Value e1HasTypeT1T2

    get-evTo : ∃ ℕ (λ x → (∃ Term (λ m1 → e1 ≡ (fun x t1 m1)))) → ∃ Term (λ m → EvalTo (app e1 e2) m)
    get-evTo (exists x (exists m1 e1≡Fun)) rewrite e1≡Fun = exists (subst x e2 m1) (e-beta x t1 m1 e2 e2Value)

    evTo = get-evTo ∃e1≡Fun


-- refl is a proof tha x is equal to x
-- input :
--     a proof that an extended environment contains x
--     a proof that x is not the first element of the environment
-- output:
--     a proof that x is in the environment that is the original one without the first element
in-env-decompose : {Γ : Env} {x y : ℕ} {t1 t2 : Type} → EnvContains x t1 (env-add y t2 Γ) → x ≢ y → EnvContains x t1 Γ
in-env-decompose (m-first x t Γ) x≢x = absurd (x≢x refl)
in-env-decompose (m-tail y ty inΓ) x≢y = inΓ

substitution-lemma : {Γ : Env} {x : ℕ} {t1 t2 : Type} {m1 m2 : Term} → HasType (env-add x t2 Γ) m1 t1 → HasType Γ m2 t2 → HasType Γ (subst x m2 m1) t1
substitution-lemma t-true m2T2 = t-true
substitution-lemma t-false m2T2 = t-false
substitution-lemma (t-num n) m2T2 = t-num n
substitution-lemma (t-sum e1Nat e2Nat) m2T2 = t-sum (substitution-lemma e1Nat m2T2)
                                                (substitution-lemma e2Nat m2T2)
substitution-lemma (t-if e1Bool e2T e3T) m2T2 = t-if (substitution-lemma e1Bool m2T2)
                                                  (substitution-lemma e2T m2T2)
                                                  (substitution-lemma e3T m2T2)
substitution-lemma (t-app e1T1T2 e2T1) m2T2 = t-app (substitution-lemma e1T1T2 m2T2)
                                                (substitution-lemma e2T1 m2T2)
substitution-lemma (t-fun p) m2T2 = {!!}
substitution-lemma (t-var (m-first x t2 Γ)) m2T2 rewrite comp-ℕ-xx x = m2T2
substitution-lemma (t-var (m-tail y ty inEnv)) m2T2 = {!!}



preservation : {Γ : Env} {m m' : Term} {t : Type} → HasType Γ m t → EvalTo m m' → HasType Γ m' t
preservation (t-sum m1Nat m2Nat) (e-sum-l m1 m1' m2 pe)          = t-sum (preservation m1Nat pe) m2Nat
preservation (t-sum m1Nat m2Nat) (e-sum-r n1 m2 m2' pe)          = t-sum m1Nat (preservation m2Nat pe)
preservation (t-sum m1Nat m2Nat) (e-sum n1 n2)                   = t-num (n1 + n2)
preservation (t-if e1Bool e2T e3T) (e-if-guard m1 m1' m2 m3 pe)  = t-if (preservation e1Bool pe) e2T e3T
preservation (t-if e1Bool e2T e3T) (e-if-true m2 m3)             = e2T
preservation (t-if e1Bool e2T e3T) (e-if-false m2 m3)            = e3T
preservation (t-app e1T1T2 e2T1) (e-beta x t e1 e2 p1)            = {!!} where
  
preservation (t-app e1T1T2 e2T1) (e-app1 m1 m1' m2 pe)           = t-app (preservation e1T1T2 pe) e2T1
preservation (t-app e1T1T2 e2T1) (e-app2 v1 m2 m2' p1 pe)        = t-app e1T1T2 (preservation e2T1 pe)
