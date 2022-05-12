
data ⊥ : Set where

data _≡_ {A : Set} : A → A → Set where
  refl : (a : A) → a ≡ a

_≢_ : {A : Set} → A → A → Set
x ≢ y = ((x ≡ y) → ⊥)

data _⊎_ (A B : Set) : Set where
  left : A → A ⊎ B
  right : B → A ⊎ B

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
cong f (refl a) = refl (f a)

-- If the successors of two numbers are equals, then the two numbers are equal
-- This can't be generalized right ???
succ-eq-pred-eq : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-eq-pred-eq (refl (succ x)) = refl x

-- Comparator for natual numbers
-- Given two numbers it provides either a proof that those number are equals or
-- a proof that those numbers are not equal.
comp-ℕ : (x : ℕ) → (y : ℕ) → ((x ≡ y) ⊎ (x ≢ y))
comp-ℕ zero zero = left (refl zero)
comp-ℕ zero (succ y) = right (λ ())
comp-ℕ (succ x) zero = right (λ ())
comp-ℕ (succ x) (succ y) with comp-ℕ x y
... | left p  = left (cong succ p)
... | right p = right λ pSuccEq → p (succ-eq-pred-eq pSuccEq)

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
rem-ℕ : List {ℕ} → (x : ℕ) → List {ℕ}
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
data Env : Set where
  []       : Env
  env-add  : ℕ → Type → Env → Env


-- Proposition: the provided environment contains the binding from the provided variable to the provided type.
-- m-first = match the first
-- m-tail  = match the tail
data EnvContains : ℕ → Type → Env → Set where
  m-first : (n : ℕ) (t : Type) (env : Env) → EnvContains n t (env-add n t env)
  m-tail  : (n n₁ : ℕ) (t t₁ : Type) (env : Env) → EnvContains n t (env) → EnvContains n t (env-add n₁ t₁ env)

-- Typing rules
-- HasType is the set that contains the proofs that the term M has the type T in the environment E
--             E      M       T        E = environment   M = term   T = type
data HasType : Env → Term → Type → Set where
  t-true  : (env : Env) → HasType env true Bool
  t-false : (env : Env) → HasType env false Bool
  t-num   : (env : Env) (n : ℕ) → HasType env (num n) Nat
  t-sum   : (env : Env) (n1 n2 : Term) (p1 : HasType env n1 Nat) (p2 : HasType env n2 Nat) → HasType env (plus n1 n2) Nat
  t-if    : (env : Env) (e1 e2 e3 : Term) (t : Type) (p1 : HasType env e1 Bool) (p2 : HasType env e2 t) (p3 : HasType env e3 t) → HasType env (if e1 e2 e3) t
  t-app   : (env : Env) (e1 e2 : Term) (t1 t2 : Type) (p1 : HasType env e1 (Tarrow t1 t2)) (p2 : HasType env e2 t1) → HasType env (app e1 e2) t2
  t-fun   : (env : Env) (x : ℕ) (t1 t2 : Type) (e1 : Term) (p : HasType (env-add x t1 env) e1 t2) → HasType env (fun x t1 e1) (Tarrow t1 t2)
  t-var   : (env : Env) (x : ℕ) (t : Type) (p : EnvContains x t env) → HasType env (var x) t


data Value : Term → Set where
  v-true : Value true
  v-false : Value false
  v-num : (n : ℕ) → Value (num n)
  v-fun : (x : ℕ) (t : Type) (e : Term) →  Value (fun x t e)


-- Substitution
-- occurences of the variable x are substituted with the term m in term t, producing a new term  
subst : ℕ → Term → Term → Term
subst x m true          = true
subst x m false         = false
subst x m (num n)       = num n
subst x m (var y) with comp-ℕ x y
... | left p = m         -- case x equals y
... | right p = var y    -- case x not equals y
subst x m (plus e1 e2)  = plus (subst x m e1) (subst x m e2)
subst x m (if e1 e2 e3) = if (subst x m e1) (subst x m e2) (subst x m e3)
subst x m (app e1 e2)   = app (subst x m e1) (subst x m e2)
subst x m (fun y t e)   = fun y t (subst x m e) -- ???
-- y should not appear in fv(e) ???
-- the substitution in this case should not be defined.
-- we define it anyway, we force this to not happen in the typing rules
-- here we have to deal with alpha equivalence


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
  e-beta     : (x : ℕ) (t : Type) (b e1 : Term) (p1 : Value b) → EvalTo (app (fun x t e1) b) (subst x b e1)
  e-app1     : (m1 m1' m2 : Term) (p1 : EvalTo m1 m1') → EvalTo (app m1 m2) (app m1' m2)
  e-app2     : (v1 m2 m2' : Term) (p1 : Value v1) (p1 : EvalTo m2 m2') → EvalTo (app v1 m2) (app v1 m2')


-- Evaluation in multiple steps
-- reflexive and transitive closure
data EvalTo* : Term → Term → Set where
  e-refl : (e1 : Term) → EvalTo* e1 e1                                          -- reflexivity
  e-trans : (e1 e2 e3 : Term) → EvalTo* e1 e2 → EvalTo* e2 e3 → EvalTo* e1 e3   -- transitivity


-- INVERTION LEMMAS
-- invertion lemma for bool terms 
lemma-inversion-true : (env : Env) (t : Type) → HasType env true t → t ≡ Bool
lemma-inversion-true env Bool (t-true env) = refl Bool

lemma-inversion-false : (env : Env) (t : Type) → HasType env false t → t ≡ Bool
lemma-inversion-false env Bool (t-false env) = refl Bool

-- invertion lemma for sum term 
lemma-inversion-nat : (Γ : Env) (m1 m2 : Term) (t : Type) → HasType Γ (plus m1 m2) t → t ≡ Nat
lemma-inversion-nat Γ m1 m2 Nat (t-sum Γ m1 m2 p1 p2) = refl Nat

lemma-inversion-nat-m1 : (Γ : Env) (m1 m2 : Term) (t : Type) → HasType Γ (plus m1 m2) t → HasType Γ m1 Nat
lemma-inversion-nat-m1 Γ m1 m2 Nat (t-sum Γ m1 m2 p1 p2) = p1

lemma-inversion-nat-m2 : (Γ : Env) (m1 m2 : Term) (t : Type) → HasType Γ (plus m1 m2) t → HasType Γ m2 Nat
lemma-inversion-nat-m2 Γ m1 m2 Nat (t-sum Γ m1 m2 p1 p2) = p2

-- invertion lemma for if then else term
lemma-inversion-if-e1 : (Γ : Env) (e1 e2 e3 : Term) (t : Type) → HasType Γ (if e1 e2 e3) t → HasType Γ e1 Bool
lemma-inversion-if-e1 env e1 e2 e3 t (t-if env e1 e2 e3 t p1 p2 p3) = p1

lemma-inversion-if-e2 : (Γ : Env) (e1 e2 e3 : Term) (t : Type) → HasType Γ (if e1 e2 e3) t → HasType Γ e2 t
lemma-inversion-if-e2 env e1 e2 e3 t (t-if env e1 e2 e3 t p1 p2 p3) = p2

lemma-inversion-if-e3 : (Γ : Env) (e1 e2 e3 : Term) (t : Type) → HasType Γ (if e1 e2 e3) t → HasType Γ e3 t
lemma-inversion-if-e3 env e1 e2 e3 t (t-if env e1 e2 e3 t p1 p2 p3) = p3

-- invertion lemma for variable term
lemma-invertion-var : (Γ : Env) (x : ℕ) (t : Type) → HasType Γ (var x) t → EnvContains x t Γ
lemma-invertion-var env x t (t-var env x t p) = p     -- p is the proof that "env" contains "x"

lemma-invertion-app : (Γ : Env) (m1 m2 : Term) (t : Type) → HasType Γ (app m1 m2) t → ∃ Type (λ t1 → (HasType Γ m1 (Tarrow t1 t)) & (HasType Γ m2 t1))
lemma-invertion-app Γ m1 m2 t2 (t-app Γ m1 m2 t1 t2 p1 p2) = exists t1 (and p1 p2)

lemma-invertion-fun : (Γ : Env) (m : Term) (x : ℕ) (t1 t : Type) → HasType Γ (fun x t1 m) t → ∃ Type (λ t2 → (t ≡ (Tarrow t1 t2)) & HasType (env-add x t1 Γ) m t2)
lemma-invertion-fun Γ m x t1 (Tarrow t1 t2) (t-fun Γ x t1 t2 m p) = exists t2 (and (refl (Tarrow t1 t2)) p)


-- CANONICAL FORMS LEMMAS
-- if v is a value of type Bool then v is ewither true or false
lemma-canon-bool : {Γ : Env} (m : Term) → Value m → (HasType Γ m Bool) →
          (m ≡ true) ⊎ (m ≡ false)
lemma-canon-bool true pv (t-true Γ) = left (refl true)
lemma-canon-bool false pv (t-false Γ) = right (refl false)

lemma-canon-nat : {Γ : Env} (m : Term) → Value m → (HasType Γ m Nat) →
          ∃ ℕ (λ n → m ≡ num n)
lemma-canon-nat (num n) pv (t-num Γ n) = exists n (refl (num n))

lemma-canon-arrow : {Γ : Env} {t1 t2 : Type} (m : Term) → Value m → (HasType Γ m (Tarrow t1 t2)) →
          ∃ ℕ (λ x → (∃ Term (λ m1 → m ≡ (fun x t1 m1))))
lemma-canon-arrow (fun x t1 e1) pv (t-fun Γ x t1 t2 e1 pt) = exists x (exists e1 (refl (fun x t1 e1)))



-- some test examples
ex : HasType [] (if true (num (succ zero)) (num zero)) Nat
ex = t-if [] true (num (succ zero)) (num zero) Nat (t-true [])
          (t-num [] (succ zero)) (t-num [] zero) 
  
ex' : HasType [] (plus (num (succ (succ zero))) (num zero)) Nat
ex' = t-sum [] (num (succ (succ zero))) (num zero)
        (t-num [] (succ (succ zero))) (t-num [] zero)

ex'' : EnvContains zero Nat (env-add zero Nat []) 
ex'' = m-first zero Nat []

ex''' : EnvContains zero Nat (env-add zero Nat (env-add (succ zero) Nat []))
ex''' = m-first zero Nat (env-add (succ zero) Nat [])

ex'''' : EnvContains (succ zero) Bool (env-add zero Nat (env-add (succ zero) Bool []))
ex'''' = m-tail (succ zero) zero Bool Nat (env-add (succ zero) Bool [])
           (m-first (succ zero) Bool []) 

ex5 : EvalTo (if true (num (succ zero)) (num zero)) (num (succ zero))
ex5 = e-if-true (num (succ zero)) (num zero)

ex7 : in-list zero (zero ∷ [])
ex7 = in-head zero []

ex8 : in-list zero ((succ zero) ∷ (zero ∷ []))
ex8 = in-tail zero (succ zero) (zero ∷ []) (in-head zero [])

ex9 : in-list zero ((succ (succ zero)) ∷ ((succ zero) ∷ (zero ∷ [])))
ex9 = in-tail zero (succ (succ zero)) (succ zero ∷ (zero ∷ []))
        (in-tail zero (succ zero) (zero ∷ []) (in-head zero []))


ex-exists : ∃ ℕ (λ x → (succ x) ≡ (succ (succ zero)))
ex-exists = exists (succ zero) (refl (succ (succ zero)))

