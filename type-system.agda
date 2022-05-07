

data _≡_ {A : Set} : A → A → Set where
  refl : (a : A) → a ≡ a

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + b   = b
succ a + b = succ (a + b)

-- Language types
data Type : Set where
  Bool   : Type
  Int    : Type
  Tarrow : Type → Type → Type

-- Language terms
data Term : Set where
  true  : Term                          
  false : Term
  num   : ℕ → Term                    -- number
  var   : ℕ → Term                     -- variable
  plus  : Term → Term → Term          -- sum between natural numbers
  if    : Term → Term → Term → Term  -- if e1 then e1 else e3
  app   : Term → Term → Term          -- function application
  fun   : ℕ → Type → Term → Term     -- labda abstraction


data List {A : Set} : Set where
  []  : List {A}
  _∷_ : (x : A) → (xs : List {A}) → List {A} 


-- List concatenation
_++_ : {A : Set} → List {A} → List {A} → List {A}
[] ++ l2       = l2
(x ∷ l1) ++ l2 = x ∷ (l1 ++ l2)


-- Remove the given element from the list
rem : {A : Set} → List {A} → (x : A) → List {A}
rem [] x = []
rem (x ∷ l) y = {!!}


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
fv (fun x t e)   = rem (fv e) x 


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

-- evaluation rules
-- HasType is the set that contains the proofs that the term M has the type T in the environment E
--             E      M       T        E = environment   M = term   T = type
data HasType : Env → Term → Type → Set where
  t-true  : (env : Env) → HasType env true Bool
  t-false : (env : Env) → HasType env false Bool
  t-num   : (env : Env) (n : ℕ) → HasType env (num n) Int
  t-sum   : (env : Env) (n1 n2 : Term) (p1 : HasType env n1 Int) (p2 : HasType env n2 Int) → HasType env (plus n1 n2) Int
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
subst x m true = true
subst x m false = false
subst x m (num n) = num n
subst x m (var y) = {!!} -- here I have to split the two cases, when x = x₁, and when x ≠ x₁
subst x m (plus e1 e2) = plus (subst x m e1) (subst x m e2)
subst x m (if e1 e2 e3) = if (subst x m e1) (subst x m e2) (subst x m e3)
subst x m (app e1 e2) = app (subst x m e1) (subst x m e2)
subst x m (fun y t e) = {!!}                         -- y not in fv(e) ???



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
  e-refl : (e1 : Term) → EvalTo* e1 e1                                            -- reflexivity
  e-trans : (e1 e2 e3 : Term) → EvalTo* e1 e2 → EvalTo* e2 e3 → EvalTo* e1 e3   -- transitivity


-- invertion lemma for type bool 
lemma-inversion-true : (env : Env) (t : Type) → HasType env true t → t ≡ Bool
lemma-inversion-true env Bool (t-true env) = refl Bool

lemma-inversion-false : (env : Env) (t : Type) → HasType env false t → t ≡ Bool
lemma-inversion-false env Bool (t-false env) = refl Bool

-- invertion lemma for type nat 
lemma-inversion-nat : (Γ : Env) (m1 m2 : Term) (t : Type) → HasType Γ (plus m1 m2) t → t ≡ Int
lemma-inversion-nat Γ m1 m2 Int (t-sum Γ m1 m2 p1 p2) = refl Int

lemma-inversion-nat-m1 : (Γ : Env) (m1 m2 : Term) (t : Type) → HasType Γ (plus m1 m2) t → HasType Γ m1 Int
lemma-inversion-nat-m1 Γ m1 m2 Int (t-sum Γ m1 m2 p1 p2) = p1

lemma-inversion-nat-m2 : (Γ : Env) (m1 m2 : Term) (t : Type) → HasType Γ (plus m1 m2) t → HasType Γ m2 Int
lemma-inversion-nat-m2 Γ m1 m2 Int (t-sum Γ m1 m2 p1 p2) = p2








ex : HasType [] (if true (num (succ zero)) (num zero)) Int
ex = t-if [] true (num (succ zero)) (num zero) Int (t-true [])
          (t-num [] (succ zero)) (t-num [] zero) 
  
ex' : HasType [] (plus (num (succ (succ zero))) (num zero)) Int
ex' = t-sum [] (num (succ (succ zero))) (num zero)
        (t-num [] (succ (succ zero))) (t-num [] zero)

-- check if the environment contains the variable bouded to that type
ex'' : EnvContains zero Int (env-add zero Int []) 
ex'' = m-first zero Int []

ex''' : EnvContains zero Int (env-add zero Int (env-add (succ zero) Int []))
ex''' = m-first zero Int (env-add (succ zero) Int [])

ex'''' : EnvContains (succ zero) Bool (env-add zero Int (env-add (succ zero) Bool []))
ex'''' = m-tail (succ zero) zero Bool Int (env-add (succ zero) Bool [])
           (m-first (succ zero) Bool []) 

ex5 : EvalTo (if true (num (succ zero)) (num zero)) (num (succ zero))
ex5 = e-if-true (num (succ zero)) (num zero)


ex6 : EvalTo* (if true (plus (num (succ zero)) (num (succ zero))) (num zero)) (num (succ (succ zero)))
ex6 = {!e-trans!}

ex7 : in-list zero (zero ∷ [])
ex7 = in-head zero []

ex8 : in-list zero ((succ zero) ∷ (zero ∷ []))
ex8 = in-tail zero (succ zero) (zero ∷ []) (in-head zero [])

ex9 : in-list zero ((succ (succ zero)) ∷ ((succ zero) ∷ (zero ∷ [])))
ex9 = in-tail zero (succ (succ zero)) (succ zero ∷ (zero ∷ []))
        (in-tail zero (succ zero) (zero ∷ []) (in-head zero []))


