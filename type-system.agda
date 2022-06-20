{-
The purpose of this project is to formalize a basic functional language with
its type system and to prove the well known safety theorem.
-}

{-
Agda is a functional programming language based on Marting Martin-Löf's Type Theory.
The main feature of the language are dependent types.

Dependent type are types that can depends (that are parameterized) on values of
other types.
In common mainstream programming languages such as Java we have Generics: types
that depends on other types.

As an example, in Java we can define the type List<T> that is a generic type
that can be instantiated providing some other type, such as Integer or String,
as parameter T. T must be a type and can't be a value. List<Integer> represents
the type of lists containing integers as elements.

In Agda we can define the type (List : (T : Set) → (n : Nat) → Set) of lists of
lenght n containing elements of type T. The type (List Nat 4) is the type of lists with
lenght 4 containing natural numbers.
This type can't be represented in Java; the second parameter is a value and not
a type.

Dependent types can be used to define propositions by means of Curry–Howard, such
that proofs can be developed withing the language.
In the same language we can develop useful code, such as algorithms, but also
proove properties of code. We could develop a sorting algorithm and also prove
its correctness, all inside agda.

All functions that can be defined in Agda are computable, that is, evaluates to
a final value in a finite number of steps.
In Agda there is not a clear separation between type checking and execution.
-}

open import basic
open import nat
open import list

-- Language types
data Type : Set where
  Bool     : Type
  Nat      : Type
  Tarrow   : Type → Type → Type

-- The environment is simply a list of types.
-- The environmnet don't contain bindings between variable names and types, but
-- only types.
Env = List {Type}

-- Language terms
-- Terms are represented in the de Brujin way, as nameless terms. (see ch 6 TPL)
-- Note as variables are represented as natural numbers, and lambda abstractions
-- don't carry along variable names.
--
-- A variable with number "n" indicates the parameter introduced by the n-th lambda
-- abstraction at its left.
--
-- fun Bool fun Nat var 0
-- This term has type Bool → Nat → Nat since the term "var 0" indicates the parameter
-- introduced by "fun Nat".
--
-- fun Bool fun Nat var 1
-- This term has type Bool → Nat → Nat since the term "var 1" indicates the parameter
-- introduced by "fun Bool".
--
-- examples (ex 6.1.1 TPL):
-- standard term                                                de Brujin term
-- c₀ = λs. λz. z                                               λ. λ. 0
-- c₂ = λs. λz. s (s z)                                         λ. λ. 1 (1 0)
-- plus = λm. λn. λs. λz. m s (n z s)                           λ. λ. λ. λ. 3 1 (2 0 1)
-- fix = λf. (λx. f (λy. (x x) y )) (λx. f (λy. (x x) y))       λ. (λ. 1 (λ. (1 1) 0)) (λ. 1 (λ. (1 1) 0))
-- foo = (λx. (λx. x)) (λx. x)                                  (λ. (λ. 0)) (λ. 0)

-- TODO book says: we need to keep careful track of how many free variables each
-- term may contain. why ?
data Term : Set where
  true          :                              Term
  false         :                              Term
  num           : (n : ℕ)                    → Term
  if_then_else_ : Term → Term → Term         → Term
  _+ₙ_          : Term → Term                → Term
  var           : (x : ℕ)                    → Term
  _app_         : (e1 : Term) → (e2 : Term)  → Term
  fun           : (t : Type) → (e1 : Term)   → Term  -- "fun t" is a binder whose scope is "e1"

infixl 31 var
infixl 21 num
infixl 30 _app_
infixl 29 _+ₙ_
infixl 28 if_then_else_

-- Type judgmenet.
-- The dependent type HasType Γ M T correspond to the following proposition:
--      In environment Γ, the term M has type T
-- An element of the type HasType Γ M T is a witness that the term M has type T
-- in the environment Γ.
data HasType : Env → Term → Type → Set where
  t-true  : {Γ : Env}
            → HasType Γ true Bool

  t-false : {Γ : Env}
            → HasType Γ false Bool

  t-nat   : {Γ : Env} {n : ℕ}
            → HasType Γ (num n) Nat

  t-sum   : {Γ : Env} {m1 m2 : Term}
            → (p1 : HasType Γ m1 Nat)
            → (p2 : HasType Γ m2 Nat)
            → HasType Γ (m1 +ₙ m2) Nat

  t-var   : {Γ : Env} {x : ℕ} {t : Type}
            → (p : (getIdx Γ x) ≡ some t)
            → HasType Γ (var x) t

  t-app   : {Γ : Env} {m1 m2 : Term} {t1 t2 : Type}
            → (p1 : HasType Γ m1 (Tarrow t1 t2))
            → (p2 : HasType Γ m2 t1)
            → HasType Γ (m1 app m2) t2
            
  t-fun   : {Γ : Env} {t1 t2 : Type} {m : Term}
            → (p : HasType (t1 ∷  Γ) m t2)
            → HasType Γ (fun t1 m) (Tarrow t1 t2)

  t-if    : {Γ : Env} {m1 m2 m3 : Term} {t : Type}
            → (p1 : HasType Γ m1 Bool)
            → (p2 : HasType Γ m2 t)
            → (p3 : HasType Γ m3 t)
            → HasType Γ (if m1 then m2 else m3) t


-- Unicity of typing
-- Given a context Γ and a term M, there exists at most one type T such that
-- Γ ⊢ M : T is derivable.
-- We can equivalently say that if  Γ ⊢ M : T₁ and  Γ ⊢ M : T₂ are two derivable
-- judgements, then T₁ = T₂.
type-unicity : {Γ : Env} {m : Term} {t1 t2 : Type}
    → HasType Γ m t1
    → HasType Γ m t2
    → t1 ≡ t2
type-unicity t-true  t-true              = refl
type-unicity t-false t-false             = refl
type-unicity t-nat   t-nat               = refl
type-unicity (t-sum p1 p3) (t-sum p2 p4) = refl
type-unicity (t-var p1) (t-var p2)       = eq-opt-some-to-val (trans (symm p1) p2)
type-unicity (t-app p1 p3) (t-app p2 p4) with type-unicity p1 p2
... | refl = refl
type-unicity (t-fun p1) (t-fun p2) with type-unicity p1 p2
... | refl = refl
type-unicity (t-if p1 p3 p4) (t-if p2 p5 p6) with type-unicity p3 p5
... | refl = refl


-- Definition of values.
-- The dependent type Value M represents the proposition:
--     The term M is a value
data Value : Term → Set where
  v-true  :                          Value true
  v-false :                          Value false
  v-nat   : {n : ℕ}                → Value (num n)
  v-fun   : {t : Type} {e : Term}  → Value (fun t e)

-- Free variables of a term
-- The free variables of a term is a list of ℕ.
-- Note how free variables are defined for lambda abstractions.
-- The same number can appear multiple times inside the list.
--
-- What free variables are in de Brujin terms ?
-- A variable is free when there is no abstraction that binds it.
-- A term with free varibales can only be typed in an environment that contains
-- bindings for those variables.
-- In the term "var 0", 0 is a free variable because there is no lambda abstraction
-- to which the variable points. An environment with lenght at least 1 is needed
-- to type this term.
-- In the term "fun Bool var 1" the free variable is 0 (not 1). To type this term
-- we need an environment that specify a type at least for index 0.
--
-- The list of free variables of a term is the list of indices that must be available
-- in an environment to type that term.
-- A term with free variables [3, 5, 1] can only be typed in an env. with lenght
-- at least 6.
fv : Term → List {ℕ}
fv true                     = []
fv false                    = []
fv (num n)                  = []
fv (m1 +ₙ m2)               = (fv m1) ++ (fv m2)
fv (var x)                  = x ∷ []
fv (m1 app m2)              = (fv m1) ++ (fv m2)
fv (fun t m)                = decAll ((fv m) remove zero)
fv (if m1 then m2 else m3)  = (fv m1 ++ fv m2) ++ fv m3


-- Shift operation (used to define substitution)
-- Used to increase by "d" (shift up) the free variables of a term.
--
-- examples (ex 6.2.2 TPL):
-- ↑² (λ.λ. 1 (0 2)) = λ.λ. 1 (0 4)
-- ↑² (λ. 0 1 (λ. 0 1 2)) = λ. 0 3 (λ. 0 1 4)
shift : ℕ → ℕ → Term → Term
shift d c (var x) with x <? c
... | left  p         = var x
... | right p         = var (x + d)
shift d c (e1 app e2) = (shift d c e1) app  (shift d c e2)
shift d c (fun t e1)  = fun t (shift d (succ c) e1)
shift d c true        = true
shift d c false       = false
shift d c (num n)     = num n
shift d c (m1 +ₙ m2)  = (shift d c m1) +ₙ (shift d c m2)
shift d c (if m1 then m2 else m3)
  = if (shift d c m1) then (shift d c m2) else (shift d c m3)

-- Shift back (used to define substitution)
-- Used to decrease by "d" (shift down) the free variables of a term.
shift-back : ℕ → ℕ → Term → Term
shift-back d c (var x) with x <? c
... | left  p              = var x
... | right p              = var (x - d)
shift-back d c (e1 app e2) = (shift-back d c e1) app  (shift-back d c e2)
shift-back d c (fun t e1)  = fun t (shift-back d (succ c) e1)
shift-back d c true        = true
shift-back d c false       = false
shift-back d c (num n)     = num n
shift-back d c (m1 +ₙ m2)  = (shift-back d c m1) +ₙ (shift-back d c m2)
shift-back d c (if m1 then m2 else m3)
  = if (shift-back d c m1) then (shift-back d c m2) else (shift-back d c m3)


-- Substitution M{j:=N}.
-- Substitute the variable j with the term N in the term M.
--
-- examples (ex 6.2.5 TPL):
-- assuming Γ = a,b
-- [b → a] (b (λx.λy.b)) = [0 → 1] (0 (λ.λ.2)) = 1 (λ)
-- [b → a (λz.a)] (b (λx.b)) = [0 → 1 (λ.2)] (0 (λ.1))
-- [b → a] (λb. b a) = [0 → 1] (λ. 0 2)
-- [b → a] (λa. b a) = [0 → 1] (λ. 1 0)
subst : ℕ → Term → Term → Term
subst j s (var x) with x ≡? j
... | left  p          = s
... | right p          = var x
subst j s (e1 app e2)  = (subst j s e1) app (subst j s e2)
subst j s (fun t e1)   = fun t (subst (succ j) (shift one zero s) e1)
subst j s true         = true
subst j s false        = false
subst j s (num n)      = num n
subst j s (m1 +ₙ m2)   = (subst j s m1) +ₙ (subst j s m2)
subst j s (if m1 then m2 else m3)
  = if (subst j s m1) then (subst j s m2) else (subst j s m3)

-- Evaluation judgement.
-- The dependent type M ⇒ M' corresponds to the following judgement:
--     The term M evaluates to the term M' in one step.
-- Note as beta reduction is defined using the shift operations.
data _⇒_ : Term → Term → Set where
  e-app1     : {m1 m1' m2 : Term}
             → (p1 : m1 ⇒ m1')
             → (m1 app m2) ⇒ (m1' app m2)

  e-app2     : {v1 m2 m2' : Term}
             → (p1 : Value v1)
             → (p2 : m2 ⇒ m2')
             → (v1 app m2) ⇒ (v1 app m2')

  e-beta     : {t : Type} {e1 v2 : Term}
             → (p1 : Value v2)
             → ((fun t e1) app v2) ⇒ shift-back 1 0 (subst 0 (shift 1 0 v2) e1)

  e-sum-l    : {m1 m1' m2 : Term}
             → (p1 : m1 ⇒ m1')
             → (m1 +ₙ m2) ⇒ (m1' +ₙ m2)

  e-sum-r    : {v1 m2 m2' : Term}
             → (p1 : Value v1)
             → (p2 : m2 ⇒ m2')
             → (v1 +ₙ m2) ⇒ (v1 +ₙ m2')

  e-sum      : {n1 n2 : ℕ}
             → ((num n1) +ₙ (num n2)) ⇒ (num (n1 + n2))

  e-if-guard : {m1 m1' m2 m3 : Term}
             → (p1 : m1 ⇒ m1')
             → (if m1 then m2 else m3) ⇒ (if m1' then m2 else m3)

  e-if-true  : {m2 m3 : Term}
             → (if true then m2 else m3) ⇒ m2

  e-if-false : {m2 m3 : Term}
             → (if false then m2 else m3) ⇒ m3


-- Γ,Γ₁ ⊢ m : tm
-- ⇒ Γ,tu,Γ₁ ⊢ ↑[1,len(Γ₁)] m : tm
weakening-2 : {Γ : Env} {Γ₁ : Env} {m : Term} {tm tu : Type}
        → HasType (Γ₁ ++ Γ) m tm
        → HasType (Γ₁ ++ (tu ∷ Γ)) (shift one (len Γ₁) m) tm
weakening-2 t-true           = t-true
weakening-2 t-false          = t-false
weakening-2 t-nat            = t-nat
weakening-2 (t-app p1 p2)    = t-app (weakening-2 p1) (weakening-2 p2)
weakening-2 (t-sum p1 p2)    = t-sum (weakening-2 p1) (weakening-2 p2)
weakening-2 (t-fun p)        = t-fun (weakening-2 p)
weakening-2 (t-if p1 p2 p3)  = t-if (weakening-2 p1) (weakening-2 p2) (weakening-2 p3)
weakening-2 {Γ} {Γ₁} {var x} {tm} {tu} (t-var {_} {i} p1)
  with x <? (len Γ₁)
... | left  p2
  rewrite eq-idx-in-first Γ₁ Γ i p2
        | eq-idx-in-first-in-concat Γ₁ (tu ∷ Γ) i p2 = t-var p1
... | right p2
  rewrite symm+ x (succ zero)
        | eq-idx-add-one-mid Γ₁ Γ tu x p2  = t-var p1


-- Γ ⊢ M : T
-- ⇒ Γ,tu ⊢ ↑[1,0] M : T
--
-- If in Γ I can say that M has type T, then I can shift up by 1 all the free variables
-- of the term and add a dummy type to the context. The new term would keep the same
-- type in the new context.
-- I'm weakening the context because I'm adding unneeded information.
weakening : {Γ : Env} {m : Term} {t tu : Type}
        → HasType Γ m t
        → HasType (tu ∷ Γ) (shift one zero m) t
weakening t-true             = t-true
weakening t-false            = t-false
weakening t-nat              = t-nat
weakening (t-app p1 p2)      = t-app (weakening p1) (weakening p2)
weakening (t-sum p1 p2)      = t-sum (weakening p1) (weakening p2)
weakening (t-if p1 p2 p3)    = t-if  (weakening p1) (weakening p2) (weakening p3)
weakening (t-fun p)          = t-fun (weakening-2 p)
weakening {Γ} {var x} (t-var p)
  with x <? zero
... | right p2
  rewrite symm+ x (succ zero) = t-var p


-- Γ,S,Γ₁ ⊢ M : T      and
-- Γ,S,Γ₁ ⊢ N : S
-- ⇒ Γ,S,Γ₁ ⊢ M {len(Γ₁) := N} : T
--
-- If in Δ I can say that M has type T and N has type S,
-- and in Δ I have the type S at index <i>,
-- then the term I obtain substituting the free variable <i> of M with N, keeps
-- the same type T in Δ.
substitution : {Γ Γ₁ : Env} {S T : Type} {M N : Term}
        → HasType (Γ₁ ++ (S ∷ Γ)) M T
        → HasType (Γ₁ ++ (S ∷ Γ)) N S
        → HasType (Γ₁ ++ (S ∷ Γ)) (subst (len Γ₁) N M) T
substitution t-true  p2         = t-true
substitution t-false p2         = t-false
substitution t-nat   p2         = t-nat
substitution (t-app p1 p2) p3   = t-app (substitution p1 p3) (substitution p2 p3)
substitution (t-sum p1 p2) p3   = t-sum (substitution p1 p3) (substitution p2 p3)
substitution (t-fun p1) p2      = t-fun (substitution p1 (weakening p2))
substitution (t-if p1 p2 p3) p4 = t-if  (substitution p1 p4) (substitution p2 p4) (substitution p3 p4)
substitution {Γ} {Γ₁} {S} (t-var {_} {x} p1) p2
  with x ≡? (len Γ₁)
... | left  p
  rewrite eq-idx-in-second Γ₁ (S ∷ Γ) x (x≡y-to-x≥y x (len Γ₁) p)
        | x≡y-to-x-y≡0 x (len Γ₁) p
        | eq-opt-some-to-val p1 = p2
... | right p                   = t-var p1



-- Γ,S,Γ₁ ⊢ M : T
-- len(Γ₁) ∉ fv(M)
-- ⇒ Γ,Γ₁ ⊢ ↑ -1 len(Γ₁) M : T
--
-- If in Δ I can say that M has type T and Δ assigns a type to variable <i>
-- that doesn't appear free in M, then I can remove that type from Δ and adjust
-- M in a way that it keeps its semantics and its type in the new Δ.
-- 
-- We are somehow strengthening the context removing useless assumptions.
-- It is useless to assume type S for a variable <i> if that variable doesn't
-- appear in the term.
strengthening : {t : Type} (Γ : Env) (tu : Type) (Γ₁ : Env) (m : Term)
        → HasType (Γ₁ ++ (tu ∷ Γ)) m t
        → len (Γ₁) ∉ (fv m)
        → HasType (Γ₁ ++ Γ) (shift-back one (len Γ₁) m) t
strengthening Γ tu Γ₁ true    t-true  p2 = t-true
strengthening Γ tu Γ₁ false   t-false p2 = t-false
strengthening Γ tu Γ₁ (num n) t-nat   p2 = t-nat
strengthening Γ tu Γ₁ (m1 app m2) (t-app p1 p2) lenΓ₁-∉-fvM = 
    t-app
      (strengthening Γ tu Γ₁ m1 p1 (not-in-concat-not-in-first  lenΓ₁-∉-fvM))
      (strengthening Γ tu Γ₁ m2 p2 (not-in-concat-not-in-second lenΓ₁-∉-fvM))
strengthening Γ tu Γ₁ (m1 +ₙ m2) (t-sum p1 p2) lenΓ₁-∉-fvM = 
    t-sum
      (strengthening Γ tu Γ₁ m1 p1 (not-in-concat-not-in-first  lenΓ₁-∉-fvM))
      (strengthening Γ tu Γ₁ m2 p2 (not-in-concat-not-in-second lenΓ₁-∉-fvM))
strengthening Γ tu Γ₁ (if m1 then m2 else m3) (t-if p1 p2 p3) lenΓ₁-∉-fvM =
    t-if
      (strengthening Γ tu Γ₁ m1 p1 lenΓ₁-∉-fvm1)
      (strengthening Γ tu Γ₁ m2 p2 lenΓ₁-∉-fvm2)
      (strengthening Γ tu Γ₁ m3 p3 lenΓ₁-∉-fvm3)
    where
    lenΓ₁-∉-fvm1++fvm2 : len Γ₁ ∉ (fv m1 ++ fv m2)
    lenΓ₁-∉-fvm1++fvm2 = not-in-concat-not-in-first lenΓ₁-∉-fvM

    -- There are no variables with index = len Γ₁ in the free variables of m1,m2 and m3
    lenΓ₁-∉-fvm1 : len Γ₁ ∉ (fv m1)
    lenΓ₁-∉-fvm1 = not-in-concat-not-in-first lenΓ₁-∉-fvm1++fvm2

    lenΓ₁-∉-fvm2 : len Γ₁ ∉ (fv m2)
    lenΓ₁-∉-fvm2 = not-in-concat-not-in-second lenΓ₁-∉-fvm1++fvm2

    lenΓ₁-∉-fvm3 : len Γ₁ ∉ (fv m3)
    lenΓ₁-∉-fvm3 = not-in-concat-not-in-second lenΓ₁-∉-fvM
      
strengthening Γ tu Γ₁ (fun tx m) (t-fun p1) lenΓ₁-∉-fvM =
    t-fun (strengthening Γ tu (tx ∷ Γ₁) m p1 (notin-dec-not-succ-in-list' lenΓ₁-∉-fvM))
strengthening Γ tu Γ₁ (var x) (t-var {_} {_} {t} p1) lenΓ₁-∉-fvM
  with x <? len(Γ₁)
... | left  p
  rewrite eq-idx-in-first Γ₁ (tu ∷ Γ) x p
        | eq-idx-in-first-in-concat Γ₁ Γ x p = t-var p1
... | right p = t-var p-getIdx
  where
  x-not-len : x ≢ len(Γ₁)
  x-not-len = symm≢  (neq-the-first lenΓ₁-∉-fvM)

  x->-len : x > len(Γ₁)
  x->-len = x≥y-and-x≢y-to-x>y p x-not-len

  p-getIdx : getIdx (Γ₁ ++ Γ) (pred x) ≡ some t
  p-getIdx rewrite eq-idx-second-rem-from-center Γ₁ tu Γ x x->-len = p1



-- for any k,        k ∉ fv (↑[1,k] M)
-- 
-- This is intuitively true because "↑[1,k] M" sums 1 to all the free variables
-- of M that are ≥ k.
-- If a free variable "k" appears in M, it is incremented to "k + 1".
-- If a free variable "k-1" appears in M, it stays as it is.
-- All free variables "k" are incremented and no free variable is incremented to "k".
-- So after this operation there can't be free variables "k" in M.
not-in-fv : (k : ℕ)
        → (m : Term)
        → k ∉ fv (shift one k m)
not-in-fv k true                    = λ ()
not-in-fv k false                   = λ ()
not-in-fv k (num n)                 = λ ()
not-in-fv k (if m1 then m2 else m3) = -- by inductive hypothesys
  notin-first-notin-second-notin-concat
    (notin-first-notin-second-notin-concat (not-in-fv k m1) (not-in-fv k m2))
    (not-in-fv k m3)
not-in-fv k (m1 +ₙ m2)             =
  notin-first-notin-second-notin-concat (not-in-fv k m1) (not-in-fv k m2)
not-in-fv k (m1 app m2)            =
  notin-first-notin-second-notin-concat (not-in-fv k m1) (not-in-fv k m2)
not-in-fv k (var x) with x <? k
... | left  p = λ p1 → x∈y∷[]-x≢y-to-⊥ p1 (symm≢ (x<y-to-x≢y p))
... | right p rewrite symm+ x (succ zero)
  = λ p1 → x∈y∷[]-x≢y-to-⊥ p1 (symm≢ (x>y-to-x≢y (x≥y-to-x+1>y p)))
not-in-fv k (fun t m)
  = succ-notin-list-not-in-dec
        (notin-after-remove zero (not-in-fv (succ k) m))
        (x-notin-list-remove-x zero (fv (shift one (succ k) m)))
  where
  k+1-not-in-fv : (succ k) ∉ fv (shift one (succ k) m)
  k+1-not-in-fv = not-in-fv (succ k) m


-- y ∉ fv(M),   y ≥ k   ⇒   y + 1 ∉ fv (↑[1, k] M)
-- auxiliary
not-in-fv'' : {k y : ℕ} {s : Term}
  → y ∉ fv s
  → y ≥ k
  → (succ y) ∉ fv (shift one k s)
not-in-fv'' {k} {y} {true} p1 p2                   = λ ()
not-in-fv'' {k} {y} {false} p1 p2                  = λ ()
not-in-fv'' {k} {y} {num n} p1 p2                  = λ ()
not-in-fv'' {k} {y} {if m1 then m2 else m3} p1 p2  =  -- by inductive hypothesys
  notin-first-notin-second-notin-concat
    (notin-first-notin-second-notin-concat
      (not-in-fv'' {k} {y} {m1} (not-in-concat-not-in-first  (not-in-concat-not-in-first p1)) p2)
      (not-in-fv'' {k} {y} {m2} (not-in-concat-not-in-second {_} {y} {fv m1} (not-in-concat-not-in-first p1)) p2))
    (not-in-fv'' {k} {y} {m3} (not-in-concat-not-in-second p1) p2)

not-in-fv'' {k} {y} {m1 +ₙ m2} p1 p2               = 
  notin-first-notin-second-notin-concat
    (not-in-fv'' {k} {y} {m1} (not-in-concat-not-in-first  p1) p2)
    (not-in-fv'' {k} {y} {m2} (not-in-concat-not-in-second p1) p2)
not-in-fv'' {k} {y} {m1 app m2} p1 p2              =
  notin-first-notin-second-notin-concat
    (not-in-fv'' {k} {y} {m1} (not-in-concat-not-in-first  p1) p2)
    (not-in-fv'' {k} {y} {m2} (not-in-concat-not-in-second p1) p2)
not-in-fv'' {k} {y} {var x} p1 p2 with x <? k
... | left  p3 = λ { (in-head (succ y) []) → p2 (x+1<y-to-x<y p3)} -- p2 and p3 are in contraddiction
... | right p3 rewrite symm+ x (succ zero) = λ { (in-head (succ x) []) → p1 (in-head x []) }
not-in-fv'' {k} {y} {fun t s} p1 p2
  = succ-notin-list-not-in-dec
         (notin-after-remove zero (not-in-fv'' {succ k} {succ y} {s} (notin-dec-not-succ-in-list' p1) (x≥y-to-x+1≥y+1 p2) ))
         (x-notin-list-remove-x zero (fv (shift one (succ k) s)))


-- If k ∉ fv(N)    then   k ∉ fv([k := N] M)
--
-- If k is not in the free variables of the term N, then when I substitute the
-- free variables "k" with N in the term M, I get a term where free variables "k"
-- doesn't appear.
-- This result is intuitive because during the substitution we replace all "k"s
-- with N (that in turn doesn't contain "k"s).
not-in-fv' : {s : Term} (k : ℕ)
  → (m : Term)
  → k ∉ fv s
  → k ∉ fv (subst k s m)
not-in-fv' k true p1                   = λ ()
not-in-fv' k false p1                  = λ ()
not-in-fv' k (num n) p1                = λ ()
not-in-fv' k (if m1 then m2 else m3) p1 =  -- by inductive hypothesys
  notin-first-notin-second-notin-concat
    (notin-first-notin-second-notin-concat (not-in-fv' k m1 p1) (not-in-fv' k m2 p1))
    (not-in-fv' k m3 p1)
not-in-fv' k (m1 +ₙ m2) p1             = 
  notin-first-notin-second-notin-concat (not-in-fv' k m1 p1) (not-in-fv' k m2 p1)
not-in-fv' k (m1 app m2) p1            = 
  notin-first-notin-second-notin-concat (not-in-fv' k m1 p1) (not-in-fv' k m2 p1)
not-in-fv' k (var x) p1 with x ≡? k
... | left  p = p1
... | right p = λ p2 → x∈y∷[]-x≢y-to-⊥ p2 (symm≢ p)
not-in-fv' {s} k (fun t m) p1
  = succ-notin-list-not-in-dec
        (notin-after-remove zero (not-in-fv' (succ k) m (not-in-fv'' {zero} {k} {s} p1 λ ())))
        (x-notin-list-remove-x zero (fv (subst (succ k) (shift one zero s) m)))


-- -----------------------------------------------------------------------------
-- --------------------------------------------------- SUBJECT REDUCTION THEOREM

-- Γ ⊢ M : T    M ⇒ M'   ⇒   Γ ⊢ M' : T
type-preservation : {Γ : Env} {m m' : Term} {t : Type}
                  → HasType Γ m t
                  → m ⇒ m'
                  → HasType Γ m' t
type-preservation (t-app p1 p3) (e-app1 p2)
  = t-app (type-preservation p1 p2) p3
type-preservation (t-app p1 p3) (e-app2 p2 p4)
  = t-app p1 (type-preservation p3 p4)
type-preservation (t-sum p1 p2) (e-sum-l p3)
  = t-sum (type-preservation p1 p3) p2
type-preservation (t-sum p1 p2) (e-sum-r p3 p4)
  = t-sum p1 (type-preservation p2 p4)
type-preservation (t-sum p1 p2) e-sum
  = t-nat
type-preservation (t-if p1 p2 p3) (e-if-guard p4)
  = t-if (type-preservation p1 p4) p2 p3
type-preservation (t-if p1 p2 p3) e-if-true
  = p2
type-preservation (t-if p1 p2 p3) e-if-false
  = p3
type-preservation {Γ} (t-app {_} {_} {_} {t1} {t2} (t-fun p1) p3) (e-beta {_} {e1} {v2} p)
  = strengthening Γ t1 [] subst-term (substitution p1 (weakening p3)) zero-notin-fv-subst-term
  where
  subst-term : Term
  subst-term = subst zero (shift (succ zero) zero v2) e1

  zero-notin-fv-subst-term : ¬ (zero ∈ fv subst-term)
  zero-notin-fv-subst-term = not-in-fv' zero e1 (not-in-fv zero v2)



-- Evaluation in multiple steps
-- The "evaluation in multiple steps" relation is the reflexive and transitive
-- closure of the one step evaluation relation.
data _⇒*_ : Term → Term → Set where
  e-refl     : (e1 : Term) → e1 ⇒* e1                                -- reflexivity
  e-trans    : {e1 e2 e3 : Term} → e1 ⇒* e2 → e2 ⇒ e3 → e1 ⇒* e3   -- transitivity

infixl 5 _⇒_
infixl 5 _⇒*_


-- Γ ⊢ M : T    M ⇒* M'   ⇒   Γ ⊢ M' : T
--
-- This is type preservation extended to evaluation in multiple steps.
type-preservation' : {Γ : Env} {m m' : Term} {t : Type}
                  → HasType Γ m t
                  → m ⇒* m'
                  → HasType Γ m' t
type-preservation' p1 (e-refl e1)              = p1
type-preservation' p1 (e-trans p2 p3) = type-preservation (type-preservation' p1 p2) p3



-- lemma of canonical forms
lemma-canon-bool : {Γ : Env} {m : Term}
  → Value m
  → HasType Γ m Bool
  → (m ≡ true) ⊎ (m ≡ false)
lemma-canon-bool pv (t-true)       = left refl
lemma-canon-bool pv (t-false)      = right refl

lemma-canon-nat : {Γ : Env} {m : Term}
  → Value m
  → (HasType Γ m Nat)
  → ∃ ℕ (λ n → m ≡ num n)
lemma-canon-nat pv (t-nat {Γ} {n}) = exists n refl

lemma-canon-arrow : {Γ : Env} {t1 t2 : Type} {m : Term}
  → Value m
  → HasType Γ m (Tarrow t1 t2)
  → ∃ Term (λ m1 → m ≡ (fun t1 m1))
lemma-canon-arrow pv (t-fun {Γ} {t1} {t2} {e1} pt) = exists e1 refl


-- -----------------------------------------------------------------------------
-- ------------------------------------------------------------ PROGRESS THEOREM

-- ∅ ⊢ M : T   ⇒   M value or ∃ M' such that M ⇒ M'
--
-- If a term M is well typed in the empty context, either this term is a value
-- or it can make a step of evaluation.
progress : {m : Term} {t : Type}
         → HasType [] m t
         → (Value m) ⊎ (∃ Term (λ m' → m ⇒ m'))
progress t-true            = left v-true
progress t-false           = left v-false
progress t-nat             = left v-nat
progress (t-fun p)         = left v-fun
progress {m} (t-sum {Γ} {m1} {m2} p1 p2) =  m-val-or-eval
  where
  -- use the inductive hypothesis
  -- the subterm m1 is either a value or it can make a step of evaluation
  -- the same holds for the subterm m2: or it is a value or it can evaluate
  m1-val-or-eval : Value m1 ⊎ ∃ Term (λ m1' → m1 ⇒ m1')
  m1-val-or-eval = progress p1

  m2-val-or-eval : Value m2 ⊎ ∃ Term (λ m2' → m2 ⇒ m2')
  m2-val-or-eval = progress p2

  m-val-or-eval : Value m ⊎ ∃ Term (λ m' → m ⇒ m')
  m-val-or-eval = case m1-val-or-eval of λ {
    (left m1Val@(v-nat {n1})) → case m2-val-or-eval of λ {
      (left  (v-nat {n2})) →
             right (exists (num (n1 + n2)) e-sum);
      (right (exists m2' m2Eval)) →
             right (exists (m1 +ₙ m2') (e-sum-r m1Val m2Eval))
      };
    (right (exists m1' m1Eval)) →
             right (exists (m1' +ₙ m2) (e-sum-l m1Eval))
    }

progress {m} (t-app {Γ} {m1} {m2} {t1} p1 p2) = m-val-or-eval
  where
  -- use the inductive hypothesis
  -- the subtern m1 is either a value of it can make a step of evaluation
  -- the same holds for the subterm m2: or it is a value or it can evaluate
  m1-val-or-eval : Value m1 ⊎ ∃ Term (λ m1' → m1 ⇒ m1')
  m1-val-or-eval = progress p1

  m2-val-or-eval : Value m2 ⊎ ∃ Term (λ m2' → m2 ⇒ m2')
  m2-val-or-eval = progress p2

  m-val-or-eval : Value m ⊎ ∃ Term (λ m' → m ⇒ m')
  m-val-or-eval = case m1-val-or-eval of λ {
    (left m1Val@(v-fun {_} {e1})) → case m2-val-or-eval of λ {
      (left  m2Val) →
             right (exists (shift-back 1 zero (subst zero (shift 1 zero m2) e1)) (e-beta m2Val));
      (right (exists m2' m2Eval)) →
             right (exists (m1 app m2') (e-app2 m1Val m2Eval))
      };
    (right (exists m1' m1Eval)) →
           right (exists (m1' app m2) (e-app1 m1Eval))
    } 

progress {m} (t-if {Γ} {m1} {m2} {m3} p1 p2 p3) = m-val-or-eval
  where
  m1-val-or-eval : Value m1 ⊎ ∃ Term (λ m1' → m1 ⇒ m1')
  m1-val-or-eval = progress p1

  m-val-or-eval : Value m ⊎ ∃ Term (λ m' → m ⇒ m')
  m-val-or-eval = case m1-val-or-eval of λ {
    (left v-true)  → right (exists m2 e-if-true);
    (left v-false) → right (exists m3 e-if-false);
    (right (exists m1' m2Eval)) →
           right (exists (if m1' then m2 else m3) (e-if-guard m2Eval))
    }


-- -----------------------------------------------------------------------------
-- -------------------------------------------------------------- SAFETY THEOREM

-- ∅ ⊢ M : T   M ⇒* M'   M' ⇏        then M' is a value
safety : {m m' : Term} {t : Type}
       → HasType [] m t
       → m ⇒* m'
       → ¬ (∃ Term (λ m'' → m' ⇒ m''))
       → Value m'
safety mTypeT mEval ¬m'Eval with progress (type-preservation' mTypeT mEval)
... | left  m'Value = m'Value
... | right m'Eval = absurd (¬m'Eval m'Eval)

