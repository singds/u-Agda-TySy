open import basics

-- Language types
data Type : Set where
  Bool     : Type
  Nat      : Type
  Tarrow : Type → Type → Type

-- Language terms
data Term : Set where
  true                  : Term
  false                 : Term
  num                 : ℕ → Term                                    -- number
  var                   : ℕ → Term                                    -- variable
  _+ₙ_                 : Term → Term → Term                  -- sum between natural numbers
  if_then_else_    :  Term → Term → Term → Term     -- if e1 then e1 else e3
  _app_               : Term → Term → Term                 -- function application
  fun                   : ℕ → Type → Term → Term           -- labda abstraction


-- Get the free vriables of a term
fv : Term → List {ℕ}
fv true          = []
fv false         = []
fv (num x)       = []
fv (var x)       = x ∷ []
fv (m1 +ₙ m2)  = (fv m1) ++ (fv m2)
fv (if e1 then  e2 else  e3) = ((fv e1) ++ (fv e2)) ++ (fv e3)
fv (e1 app  e2)   = (fv e1) ++ (fv e2)
fv (fun x t e)   = (fv e) remove x 

data Env : Set

Dom : Env → List {ℕ}

data Env where
  []Env : Env
  addEnv : (x : ℕ) (t : Type) (Γ : Env) → ¬ (x ∈ (Dom Γ)) → Env

Dom []Env = []
Dom (addEnv x t Γ p) = x ∷ (Dom Γ)


-- Proposition: the provided environment contains the binding from the provided variable to the provided type.
-- m-first = match the first
-- m-tail  = match the tail
data EnvContains : ℕ → Type → Env → Set where
  m-first : (x : ℕ) (t : Type) (Γ : Env) (p : ¬ (x ∈ (Dom Γ))) → EnvContains x t (addEnv x t Γ p)
  m-tail  : (x : ℕ) (t : Type) (Γ : Env) (y : ℕ) (ty : Type) (p : ¬ (y ∈ (Dom Γ))) → EnvContains x t Γ → EnvContains x t (addEnv y ty Γ p)


{-# TERMINATING #-}
-- Substitution
-- occurences of the variable x are substituted with the term m in term t, producing a new term  
subst : ℕ → Term → Term → Term
subst x m true                                 = true
subst x m false                                = false
subst x m (num n)                           = num n
subst x m (var y) with x ≡? y
... | left p = m           -- case x equals y
... | right p = var y    -- case x not equals y
subst x m (e1 +ₙ e2)                      = (subst x m e1) +ₙ (subst x m e2)
subst x m (if e1 then e2 else e3)    = if (subst x m e1) then (subst x m e2) else  (subst x m e3)
subst x m (e1 app e2)                     = (subst x m e1) app (subst x m e2)
subst x m (fun y t e)                        = fun z t (subst x m (subst y (var z) e)) where
  z = succ ( max (getMax (fv m)) (getMax (fv e)) )


-- Typing rules
-- HasType is the set that contains the proofs that the term M has the type T in the environment E
--             E      M       T        E = environment   M = term   T = type
data HasType : Env → Term → Type → Set where
  t-true  : {Γ : Env} → HasType Γ true Bool
  t-false : {Γ : Env} → HasType Γ false Bool
  t-num   : {Γ : Env} (n : ℕ) → HasType Γ (num n) Nat
  t-sum   : {Γ : Env} {n1 n2 : Term}
            (p1 : HasType Γ n1 Nat) (p2 : HasType Γ n2 Nat) → HasType Γ (n1 +ₙ n2) Nat
  t-if    : {Γ : Env} {e1 e2 e3 : Term} {t : Type}
            (p1 : HasType Γ e1 Bool) (p2 : HasType Γ e2 t) (p3 : HasType Γ e3 t) → HasType Γ (if e1 then e2 else e3) t
  t-app   : {Γ : Env} {e1 e2 : Term} {t1 t2 : Type}
            (p1 : HasType Γ e1 (Tarrow t1 t2)) (p2 : HasType Γ e2 t1) → HasType Γ (e1 app e2) t2
  t-fun   : {Γ : Env} {x : ℕ} {t1 t2 : Type} {e1 : Term} (z : ℕ) → (z∉Γ : ¬ (z ∈ (Dom Γ))) → ¬ (z ∈ (fv e1)) →
            (p : HasType (addEnv z t1 Γ z∉Γ) (subst x (var z) e1) t2) → HasType Γ (fun x t1 e1) (Tarrow t1 t2)
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
is-value (m +ₙ m₁)   = right (λ ())
is-value (if m then m₁ else m₂)  = right (λ ())
is-value (m app m₁)    = right (λ ())
is-value (fun x t m)   = left (v-fun x t m)

-- Evaluation in a single step
data _⇒_ : Term → Term → Set where
  e-sum-l    : (m1 m1' m2 : Term) (pl : m1 ⇒ m1') → (m1 +ₙ m2) ⇒ (m1' +ₙ m2)
  e-sum-r    : (n1 : ℕ) (m2 m2' : Term) (pr : m2 ⇒ m2') → ((num n1) +ₙ m2) ⇒  ((num n1) +ₙ m2')
  e-sum      : (n1 n2 : ℕ) → ((num n1) +ₙ  (num n2)) ⇒ (num (n1 + n2))
  e-if-guard : (m1 m1' m2 m3 : Term) (p1 : m1 ⇒ m1') → (if m1 then m2 else m3) ⇒ (if m1' then m2 else m3)
  e-if-true  : (m2 m3 : Term) → (if true then m2 else m3) ⇒ m2
  e-if-false : (m2 m3 : Term) → (if false then m2 else m3) ⇒ m3
  -- beta reduction
  -- how can i say that an element is not in a list ?
  e-beta     : (x : ℕ) (t : Type) (e1 v2 : Term) (pv : Value v2) → ((fun x t e1) app v2) ⇒ (subst x v2 e1)
  e-app1     : (m1 m1' m2 : Term) (p1 :  m1 ⇒ m1') → (m1 app m2) ⇒ (m1' app m2)
  e-app2     : (v1 m2 m2' : Term) (p1 : Value v1) (p1 : m2 ⇒ m2') → (v1 app m2) ⇒ (v1 app m2')

-- Evaluation in multiple steps
-- reflexive and transitive closure
data _⇒*_ : Term → Term → Set where
  e-refl       : (e1 : Term) → e1 ⇒* e1                                                   -- reflexivity
  e-trans    : (e1 e2 e3 : Term) → e1 ⇒* e2 → e2 ⇒* e3 → e1 ⇒* e3   -- transitivity



-- INVERTION LEMMAS
-- invertion lemma for bool terms 
lemma-inversion-true : {Γ : Env} {t : Type} → HasType Γ true t → t ≡ Bool
lemma-inversion-true t-true = refl

lemma-inversion-false : {Γ : Env} {t : Type} → HasType Γ false t → t ≡ Bool
lemma-inversion-false t-false = refl

-- invertion lemma for sum term 
lemma-inversion-nat : {Γ : Env} {m1 m2 : Term} {t : Type} → HasType Γ (m1 +ₙ m2) t → t ≡ Nat
lemma-inversion-nat (t-sum p1 p2) = refl

lemma-inversion-nat-m1 : {Γ : Env} {m1 m2 : Term} {t : Type} → HasType Γ (m1 +ₙ m2) t → HasType Γ m1 Nat
lemma-inversion-nat-m1 (t-sum p1 p2) = p1

lemma-inversion-nat-m2 : {Γ : Env} {m1 m2 : Term} {t : Type} → HasType Γ (m1 +ₙ m2) t → HasType Γ m2 Nat
lemma-inversion-nat-m2 (t-sum p1 p2) = p2

-- invertion lemma for if then else term
lemma-inversion-if-e1 : {Γ : Env} {e1 e2 e3 : Term} {t : Type} → HasType Γ (if e1 then e2 else e3) t → HasType Γ e1 Bool
lemma-inversion-if-e1 (t-if p1 p2 p3) = p1

lemma-inversion-if-e2 : {Γ : Env} {e1 e2 e3 : Term} {t : Type} → HasType Γ (if e1 then e2 else e3) t → HasType Γ e2 t
lemma-inversion-if-e2 (t-if p1 p2 p3) = p2

lemma-inversion-if-e3 : {Γ : Env} {e1 e2 e3 : Term} {t : Type} → HasType Γ (if e1 then e2 else e3) t → HasType Γ e3 t
lemma-inversion-if-e3 (t-if p1 p2 p3) = p3

-- invertion lemma for variable term
lemma-invertion-var : {Γ : Env} {x : ℕ} {t : Type} → HasType Γ (var x) t → EnvContains x t Γ
lemma-invertion-var (t-var p) = p     -- p is the proof that "Γ" contains "x"

lemma-invertion-app : {Γ : Env} {m1 m2 : Term} {t : Type} → HasType Γ (m1 app m2) t → ∃ Type (λ t1 → (HasType Γ m1 (Tarrow t1 t)) & (HasType Γ m2 t1))
lemma-invertion-app (t-app {Γ} {m1} {m2} {t1} {t2} p1 p2) = exists t1 (and p1 p2)

lemma-invertion-fun : {Γ : Env} {m : Term} {x : ℕ} {t1 t : Type} → HasType Γ (fun x t1 m) t → ∃ Type (λ t2 → (t ≡ (Tarrow t1 t2)) & HasType Γ m t2)
lemma-invertion-fun (t-fun {Γ} {x} {t1} {t2} {m} z z∉Γ z∉m p) = exists t2 (and refl {!!})


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
lemma-canon-arrow p1 (t-fun {Γ} {x} {t1} {t2} {e1} z z∉Γ p2 p3) = exists x (exists e1 refl)


-- PROGRESS THEOREM
progress : {m : Term} {t : Type} → HasType []Env m t → (Value m) ⊎ (∃ Term (λ m' → m ⇒ m'))

progress t-true = left v-true

progress t-false = left v-false

progress (t-num n) = left (v-num n)

progress (t-fun {Γ} {x} {t1} {t2} {e1} z p1 p2 p3) = left (v-fun x t1 e1)

progress (t-sum {Γ} {n1} {n2} n1HasTypeNat n2HasTypeNat) with is-value n1 | is-value n2
... | right n1NotValue | _ = right evTo -- n1 is not a value
    where
    n1ValueOrEval = progress n1HasTypeNat
    ∃n1' = ⊎-getB n1ValueOrEval n1NotValue
    
    get-evTo : (∃ Term (λ n1' → n1 ⇒ n1')) → ∃ Term (λ m → (n1 +ₙ n2) ⇒ m)
    get-evTo (exists n1' n1→n1') = exists (n1' +ₙ n2) (e-sum-l n1 n1' n2 n1→n1')

    evTo = get-evTo ∃n1'

... | left n1Value | right n2NotValue = right evTo
    where
    ∃x1 = lemma-canon-nat n1Value n1HasTypeNat

    n2ValueOrEval = progress n2HasTypeNat
    ∃n2' = ⊎-getB n2ValueOrEval n2NotValue
    
    get-evTo : (∃ ℕ (λ x1 → n1 ≡ num x1)) → (∃ Term (λ n2' → n2 ⇒ n2')) → ∃ Term (λ m → (n1 +ₙ n2) ⇒ m)
    get-evTo (exists x1 p1) (exists n2' p2) rewrite p1 = exists ((num x1) +ₙ n2')  (e-sum-r x1 n2 n2' p2)
    
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

    get-evTo : (∃ ℕ (λ x → (n1 ≡ (num x)))) → (∃ ℕ (λ x → (n2 ≡ (num x)))) → ∃ Term (λ m → (n1 +ₙ n2) ⇒ m)
    get-evTo (exists x1 p1) (exists x2 p2) rewrite p1 | p2 = exists (num (x1 + x2)) (e-sum x1 x2)

    evTo = get-evTo n1≡num n2≡num


progress (t-if {[]Env} {e1} {e2} {e3} e1HasTypeBool p2 p3) with is-value e1
... | left e1Value = right evTo
    where
    e1TrueOrFalse = lemma-canon-bool e1Value e1HasTypeBool
    
    get-evTo : (g : Term) → (g ≡ true) ⊎ (g ≡ false) → ∃ Term (λ m → (if g then e2 else e3) ⇒ m)
    get-evTo g (left gEqTrue) rewrite gEqTrue = exists e2 (e-if-true e2 e3)
    get-evTo g (right gEqFalse) rewrite gEqFalse = exists e3 (e-if-false e2 e3)

    evTo = get-evTo e1 e1TrueOrFalse

... | right e1NotValue = right evTo
    where
    e1ValueOrEval = progress e1HasTypeBool
    ∃e1' = ⊎-getB e1ValueOrEval e1NotValue
    
    get-evTo : ∃ Term (λ e1' → e1 ⇒ e1') → ∃ Term (λ m → (if e1 then e2 else e3) ⇒ m)
    get-evTo (exists e1' p1) = exists (if e1' then e2 else e3) (e-if-guard e1 e1' e2 e3 p1)

    evTo = get-evTo ∃e1'

progress (t-app {[]Env} {e1} {e2} {t1} {_} e1HasTypeT1T2 e2HasTypeT1) with is-value e1 | is-value e2
... | right e1NotValue | _ = right evTo
    where
    e1ValueOrEval = progress e1HasTypeT1T2
    ∃e1' = ⊎-getB e1ValueOrEval e1NotValue

    get-evTo : ∃ Term (λ e1' → e1 ⇒ e1') → ∃ Term (λ m → (e1 app e2) ⇒ m)
    get-evTo (exists e1' p) = exists (e1' app e2) (e-app1 e1 e1' e2 p)

    evTo = get-evTo ∃e1'
    
... | left e1Value | right e2NotValue = right evTo
    where
    e2ValueOrEval = progress e2HasTypeT1
    ∃e2' = ⊎-getB e2ValueOrEval e2NotValue

    get-evTo : ∃ Term (λ e2' → e2 ⇒ e2') → ∃ Term (λ m → (e1 app e2) ⇒ m)
    get-evTo (exists e2' e2→e2') = exists (e1 app e2') (e-app2 e1 e2 e2' e1Value e2→e2')

    evTo = get-evTo ∃e2'

... | left e1Value | left e2Value = right evTo
    where

    ∃e1≡Fun = lemma-canon-arrow e1Value e1HasTypeT1T2

    get-evTo : ∃ ℕ (λ x → (∃ Term (λ m1 → e1 ≡ (fun x t1 m1)))) → ∃ Term (λ m → (e1 app e2) ⇒ m)
    get-evTo (exists x (exists m1 e1≡Fun)) rewrite e1≡Fun = exists (subst x e2 m1) (e-beta x t1 m1 e2 e2Value)

    evTo = get-evTo ∃e1≡Fun

magic2 : (Γ : Env) (x : ℕ) (t : Type) → EnvContains x t Γ → x ∈ (Dom Γ)
magic2 (addEnv x t Γ p) x t (m-first x t Γ p) = in-head x (Dom Γ)
magic2 (addEnv y ty Γ p) x t (m-tail x t Γ y ty p p₁) = in-tail x y (Dom Γ) (magic2 Γ x t p₁)

magic1 : (Γ : Env) (x : ℕ) (t : Type) → ¬ (x ∈ (Dom Γ)) → ¬ (EnvContains x t Γ)
magic1 Γ x t p = λ p2 → p (magic2 Γ x t p2)

magic : {Γ : Env} {x : ℕ} {t1 t2 : Type} {p : ¬ (x ∈ (Dom Γ))} → EnvContains x t1 (addEnv x t2 Γ p) → t1 ≡ t2
magic (m-first x t Γ p) = refl
magic (m-tail x t Γ x ty p1 p2) = absurd ((magic1 Γ x t p1) p2)

magic3 : {x1 x2 : ℕ} {t1 t2 : Type} {Γ : Env} {p : ¬ (x2 ∈ (Dom Γ))} → EnvContains x1 t1 (addEnv x2 t2 Γ p) → x1 ≢ x2 → EnvContains x1 t1 Γ
magic3 (m-first x1 t1 Γ p1) p2 = absurd (p2 refl)
magic3 (m-tail x1 t1 Γ x2 t2 p1 p2) p3 = p2


unique-var-type : {Γ : Env} {x : ℕ} {t1 t2 : Type} → HasType Γ (var x) t1 → EnvContains x t2 Γ → t1 ≡ t2
unique-var-type = {!!}


magic5 : {Γ : Env} {x z : ℕ} {t1 t : Type} {m : Term} {p : ¬ (x ∈ (Dom Γ))}
            → HasType (addEnv x t1 Γ p) m t → (p2 : ¬ (z ∈ (Dom Γ))) → ¬ (z ∈ (fv m)) → HasType (addEnv z t1 Γ p2) (subst x (var z) m) t
            
magic5 t-true p2 p3 = t-true
magic5 t-false p2 p3 = t-false
magic5 (t-num n) p2 p3 = t-num n
magic5 {Γ} {x} {z} {t1} {t} {m} {p} (t-sum {_} {n1} {n2} p1 p4) p2 p3 = t-sum n1-nat n2-nat  where

  not-in-n1 : ¬ (z ∈ (fv n1))
  not-in-n1 = not-in-concat-not-in-first z (fv n1) (fv n2) p3

  not-in-n2 : ¬ (z ∈ (fv n2))
  not-in-n2 = not-in-concat-not-in-second z (fv n1) (fv n2) p3

  n1-nat : HasType (addEnv z t1 Γ p2) (subst x (var z) n1) Nat
  n1-nat = magic5 p1 p2 not-in-n1

  n2-nat : HasType (addEnv z t1 Γ p2) (subst x (var z) n2) Nat
  n2-nat = magic5 p4 p2 not-in-n2
  
magic5 (t-if p1 p4 p5) p2 p3 = {!!}
magic5 (t-app p1 p4) p2 p3 = {!!}
magic5 (t-fun z z∉Γ x p1) p2 p3 = {!!}
magic5 {Γ} {x} (t-var {_} {y} inEvn) p2 p3 with x ≡? y
magic5 {Γ} {x} {t1} {t} (t-var {addEnv x _ Γ _} {y} inEvn) p2 p3 | left p = {!!}
magic5 {Γ} {x} (t-var {addEnv x _ Γ _} {y} inEvn) p2 p3 | right p = {!!}





change-fun-var : {Γ : Env} {x z : ℕ} {t1 t : Type} {m : Term} → HasType Γ (fun x t1 m) t → ¬ (z ∈ (fv m)) → ¬ (z ∈ (Dom Γ)) → HasType Γ (fun z t1 (subst x (var z) m)) t
change-fun-var (t-fun x x∉Γ e1 p1) p2 = {!!}

substitution-lemma-fun-simple : {Γ : Env} {x z : ℕ} {T Tz S : Type} {M N : Term} {p : ¬ (x ∈ (Dom Γ))} → HasType (addEnv x S Γ p) (fun z Tz M) T → HasType Γ N S → x ≢ z → HasType Γ (fun z Tz (subst x M N)) T
substitution-lemma-fun-simple = {!!}

substitution-lemma : {Γ : Env} {x : ℕ} {t1 t2 : Type} {m1 m2 : Term} {p : ¬ (x ∈ (Dom Γ))} → HasType (addEnv x t2 Γ p) m1 t1 → HasType Γ m2 t2 → HasType Γ (subst x m2 m1) t1
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
substitution-lemma {Γ} {x} {t1} {t2} (t-var {Γ₁} {y} p1) m2T2 with x ≡? y
substitution-lemma {Γ} {x} {t1} {t2} (t-var {addEnv x t2 Γ _} {x} p1) m2T2 | left refl rewrite magic p1 = m2T2
... | right p = t-var (magic3 p1 (symm≢ p))
substitution-lemma {Γ} {x} {t1} {t2} {m1} {m2} {p}  (t-fun {addEnv x t2 Γ p} {y} {tf1} {tf2} {e1} z p1 p2 p3) m2T2 = substitution-lemma-fun-simple {!!} {!!} {!!} where

  z2 : ℕ
  z2 = succ (max (getMax (Dom )) (getMax (fv e1))) 

  z3 : ℕ
  z3 = {!!}

  fun-rename : HasType (addEnv x t2 Γ p) (fun y tf1 (subst y (var z3) e1)) (Tarrow tf1 tf2)
  fun-rename = change-fun-var (t-fun {addEnv x t2 Γ p} {y} {tf1} {tf2} {e1} z2 {!!} {!!} {!!}) {!!} {!!}


{-

-- refl is a proof tha x is equal to x
-- input :
--     a proof that an extended environment contains x
--     a proof that x is not the first element of the environment
-- output:
--     a proof that x is in the environment that is the original one without the first element
in-env-decompose : {Γ : Env} {x y : ℕ} {t1 t2 : Type} → EnvContains x t1 {!!} → x ≢ y → EnvContains x t1 Γ
in-env-decompose (m-first x t Γ) x≢x = absurd (x≢x refl)
in-env-decompose (m-tail y ty inΓ) x≢y = inΓ



-- the substitution lemma does not work if we don't force the variables in the env to be unique
-- x:T1,x:T2 



preservation : {Γ : Env} {m m' : Term} {t : Type} → HasType Γ m t → m ⇒ m' → HasType Γ m' t
preservation (t-sum m1Nat m2Nat) (e-sum-l m1 m1' m2 pe)          = t-sum (preservation m1Nat pe) m2Nat
preservation (t-sum m1Nat m2Nat) (e-sum-r n1 m2 m2' pe)          = t-sum m1Nat (preservation m2Nat pe)
preservation (t-sum m1Nat m2Nat) (e-sum n1 n2)                   = t-num (n1 + n2)
preservation (t-if e1Bool e2T e3T) (e-if-guard m1 m1' m2 m3 pe)  = t-if (preservation e1Bool pe) e2T e3T
preservation (t-if e1Bool e2T e3T) (e-if-true m2 m3)             = e2T
preservation (t-if e1Bool e2T e3T) (e-if-false m2 m3)            = e3T
preservation (t-app e1T1T2 e2T1) (e-beta x t e1 e2 p1)            = {!!} where
  
preservation (t-app e1T1T2 e2T1) (e-app1 m1 m1' m2 pe)           = t-app (preservation e1T1T2 pe) e2T1
preservation (t-app e1T1T2 e2T1) (e-app2 v1 m2 m2' p1 pe)        = t-app e1T1T2 (preservation e2T1 pe)


-}
