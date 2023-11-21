/-!
#Curry-Howard Correspondence
-/

/-!
## Empty ==> False
-/
#check Empty
inductive Chaos : Type

def from_empty (e : Empty) : Chaos := nomatch e

#check False
-- inductive False: Prop

def from_false {P : Prop} (p : False) : P := False.elim p

def from_false_true_is_false(p : False) : True = False := False.elim p


/-!
Unit ==> True
-/

#check Unit
-- inductive PUnit : Sort u where
-- | united : Punit
#check True
-- inductive True : Prop where
-- | intro: True

#check True.intro

-- no elmination rule

def proof_of_true : True := True.intro

def false_implies_true : False → True := λ f => False.elim f

/-!
Prod ==> And
-/

#check Prod

/-
structure Prod(A : Type u) (B: Type V) where
  fst : a
  snd : b
-/

#check And
/-!
structure And (a b : Prop) : Prop where
  intro ::
  left: a
  right : b
-/


inductive Birds_chirping : Prop
| yep
| boo

inductive Sky_blue : Prop
| yep

#check (And Birds_chirping Sky_blue )

theorem both_and: And Birds_chirping Sky_blue := And.intro Birds_chirping.boo Sky_blue.yep

/-!
Proof Irrevelance
-/

namespace cs2120f23
inductive bool : Type
| true
| False

theorem proof_equal : Birds_chirping.boo = Birds_chirping.yep := by trivial

-- In Pop all proofs are equivalent
-- Choice of values in Prop can't influence computations


/-!
Sum ==> Or
-/

#check Sum

/-
inductive Sum (a : Type u) (B :Type v) where
  | inl (val : a) : Sum a B
  | inr (val: B) : Sum a B
-/

#check Or

/-
inductive Or (a b: Prop) : Prop where
| inl (h : a) : Or a b
| inr (h:b) : Or a b
-/

theorem one_or_other: Or Birds_chirping Sky_blue := Or.inl Birds_chirping.yep
theorem one_or_other': Or Birds_chirping Sky_blue := Or.inr Sky_blue.yep

example : Or Birds_chirping (0=1) := Or.inl Birds_chirping.yep
example : (0=2) ∨ (0=1) := _

theorem or_comm {P Q : Prop} : P ∨ Q → Q ∨ P :=
λ d =>
match d with
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q


/-!
Not (no)
-/

def no (a : Type) := a → Empty
#check Not
-- Not P is to defined to be P → False

example : no Chaos := λ (c :  Chaos) => nomatch c

inductive Raining: Prop

example : ¬ Raining := λ (r: Raining) => nomatch r



/-!
Next Day
-/


example : ¬ False :=
λ f => False.elim f

example (P : Prop) : ¬(P ∧ ¬P) := -- P ∧ ¬P → False
λ (⟨p, np ⟩) => np p

example (P Q R: Prop) : ( P → Q) → (Q →R) → (P → R) :=
fun pq qr => fun p => qr (pq p)

/-
a proof of not p if giving a function gives you a proof of false
-/

example ( a b y: Type) : (a → b) → (b → y) → (a → y) :=
λ ab bc => λ a => (bc (ab a))
example  ( P Q R : Prop) : P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)
| Or.inl p => ⟨ Or.inl p, Or.inl p⟩
| Or.inr ⟨q,r⟩ => ⟨ Or.inr q, Or.inr r ⟩

axiom em : ∀ (P : Prop), P ∨ ¬ P

example (A B : Prop) : ¬(A ∧ B) → ¬A ∨ ¬B
| nab => Or.inl _

example (A B : Prop) :¬A ∨ ¬B → ¬(A ∧ B)
| Or.inl na => λ ⟨ a, _⟩ => na a
| Or.inr nb => λ ⟨ _, b⟩ => nb b

example: X ∨ ¬X := em X
