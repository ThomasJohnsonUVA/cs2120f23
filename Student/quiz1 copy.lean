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
