/-!
# Homework #3

Near final DRAFT. 

## Overview and Rules

The purpose of this homework is to strengthen your
understanding of function composition and of enumerated
and product data types. 

The collaboration rule for this homework is that
you may *not* collaborate. You can ask friends and
colleagues to help you understand material in the
class notes, but you may not discuss any aspect
of this homework itself with anyone other than one
of the instructors or TAs. Why? Because *you* need
to learn this material to pass the exam to come.
-/

/-!
## Problem #1

Define a function of the following polymorphic type:
{α β γ : Type} → (β → γ) → (α → β) → (α → γ). Call it
*funkom*. After the implicit type arguments it should
take two function arguments and return a function as
a result. 
-/

-- Answer below
def funkom {α β γ : Type} (f : β → γ)(g : α → β) :α → γ
| x => f (g x)
/-! 
## Problem #2

Define a function of the following polymorphic type:
{α β : Type} → (a : α) → (b : β) → α × β. Call it mkop.
-/

-- Answer below
def mkop {α β : Type} (a:α) (b : β) : α × β := (a,b)
/-! 
## Problem #3

Define a function of the following polymorphic type:
{α β : Type} → α × β → α. Call it op_left.
-/

-- Answer below

def op_left {α β : Type} :α × β → α
| (a,_) => a


/-! 
## Problem #4

Define a function of the following polymorphic type:
{α β : Type} → α × β → β. Call it op_right.
-/

-- Answer below
def op_right {α β : Type} : α × β → β
| (_, b) => b


/-! 
## Problem #5

Define a data type called *Day*, the values of which
are the names of the seven days of the week: *sunday,
monday,* etc. 

Some days are work days and some days are play
days. Define a data type, *kind*, with two values,
*work* and *play*.

Now define a function, *day2kind*, that takes a *day*
as an argument and returns the *kind* of day it is as
a result. Specify *day2kind* so that weekdays (monday
through friday) are *work* days and weekend days are
*play* days.

Next, define a data type, *reward*, with two values,
*money* and *health*.

Now define a function, *kind2reward*, from *kind* to 
*reward* where *reward work* is *money* and *reward play* 
is *health*.

Finally, use your *funkom* function to produce a new
function that takes a day and returns the corresponding
reward. Call it *day2reward*.

Include test cases using #reduce to show that the reward
from each weekday is *money* and the reward from a weekend
day is *health*.
-/
inductive Day
| Monday
| Tuesday
| Wednesday
| Thursday
| Friday
| Saturday
| Sunday

inductive kind
| work
| play

def day2kind (d: Day) : kind :=
match d with
| Day.Monday => kind.work
| Day.Tuesday => kind.work
| Day.Wednesday => kind.work
| Day.Thursday => kind.work
| Day.Friday => kind.work
| Day.Saturday => kind.play
| Day.Sunday => kind.play

inductive reward
| money
| health

def kind2reward (k : kind) : reward :=
match k with
| kind.work => reward.money
| kind.play => reward.health

def day2reward : Day → reward :=
funkom kind2reward day2kind

#reduce day2reward Day.Monday   -- Output: money
#reduce day2reward Day.Tuesday  -- Output: money
#reduce day2reward Day.Wednesday -- Output: money
#reduce day2reward Day.Thursday  -- Output: money
#reduce day2reward Day.Friday    -- Output: money
#reduce day2reward Day.Saturday  -- Output: health
#reduce day2reward Day.Sunday    -- Output: health
/-!
## Problem #6

### A. 
Consider the outputs of the following #check commands. 
-/

#check Nat × Nat × Nat
#check Nat × (Nat × Nat)
#check (Nat × Nat) × Nat

/-!
Is × left associative or right associative? Briefly explain
how you reached your answer.

Answer here: 
It is left associative because putting the brackers on the left
makes it nat x nat x nat which is the same as the first example,
but putting brackets on the right makes a nat to a pair of nats. 
So it is left associative because it looks at the left ones first. 

### B.
Define a function, *triple*, of the following type:
{ α β γ : Type } → α → β → γ → (α × β × γ)  
-/

-- Here:
def triple { α β γ : Type } (a:α)  (b:β ) (c:γ) : α × β × γ :=
(a ,b ,c)
/-!
### C.
Define three functions, call them *first*, *second*, 
and *third*, each of which takes any such triple as
an argument and that returns, respectively, its first,
second, or third elements.
-/

-- Here:
def first { α β γ : Type } (a : α × β × γ  ) : α :=
match a with
| (a,_,_) => a

def second { α β γ : Type } (a : α × β × γ  ) : β :=
match a with
| (_,a,_) => a

def third { α β γ : Type } (a : α × β × γ  ) : γ :=
match a with
| (_,_,a) => a

/-!
### D.
Write three test cases using #eval to show that when 
you apply each of these "elimination" functions to a
triple (that you can make up) it returns the correct
element of that triple.  
-/

-- Here:
def triple2 : String × Nat × String := ("hello",4,"world")
#eval first triple2
#eval second triple2
#eval third triple2
/-!
### E.
Use #check to check the type of a term. that you make 
up, of type (Nat × String) × Bool. The challenge here
is to write a term of that type. 
-/

#check ((4,"hello"),true)



/- 
I used chatgpt for this assignment. All I used it for was how to create
almost like a truth table to match the values, so it just gave meat function match blank with.
Other that that not super helpful. Asking to clarify and go into more detail on things like how does funkom
work or whats wrong with my implitation of funkom was not helpful. 
-/