From NAT Require Import Peanos_axioms.
From NAT Require Import Tutorial_World.
From NAT Require Import Addition_World.

Section Function_World. 

(*In this world we are going to learn how to reason about functions.*)

(*To begin, we start with a mysterious function, that takes some element p from P, and returns some element of Q. 
The naming convention p_then_q is probably totally coincidental, and has been mistakenly left in by the editor. It would be crazy to use the theory of functions for the theory of propositions, and if it were not, then I would not try and save the surprise from being spoiled. *)
Proposition p_then_q (P Q : Type)(p : P) (h : P -> Q): Q.
Proof.
    (*Now let us look at the first proof, using the exact tactic. 
    This does exactly (*sound of drums rolling down a flight of stairs and uproarious laughter*) what you would suspect. Since p has Type P, and h has Type P -> Q, then h p has Type Q, and it was our objective to construct something of Type Q! So, in some sense we have an object that is exactly, what we are looking for, and so we are done.*)
    exact (h p).
Qed.
(*Now, this is surely the slickest proof in this case, but there are other ways as well, which may be more confortable in some cases. Let us see one now.*)
Proposition p_then_q' (P Q : Type)(p : P) (h : P -> Q): Q.
Proof.
    (*Now, instead of using exact right away, instead we will use the apply tactic.
    Essentially what this does is say `if I know that I have a function from P to Q, then in order to show there is a member of q, it is sufficient to show that there is a member of P. Thus, the goal is altered to showing that a member of P exists. *)
    apply h.
    (*Now we show easily that such a member exists with the exact tactic.*)
    exact p.
Qed.

(*Now we will do something a little strange. We will show that there is a function from the naturals to the naturals.*)
(*In fact, there are many functions from the naturals to the naturals, in fact there are even more than the naturals themselves. So this should be easy. Let us choose the function x.*)
Proposition nat_function : nat -> nat.
Proof.
    (*Here we say that x is some natural number*)
    intro x.
    (*and hey we could just hand this value back, and it will still be a natural number.*)
    exact x.
    (*And now Coq is quite happy with that.*)
Qed.

(*This is an excersise designed to challenge your ability to use the exact and apply functions. If you are having trouble, there is a little help located in hint.txt*)
Proposition function_maze (P Q R S T U: Type)
(p : P)
(h : P -> Q)
(i : Q -> R)
(j : Q -> T)
(k : S -> T)
(l : T -> U)
: U.
Proof.
    exact (l (j (h (p)))).
Qed.

(*If you think of this in terms of functions, then this proposition essentially wants to know that there is a function that takes an element of P, and returns a function that takes an element of Q and returns and element of P. Well, you may say that sounds impossible, and to that I would respond `Thats not my problem' and then I would answer my un-ringing phone, and ignore you. On the other hand, I have secretly given you a very doable problem, start with some intros! *)
Proposition loop_function (P Q : Type) : P -> (Q -> P).
Proof.
    intros h1 h2. exact h1.
Qed.
(*This is another one designed to be a challenge.*)
Proposition function_jumble (P Q R : Type) : (P -> (Q -> R)) -> ((P -> Q)->(P -> R)).
Proof.
    intros h1 h2 h3.
    apply h1. exact h3.
    apply h2. exact h3.
Qed.

(*This code defines the empty Type, which will remain mysterious for a while. I mean to you, I know what it does.*)
Inductive empty : Type :=.

(*These naming conventionsal are surely getting out of hand. It almost sounds like I am not talking about functions at all. But that notion is rather fanciful. So let us discuss that function interpretation. That is, we wish to find a function that takes in a function from P to Q, and returns a function from the collection of functions from Q to the empty type to the collection of function from P to the empty type. Got it? Great! Now, prove it.*)
Proposition transitive_falsity (P Q : Type) : (P -> Q) -> ((Q -> empty)->(P -> empty)).
Proof.
    intros h1 h2 h3.
    apply h2.
    apply h1.
    exact h3.
Qed.
End Function_World.