From NAT Require Import Peanos_axioms.
From NAT Require Import Tutorial_World.
From NAT Require Import Addition_World.
From NAT Require Import Function_World.

Section Proposition_World.
(*Next lets talk about propositions, and how to use everything we build for functions for them. Recall in Function world we said p : P, meant that p was an element of P. On the other hand it turns our we could also have said that p : P is a proof of proposition P. In addition, before we said that P -> Q, was a function from P to Q. Now we will say P implies Q. *)
(*Hey, wait a minute, didn't we alrready prove all of these?*)
Proposition if_p_then_q (P Q : Prop) (p : P) (h : P -> Q):Q. 
Proof.
    apply h.
    exact p.
Qed.

Proposition if_p_then_q' (P Q : Prop) (p : P) (h : P -> Q):Q. 
Proof.
    exact (h p).
Qed.

Proposition imp_self (P : Prop) : P -> P.
Proof.
    intro h.
    exact h.
Qed.

Proposition maze (P Q R S T U : Prop) 
(p : P)
(h : P -> Q)
(i : Q -> R)
(j : Q -> T)
(k : S -> T)
(l : T -> U)
: U.
Proof.
    apply l.
    apply j.
    apply h.
    exact p. 
Qed.

Proposition p_then_q_then_p (P Q : Prop): P -> (Q -> P).
Proof.
    intro h1.
    intro h2.
    exact h1.
Qed.

Proposition jumble (P Q R : Prop) : (P -> (Q -> R)) -> ((P -> Q)->(P -> R)).
Proof.
    intros h1 h2 h3.
    apply h1. exact h3.
    apply h2. exact h3.
Qed.

Proposition imp_trans (P Q R : Prop) : (P -> Q) -> ((Q -> R) -> (P -> R)).
Proof.
    intros h1 h2 h3.
    exact (h2 (h1 (h3))).
Qed.
(*Now that you are done reproving everything you may set aside your reinvented wheel and look at this proposition that you also already proved. Recall from Function world that you proved the existance of some truly unruly functions, on the other hand, with our new interpretation it is clear why! We were showing that the contrapositive is a valid method of proof! Do so again!*)
Proposition contrapositive (P Q : Prop) : (P -> Q) -> (~Q -> ~P). 
Proof.
    intros h1 h2 h3.
    assert Q.
    exact (h1 (h3)).
    exact (h2 (H)).
Qed.

(*REVISIT IF 9 IS INSTRUCTIVE OR JUST DIFFICULT*)
End Proposition_World.