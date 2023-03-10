From NAT Require Import Peanos_axioms.
From NAT Require Import Tutorial_World.
From NAT Require Import Addition_World.
From NAT Require Import Function_World.
From NAT Require Import Multiplication_World.
From NAT Require Import Proposition_World.
From NAT Require Import Advanced_Proposition_World.
From NAT Require Import Advanced_Addition_World.

Section Advanced_Multiplication_World.


Proposition mul_pos (a b : nat) : a <> 0 -> b <> 0 -> a * b <> 0.
Proof.
    intros h1 h2 h3.
    induction a. apply h1. reflexivity.
(*DID NOT USE IHn VERY SUSPICUOUS*)
    rewrite mul_comm in h3.
    rewrite succ_dist in h3.
    rewrite commute in h3.
    apply (add_right_eq_zero) in h3.
    exact (h2 (h3)).
Qed.
(*Put some text here *)






Proposition eq_zero_or_eq_zero_of_mul_eq_zero (a b : nat)(h : a * b = 0): 
a = 0 \/ b = 0.
Proof.
    induction b.
    right. reflexivity.
    left.
    assert (S(b) <> 0).
    exact (zero_not_succ(b)).
    rewrite succ_dist in h.
    rewrite (add_right_eq_zero (a*b)(a)) in h.
    rewrite (zero_add) in h.
    exact h.
    exact h.
Qed.

Proposition mul_eq_zero_iff (a b : nat) : 
a * b = 0 <-> a = 0 \/ b = 0.
Proof.
    split.
    intro h.
    exact (eq_zero_or_eq_zero_of_mul_eq_zero (a)(b)(h)).
    intro h.
    case h.
    intro ha.
    rewrite ha. rewrite zero_mul. reflexivity.
    intro hb.
    rewrite hb. rewrite mul_zero. reflexivity.
Qed.

Proposition mul_left_cancel (a b c : nat) (ha : a <> 0) :
a * b = a * c -> b = c. 
Proof.
induction c.
    +rewrite mul_zero.
    intro h.
    apply mul_eq_zero_iff in h.
    case h.
    intro Ha. exfalso.
    exact (ha Ha).
    intro Hb. exact Hb.
    +intro h. 
    rewrite h in IHc.
Admitted.

End Advanced_Multiplication_World.