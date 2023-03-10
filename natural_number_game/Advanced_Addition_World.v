From NAT Require Import Peanos_axioms.
From NAT Require Import Tutorial_World.
From NAT Require Import Addition_World.
From NAT Require Import Function_World.
From NAT Require Import Proposition_World.
From NAT Require Import Advanced_Proposition_World.

Section Advanced_Addition_World.

Proposition succ_inj'' (a b : nat)(hs : S(a) = S(b)) : a = b.
Proof.
    apply succ_inj.
    exact hs.
Qed.

Proposition succ_succ_inj (a b : nat)(h : S (S a) = S (S b)): a = b.
Proof.
    apply succ_inj. apply succ_inj.
    exact h.
Qed.

Proposition succ_eq_succ_of_eq (a b : nat) :
a = b -> S a = S b.
Proof.
    intro h.
    rewrite h. 
    reflexivity.
Qed.

Proposition succ_eq_succ_iff (a b : nat) : 
S a = S b <-> a = b.
Proof.
    split.
    intro h. 
    exact (succ_inj (a)(b)(h)).
    exact (succ_eq_succ_of_eq (a)(b)).
Qed.

Proposition add_right_cancel (a t b : nat) : 
(a + t = b + t) -> a = b.
Proof.
    induction t.
    rewrite add_zero. rewrite add_zero. intro h. exact h.
    intro h.
    rewrite succ_add in h. rewrite succ_add in h.
    apply IHt.
    apply succ_eq_succ_iff.
    exact h.
Qed.

Proposition add_left_cancel (t a b : nat):
t + a = t + b -> a = b. 
Proof.
    intro h.
    rewrite commute in h. 
    rewrite (commute (t)(b)) in h.
    apply add_right_cancel in h. 
    exact h.
Qed.

Proposition add_right_cancel_iff (t a b : nat) :
a + t = b + t <-> a = b.
Proof.
    split.
    exact (add_right_cancel (a)(t)(b)).
    intro h.
    induction t.
    rewrite add_zero. rewrite add_zero. exact h.
    rewrite succ_add. rewrite succ_add.
    apply <- (succ_eq_succ_iff).
    exact IHt. 
Qed.

Proposition eq_zero_of_add_right_eq_self (a b : nat):
a + b = a -> b = 0.
Proof.
    intro h.
    rewrite <- (add_zero) in h.
    rewrite commute in h. rewrite (commute (a)(0)) in h.    apply add_right_cancel_iff in h.
    exact h.
Qed.

Proposition succ_ne_zero (a : nat) : ~(S a = 0).
Proof.
    exact (zero_not_succ (a)).
Qed.

Proposition add_left_eq_zero (a b : nat) (H : a + b = 0) :
b = 0.
Proof.
    induction b.
    reflexivity.

    rewrite (succ_add) in H.
    exfalso.
    assert (~(S (a + b) = 0)).
    exact (succ_ne_zero (a + b)).
    exact (H0 (H)).
Qed.

Proposition add_right_eq_zero (a b : nat) : 
a + b = 0 -> a = 0.
Proof.
    intro h.
    rewrite commute in h.
    exact (add_left_eq_zero (b)(a)(h)).
Qed.

Proposition add_one_eq_succ (a : nat) : a + 1 = S a.
Proof.
    rewrite commute.
    reflexivity.
Qed.

Proposition ne_succ_self (n : nat) : ~(n = S n).
Proof.
    induction n.
    intro h.
    symmetry in h.
    apply (succ_ne_zero (0))in h.
    exact h.
    intro h.
    rewrite <-(succ_inj (n)(S n)) in h.
    exact (IHn (h)).
    exact h.
Qed.
End Advanced_Addition_World.