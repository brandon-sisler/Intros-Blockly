From NAT Require Import Peanos_axioms.
From NAT Require Import Tutorial_World.
From NAT Require Import Addition_World.
From NAT Require Import Multiplication_World.
From NAT Require Import Power_World.
From NAT Require Import Function_World.
From NAT Require Import Proposition_World.
From NAT Require Import Advanced_Proposition_World.
From NAT Require Import Advanced_Addition_World.




Section Inequality_World.

(*Now for our final section, Inequality World!*)
(*Up until now we have been working with strict equality, which is great, but a lot of the things we want to do with the naturals will require a notion of order. 
Just like in Power World, we should consider what it even means for a <= b. Initially, these are just random meaninless symbols and we can derive nothing from them, since our premise is not clear in the first place!
The best place to start is to realise that for a < b, there should be some `space` between them. That is b should be some distance away from a. From this idea we easily see how to define less than or equal to. *)
Definition less_than_or_equal (a b : nat):= 
    exists c : nat, b = a + c.

Notation "a <= b" := (less_than_or_equal (a)(b)).

(*Now let us just restate the definition in a way that will be more useable later, and of course show that it is a true iff statement.*)
Proposition le_iff_exists_add (a b : nat) : 
a <= b <-> exists c : nat, b = a + c.
Proof.
    split.
    intro h. exact (h).
    intro h. exact (h).
Qed.

Proposition one_add_le_self (x : nat) : x <= 1 + x.
Proof.
    apply le_iff_exists_add.
    exists 1.
    rewrite commute.
    reflexivity.
Qed.
(*If you find yourself trying some crazy proof method, take a step back and see if it cannot be done simpler.*)
Proposition le_refl (x : nat) : x <= x.
Proof. 
    apply le_iff_exists_add.
    exists 0.
    rewrite add_zero.
    reflexivity.
Qed.
(*There are a few good ways to do this, both with previous results and just with tactics.*)
Proposition le_succ (a b : nat) : a <= b -> a <= S b.
Proof.
    intro h.
    apply le_iff_exists_add.
    assert (exists c : nat, b = a + c). exact h.
    destruct H.
    exists (x + 1). 
    rewrite add_one. rewrite H. rewrite add_assoc.
    reflexivity.
Qed.
(*This is one of those theorems that you must prove in order to satisfy a lot of base cases and to make sure your definition is functioning in the way that you inteded it to.*)
Proposition zero_le (a : nat) : 0 <= a.
Proof.
    apply le_iff_exists_add.
    exists a.
    rewrite zero_add.
    reflexivity.
Qed.

Proposition le_trans (a b c : nat)(hab : a <= b)(hbc : b <= c): a <= c.
Proof.
     apply le_iff_exists_add.
     assert (exists c0 : nat, b = a + c0). exact hab.
     assert (exists c0 : nat, c = b + c0). exact hbc.
     destruct H. destruct H0.
     exists (x + x0).
     rewrite H0. rewrite H. rewrite add_assoc. reflexivity.
Qed.

Lemma left_cancel (a b c: nat): a + b= a + c -> b = c.
Proof.
    intro h.
    rewrite (commute (a)(b)) in h. rewrite (commute (a)(c)) in h.
    apply add_right_cancel_iff in h. exact h.
Qed.

Proposition le_antisymm (a b : nat) (hab : a <= b)(hba : b <= a): a = b.
Proof.
    assert (exists c : nat, b = a + c). exact hab.
    assert (exists c : nat, a = b + c). exact hba.
    destruct H. destruct H0.
    rewrite H in H0.
    rewrite <- (add_zero (a)) in H0.
    rewrite add_assoc in H0. rewrite add_assoc in H0.
    apply (left_cancel (a)(0)((0 + x + x0))) in H0.
    rewrite zero_add in H0. 
    symmetry in H0.
    apply add_right_eq_zero in H0.
    rewrite H0 in H.
    rewrite add_zero in H.
    symmetry in H.
    exact H.
Qed.

Proposition le_zero (a : nat)(h :  a <= 0) : a = 0.
Proof.
    assert (0 <= a).
    apply le_iff_exists_add.
    exists a. rewrite zero_add. reflexivity.
    exact (le_antisymm (a)(0)(h)(H)).
Qed.

Proposition succ_le_succ (a b : nat)(h : a <= b) : 
S a <= S b.
Proof.
    apply le_iff_exists_add.
    assert (exists c : nat, b = a + c). exact h.
    destruct H.
    exists x.
    rewrite add_succ. 
    rewrite H. reflexivity.
Qed.

Lemma n_less_than_succ (n : nat): n <= S n.
Proof.
    apply le_iff_exists_add.
    exists 1. rewrite add_one. reflexivity. 
Qed.
Proposition le_total (a b : nat) : a <= b \/ b <=a.
Proof.
    elim b.
    right. exact (zero_le (a) ).
    intros h1 h2. destruct h2.
    left. 
    assert  (exists c : nat, h1 = a + c). exact H.
    destruct H0.
    apply le_iff_exists_add. exists (x+1). 
    rewrite add_one. rewrite H0. rewrite add_assoc.
    reflexivity.
    assert (exists c, a = h1 + c). exact H.
    destruct H0. induction x. rewrite add_zero in H0.
    left. rewrite H0. exact (n_less_than_succ (h1)).
    right.
    apply le_iff_exists_add.
    exists x.
    rewrite add_succ. rewrite succ_add in H0.
    exact H0.
Qed.

Proposition add_le_add_right (a b : nat) :
a <= b -> forall t, (a + t) <= (b + t).
Proof.
    intros h ht.
    assert (exists c, b = a + c). exact h.
    destruct H.
    apply le_iff_exists_add.
    exists (x).
    rewrite H. rewrite add_assoc. rewrite (commute (x)(ht)).
    rewrite add_assoc. reflexivity.
Qed.

Proposition le_of_succ_le_succ (a b : nat) : 
S a <= S b -> a <= b.
Proof.
    intro h.
    assert (exists c, S b = S a + c ). exact h.
    destruct H. 
    rewrite add_one in H.
    rewrite (add_one (a)) in H.
    rewrite commute in H. rewrite (commute (a)(1)) in H.
    rewrite add_assoc in H.
    apply add_left_cancel in H.
    apply le_iff_exists_add.
    exists x. exact H.
Qed.

Proposition not_succ_le_self (a : nat) : ~(S a <= a).
Proof.
    intro h.
    assert (exists c, a = S a + c). exact h.
    destruct H. rewrite add_one in H. rewrite add_assoc in H.
    symmetry in H.
    rewrite <- (add_zero) in H.
    apply (add_left_cancel) in H.
    rewrite commute in H.
    rewrite <- (add_one) in H.
    apply zero_not_succ in H. exact H.
Qed.

Proposition add_le_add_left (a b : nat) (h : a <= b) (t :nat):
t +a <= t + b.
Proof.
    assert (exists c, b = a + c). exact h. destruct H.
    apply le_iff_exists_add. exists x.
    rewrite H. rewrite add_assoc. reflexivity.
Qed.

Proposition lt_aux_one (a b : nat) : 
a <= b /\ ~(b <= a) -> S a <= b.
Proof.
    intro h.
    destruct h as [hab hba].
    assert (exists c, b = a + c). exact hab. destruct H.
    induction x. rewrite add_zero in H. symmetry in H.
    rewrite <- (add_zero) in H.
    assert (b <= a). exists 0. exact H. 
    exfalso. exact (hba (H0)).
    apply le_iff_exists_add.
    exists x. rewrite add_succ.
    rewrite succ_add in H.
    exact H.
Qed.

Proposition lt_aux_two (a b : nat):
S a <= b -> a <= b /\ ~(b <= a).
Proof.
    intro h.
    split.
    assert (exists c, b = S a + c). exact h. destruct H.
    apply le_iff_exists_add.
    exists (1 + x).
    rewrite add_one in H. rewrite add_assoc in H.
    exact H.

    assert (exists c, b = S a + c). exact h. destruct H.
    intro hba. 
    assert (exists c, a = b + c). exact hba. destruct H0.
    rewrite H0 in H. 
    clear h. clear hba. clear H0.
    rewrite <- succ_add in H.
    rewrite add_assoc in H. symmetry in H. 
    rewrite <- add_zero in H.
    symmetry in H. apply add_left_cancel in H.
    rewrite add_succ in H. symmetry in H.
    apply (zero_not_succ) in H. exact H.
Qed.

Definition less_than (a b : nat) := (a <= b) /\ ~(b <= a).
Notation "a < b" := (less_than (a)(b)).

Proposition lt_iff_succ_le (a b : nat) :
a < b <-> S a <= b.
Proof.
    split.
    intro h.
    assert ((a <= b) /\ ~(b <= a)). exact h.
    exact (lt_aux_one (a)(b)(H)).

    intro h.
    apply lt_aux_two in h. exact h.
Qed.


End Inequality_World.