From NAT Require Import Peanos_axioms.
From NAT Require Import Tutorial_World.
From NAT Require Import Addition_World.



Section Multiplication_World.
(*Well, here we go again. One of Peanos axioms states that m * 0 = 0. However, the reverse has not been shown, so let us do it now.*)
Proposition zero_mul (m : nat) : 0 * m = 0.
Proof.
    induction m.
    rewrite mul_zero. 
    (*This base case is very interesting, since in some sense we are on the verge of derivining the fact that like terms commute. After all, you cannot tell the difference between 1*1 and 1*1, even though I swapped the order of the ones.(You cannot prove I did not)*)
    reflexivity.
    (*Now again we can use another axiom, and then easily simplify.*)
    rewrite succ_dist. rewrite add_zero. exact IHm.
Qed.

Proposition mul_one (m : nat) : m*1 = m. 
Proof.
    induction m.
    rewrite zero_mul. reflexivity.
    rewrite succ_dist.
    rewrite mul_zero. rewrite zero_add. reflexivity.
Qed.

Proposition one_mul (m : nat) : 1*m = m.
Proof.
    induction m.
    rewrite mul_zero. reflexivity.
    rewrite succ_dist.
    rewrite IHm.
    rewrite succ_add. rewrite add_zero. reflexivity.
Qed.
(*Now we will derive one of the most important propositions in this section. That is, leftward distribtivity. The best thing to do here is to try and see which inductive variable suits you the best. It is most likely possible using any of them, but not without tears.*)
Proposition mul_add ( t a b : nat) : t*(a + b) = (t * a) + (t * b).
Proof.
    induction a. rewrite zero_add. rewrite mul_zero. rewrite zero_add. 
    reflexivity.
    rewrite succ_dist. rewrite (commute (t *a)(t)).
    symmetry. rewrite add_assoc. rewrite <- IHa.
    rewrite commute. rewrite <- succ_dist. reflexivity.
Qed.
(*This is another important result, we are now going to show that multiplicaiton is associative. If you are an algebrist proving this now seems out of order, since to prove a ring structure you usually show this first. Indeed, if this angers you feel free to contact Dr. Steven Clonz at sclontz@southalabama.edu. On the other hand if you are enjoying this expierence, and wish to find an outlet for your praise, then by all means try brandon.sisler1118@gmail.com. *)
Proposition mul_assoc (a b c : nat) : (a * b) * c = a * (b * c).
Proof.
    induction c.
    rewrite mul_zero. rewrite mul_zero. rewrite mul_zero. reflexivity.
    rewrite succ_dist. rewrite succ_dist.
    rewrite mul_add. rewrite IHc. reflexivity.
Qed.
(*Now, in secret, we are going to use the next result to obtain a commutative ring. But in any case, this uses the same techniques you have been using the whole time.*)
Proposition succ_mul (a b : nat) : S (a) * b = a * b + b.
Proof.
    induction b.
    rewrite mul_zero. rewrite mul_zero. rewrite add_zero. reflexivity.
    rewrite succ_dist. rewrite IHb. rewrite add_one. symmetry.
    rewrite add_one. rewrite mul_add. rewrite mul_one. rewrite add_assoc.
    rewrite add_assoc. rewrite <- (add_assoc (a)(b)(1)).
    rewrite (commute (a)(b)). rewrite add_assoc. reflexivity.
Qed.
(*Now, let us show rightward associativity.*)
Proposition add_mul (a b t : nat) : (a + b)*t = (a * t) + (b * t).
Proof.
    induction t. rewrite mul_zero. rewrite mul_zero. rewrite mul_zero. 
    rewrite add_zero. reflexivity.

    rewrite succ_dist. rewrite IHt. rewrite add_one.
    rewrite mul_add. rewrite mul_add. rewrite mul_one. rewrite mul_one.
    rewrite add_assoc. rewrite <-(add_assoc (b * t)(a)(b)). 
    rewrite (commute (b*t)(a)). rewrite (add_assoc (a)(b*t)(b)). 
    rewrite add_assoc. reflexivity.
Qed.
(*Great, now that we have all these results we can get to the one that would have helped you all along, and hilariously relies on none of the previous parts. On the other hand, it was good to have not used this result quite yet, since now we have a good appreciation for how things can be proven when commutivity is not neccesarily true.*)
Proposition mul_comm (m n : nat) : m * n = n * m.
Proof.
    induction n. rewrite mul_zero. rewrite zero_mul. reflexivity.

    rewrite succ_dist. rewrite succ_mul. rewrite IHn. reflexivity.
Qed.
(*To end, we will prove what could be considered a theorem that will be helpful for computation.
Consider, after all, when your instructors wave their hands and just write a * (b * c) = b * (a * c) without appealing to the axioms. This will not work here, and yet, it surely is our dream to have the computer learn to waive its hands as well. The compromise is struck by showing this computational trick is justifable. Let us do so now. *)
Proposition mul_left_comm (a b c : nat) : a * (b * c) = b * (a * c).
Proof.
    induction a. rewrite zero_mul. rewrite zero_mul. rewrite mul_zero.
    reflexivity. 

    rewrite succ_mul. rewrite add_one. rewrite IHa. rewrite add_mul.
    rewrite one_mul. rewrite mul_add. reflexivity.
Qed.

End Multiplication_World.