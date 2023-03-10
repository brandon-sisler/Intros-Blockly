From NAT Require Import Peanos_axioms.
From NAT Require Import Tutorial_World.
From NAT Require Import Addition_World.
From NAT Require Import Function_World.
From NAT Require Import Multiplication_World.

Section Power_World.
(*Now, let us move on to powers! Consider for a moment how you would explain to a computer how powers work in general, say for n^m.
Your first intuition is proabably to say take m copies of n, and multiply them together. That is more or less reasonable when explaining to a human how it should be done but naturally a computer will have no idea what you are talking about. Copies? Multiply `them all`? Not to mention, how do you take 0 copies of m, and get 1? The solution to this is simple, we know that we want n ^ 0 = 1, and then we can realize that we want n ^ 1 = n, n ^ 2 =  n * n^1, n ^ 3 = n * n^2, etc. We are now ready to define powers. *)
Fixpoint power (n m : nat):=
    match m with 
        |0 => 1
        |S k => n*(power (n)(k))
        end.
(*This definition says, find out what m is. If it is zero, return 1, else return n* n^ (m - 1). If this definition is confusing, work out a few examples, and see that it does indeed match our reasoning above.*)
(*Since it is rather cumbersome, and counter to the way powers are typically written, to write power (n)(m) the next line simply asks Coq to infer that we mean power (n)(m) when we say n ^ m.*)
Notation "n ^ m" := (power(n)(m)).

(*Now, this proposition is rather easy, since we literally built it in to the definition of powers, but it is useful nevertheless to explore the idea of definitional equality.*)
Proposition zero_pow (a : nat) : a ^ 0 = 1.
Proof.
    (*Before we complete this proof you should ask yourself, `Can Coq tell the difference between the thing on the left and the thing on the right?` Kepp in mind that when it reads a ^ 0 it sees power (a)(0) which is, by definition 1. Therefore by definition the thing on the left is 1, and as a result Coq should not be able to tell the difference between a^0 and 1. So reflexivity should work!*)
    reflexivity.
Qed.
(*The next proposition is also definitional, see if you cannot reason this one our similairly.*)
Proposition succ_pow (m n : nat) : m ^ S n = m * (m ^ n).
Proof. 
    reflexivity.
Qed.

(*This is one of the greatest proofs in this section, if only for the fact that it will prevent students from writing that 0 ^ 0 is zero. *)
Proposition zero_pow_zero : 0 ^ 0 = 1.
Proof.
    reflexivity.
Qed.

Proposition zero_pow_succ (m : nat): (0 ^ S m = 0).
Proof.
    rewrite succ_pow. rewrite zero_mul. reflexivity.
Qed.

Proposition pow_one (a : nat) : a ^ (1) = a.
Proof.
    rewrite succ_pow. 
    induction a. rewrite zero_pow_zero. rewrite zero_mul. reflexivity.
    rewrite mul_one. reflexivity.
Qed.

Proposition one_pow (m : nat) : 1 ^ m = 1.
induction m.
reflexivity.
rewrite succ_pow.
rewrite IHm.
rewrite mul_one.
reflexivity.
Qed.
(*This is another great proof, since it shows that we are not just making things up about powers for students to memeorize, but rather, that there are useful computation rules that are provable!*)
Proposition pow_add (a m n : nat) : a ^ (m + n) = a ^ m * a ^ n.
Proof.
    induction n.
    rewrite add_zero. rewrite zero_pow. rewrite mul_one. reflexivity.
    rewrite succ_add. rewrite succ_pow. rewrite IHn.
    rewrite succ_pow.
    rewrite (mul_comm (a ^ m)(a ^ n)).
    rewrite <-mul_assoc. rewrite mul_comm. reflexivity.
Qed.
(*Another good rule for computation.*)
Proposition mul_pow (a b n : nat) : (a * b) ^ n = a ^ n * b ^ n.
Proof.
    induction n. rewrite zero_pow. rewrite zero_pow. rewrite zero_pow.
    rewrite mul_one. reflexivity.

    rewrite succ_pow. rewrite succ_pow. rewrite succ_pow.
    rewrite IHn.
    rewrite mul_assoc. rewrite mul_assoc. rewrite <- (mul_assoc (b)(a^n)(b^n)). rewrite (mul_comm (b)(a^n)). 
    rewrite (mul_assoc (a^n)(b)(b^n)). reflexivity.
Qed.

Proposition pow_pow (a m n : nat) : (a ^ m) ^ n = a ^ (m*n).
Proof. 
    induction n. rewrite mul_zero. reflexivity.

    rewrite succ_pow. rewrite IHn. rewrite succ_dist. rewrite pow_add.
    rewrite mul_comm. reflexivity.
Qed.

Proposition add_squared (a b :nat) : 
(a + b) ^ 2 = a ^ 2 + b^ 2 + (2 * a * b).
Proof.
    rewrite succ_pow. rewrite pow_one.
    rewrite add_mul. rewrite mul_comm. rewrite add_mul.
    rewrite (mul_comm (b)(a+b)). rewrite add_mul.
    assert (a * a = a^ 2). rewrite succ_pow.
    rewrite pow_one. reflexivity.
    assert (b * b = b^ 2). rewrite succ_pow.
    rewrite pow_one. reflexivity.
    assert (b * a + a * b = 2 * a * b).
    rewrite <- (mul_one (b * a)).
    rewrite (mul_comm (b)(a)).
    rewrite <- succ_dist. 
    rewrite mul_comm. rewrite mul_assoc.
    reflexivity.

    rewrite H. rewrite H0.
    rewrite add_assoc. 
    rewrite <-(add_assoc (b*a)(a*b)(b^2)).
    rewrite H1.
    rewrite add_assoc. rewrite (commute (b^2)(2*a*b)).
    reflexivity.
Qed. 
End Power_World.