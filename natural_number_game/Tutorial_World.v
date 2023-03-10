From NAT Require Import Peanos_axioms.

Section Tutorial_World.

(*In this example the students will be througly stunned by the pedantcy by which theorem provers operate. Namely, one is required to tell the computer that the thing on the left is exactly the same as the thing on the right (and in doing
so, invokes the relexivity of equality). *)
Proposition example1 (x y z : nat): x *y + z = x*y +z.
Proof.
    reflexivity.
Qed.

(*Now, if you are someone who thinks that every proof is as trivial as the one before, you may have attempted to just use refelxivity again. This will not work, though, since, strictly speaking, the thing on the left does not look like the thing on the right. However, Coq understands the principle of subsitution, by means
of the rewrite tactic, which we can use now.*)
Proposition example2 (x y : nat) (h : y = x + 7) : 2* y = 2*(x+7).
Proof.
    rewrite h.
    reflexivity.
Qed.

Proposition example3 (x y : nat)(h : S x = y): S (S x) = S y.
Proof.
    rewrite h.
    reflexivity.
Qed.

(*Now we have come to the first proof that actually requires a bit of machinery.*)
Proposition example4 (x : nat) : x + S 0 = S x.
Proof.
(*Now we are trying to show that x + S (0) = S x. Luckily Peano says that in general x + S y = S (x + y)*, we may use this now.*)
    rewrite succ_add.
(*Now, let us stop to ponder what exactly we did. We said we wanted to prove that x + S 0 = S x, but our application of our rule has informed us that it is  sufficient to show that S (x + 0 ) =  S x, so now all we must do is prove our new statement, and then the rest will follow immediatly.*)

(*Next we use another helpful fact from Peano, who says that x + 0 = x*)
    rewrite add_zero.
(*and hey, that is what we wanted to show*)
    reflexivity.
Qed.
End Tutorial_World.