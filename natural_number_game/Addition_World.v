From NAT Require Import Peanos_axioms.
From NAT Require Import Tutorial_World.
Section Addition_World.

(*Now that the tutorial is complete we can begin to prove something a little more difficult. Namely, that 0 + n = n. Obvious, says your intro to proof student, but of course it is not nearly as trivial as it sounds, since good old Peano, in his hurry, did not leave us an axiom that says addition is commutative. Our only option then is to prove it, which we will do now.*)
Proposition zero_add (n : nat) : 0 + n = n.
Proof.
    induction n.
(*In this step we are doing induction on n. This is a good moment to remind yourself how the naturals are formally defined. In some sense the naturals consist of two things, 0, and something that is one more than something else. induction knows this (since the naturals are inductively defined) and allows us to prove our proposition for the 0-case (the base case) and then allows us to prove the proposition for the inductive step.*)
    rewrite add_zero. reflexivity.
(*Now we just need to do some cleaning up and our base case is complete. If you are starting to feel tired of all this explicit computation you are not alone, and there are tactics that can make these steps trivial. But for now your suffering is rewarded, in that you will actually understand what Coq is doing. Eventually, though, it will become neccesary to use these tactics in order to avoid tedium, but by then we will know what goes into them, and will only use the old ones to show off to our readers.*)
(*Now it is time to do our inductive step.*)
    rewrite succ_add.
    rewrite IHn.
    reflexivity.
Qed.

(*Now that we have our result we can finally prove a big result about the natural numbers, that their addition is associative!*)
Proposition add_assoc (a b c : nat) : (a + b) + c = a + (b + c). 
Proof.
    induction c.
(*We will choose to do induction on c, by way of knowing that the other choices will bring us pain, although this is a good lesson on not getting to entrenched on your choice of inductive variable, if there are others available, else you spend lots of time trying to induct on a. The author of this file would never commit such an error, though, and since no backlogs of this file exist, I dare you to prove (forgive the pun) otherwise. *)
    rewrite add_zero. rewrite add_zero. reflexivity.
(*again, we must do some simple computations in order to arrive at the conclusion of our base case.*)
    rewrite succ_add. rewrite succ_add. rewrite succ_add.
    rewrite IHc.
    reflexivity.
Qed.

(*Again, our next proposition looks like something that we already know, and thus, highlights the importance of using a theorem prover, since this statment is NOT something we already know, at least not formally. Remember Peano said that x + S a = S (x + a) and at the moment, we have no commutativity, so if we wish to use this fact we must actually sit down and prove it.*)
Proposition add_succ (a b : nat) : (S a) + b = S (a + b).
Proof.
    induction b.
    rewrite add_zero. rewrite add_zero. reflexivity.
    rewrite succ_add.
    rewrite succ_add.
    rewrite IHb.
    reflexivity.
Qed.
(*WE COULD HAVE THE USER USE AN END OF PROOF SYMBOL FOR REFL, THAT WAY IT 
CAN BE DONE WITHOUT USER IMPUT*)

(*Now that we have many of the proofs we want in order to manipulate addition we can move on to prove the commutivity. You may have noticed that all of these propositions seem to follow fairly quickly from previous results. This is something that should be strived for, since especially in theorem provers, extremely long arguments tend to become cumbersome and confusing. Furthermore, if every lemma and sub-proof is proven in your proposition then you will have to prove them all again when you try and prove a similair theorem! Therefore, if possible it is good to prove many small theoreoms, and then combine them for your result.*)
Proposition commute (m n : nat) : m + n = n + m. 
Proof.
    induction n.
    rewrite add_zero. rewrite zero_add. reflexivity.
    rewrite succ_add.
    rewrite add_succ.
    rewrite IHn.
    reflexivity.
Qed.

Proposition add_one (n : nat) : S n = n + 1.
Proof.
    rewrite commute.
    reflexivity.
(*What on Earth, you say? Why did that work. Well remember that S n "stands for" 1 + n. In some sense Coq cannot tell the difference between them! On the other hand n + 1 is a mysterious, unknown, and potentially distinct object. Therefore, if you attempt to just complete this proof using only reflexivity, Coq will protest, and you will be met with an error.*)
Qed.

(*This proposition is designed in order to exibit how Coq uses parenthesis. Unfortunately, for addition it is left-ward associative, which while being the norm throughout most of mathematics, is counter to the convention in Type Theory, and thus earned itself snippy remark from the author. *)
Proposition rcomm ( m n k : nat) : (m + n) + k = (m + k) + n.
Proof.
    symmetry.
    rewrite add_assoc.
    rewrite commute.
    rewrite add_assoc.
    rewrite commute.
    rewrite (commute n m).
(*This line highlighs an important point. Up until now we have not specified where we want out tactics and propositions to act. This is usually fine, Coq will just look for somewhere that it can apply the proposition, and most of the time the only place it can do so is where we intended it. On the other hand, if there are many options then Coq will just choose the first one, and if that is not what we intended then it is neccsary to give it more information on where exactly we want it to act.*)
    reflexivity.
Qed.

End Addition_World.