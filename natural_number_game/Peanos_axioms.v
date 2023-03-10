Section Peanos_Axioms.
(*This axiom states that for all natural numbers, n, it is not true that n is the succesor of 0. More casually we can say that 0 has no predeccesor.*)
Axiom zero_not_succ : forall n : nat, ~(S n = 0).

(*This axiom is more or less core to our intuition that if x + 1 = y + 1 then x = y. This is stated precisely below. That is, for two natural numbers n, m, if S n = S m then n = m. This property catagorised the notion that x+1 is an injective function, and has been named accordinly.*)
Axiom succ_inj : forall n m : nat, (S n = S m) -> n = m.

(*This axiom says that for all natural numbers n + 0 = n. This seems trivial but naturally it must be stated, after all Coq does not have any webcam capabilities, and thus cannot see you waving your hands, so we must tell it that this is something we want to use.*)
Axiom add_zero : forall n :nat, n + 0 = n.

(*This axiom catorizes the additivity of the succesor function and says that for any two natural numbers n, m that n + S (m) = S(n + m).*)
Axiom succ_add : forall n m :nat, n + S(m) = S(n + m).

(*Yet again this is an axiom that you may believe is trivial, but again it must be stated. Thus, we have that for all natural numbers, n, that n*0 = 0. *)
Axiom mul_zero : forall n : nat, n*0 = 0.

(*This axiom encodes a weaker version of the distributive property. Namely, that for all n, m in the natural numbers, that n* S(m) = n*m + n. Commonly you see this concept presented as n*(m+1) = nm + n.*)
Axiom succ_dist : forall n m : nat, n*(S m) = n* m + n.
End Peanos_Axioms.