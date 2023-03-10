From NAT Require Import Peanos_axioms.
From NAT Require Import Tutorial_World.
From NAT Require Import Addition_World.
From NAT Require Import Function_World.
From NAT Require Import Proposition_World.

Section Advanced_Proposition_World.
(*Now, let us consider the following proposition. Now if you said the proposition out loud you might wonder what there is to prove. After all, it states that `If P and Q then P and Q.` But this is not strickly true. Rather, we are trying to show that if we have a proof of P, and a proof of Q, that it is possible to construct a proof of P /\ Q, and as far as Coq is concerned, it does not know our interpretation of these symbols, it only has a notion of the `legal moves` we can make on it.*)
Proposition p_and_q (P Q : Prop) (p : P)(q : Q): P /\ Q.
Proof.
    split.
    exact p. exact q.
Qed.
(*Next we wish to show that, given a proof of P and Q, that we can construct a proof of Q and P.*)
Proposition and_symm (P Q : Prop) : P /\ Q -> Q /\ P.
Proof.
    intro h. 
    destruct h.
    split.
    exact H0. exact H.
Qed.
(*Finally we wish to shoe that /\ is a transitive realtion. Bonus points if you have begun to suspect that /\ is an equivalence relation!*)
Proposition and_trans (P Q R : Prop) : (P /\ Q) -> (Q /\ R) -> (P /\ R ).
Proof.
    intros h1 h2.
    destruct h1. destruct h2.
    split.
    exact H. exact H2.
Qed.

Proposition iff_trans (P Q R : Prop) : (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros h1 h2.
    split. intro hp.
    apply h2. apply h1.
    exact hp.
    intro hr.
    apply h1. apply h2. 
    exact hr.
Qed.


Proposition q_then_or_q ( P Q : Prop) : Q -> (P \/ Q).
Proof.
      intro hq.
      right.
      exact hq.  
Qed.

Proposition or_symm (P Q : Prop) : P \/ Q -> Q \/ P.
Proof.
    intro hpq.
    case hpq.
    intro hp.
    right. exact hp.
    intro hq.
    left. exact hq.
Qed.
(*Another good problem would be to show that or is not transitive. *)

Proposition and_or_dist_left (P Q R : Prop) :
(P /\ (Q \/ R)) <-> ((P /\ Q) \/ (P /\ R)).
Proof.
    split.
    intro h1.
    destruct h1 as [hp hq].
    destruct hq.
    left. exact (p_and_q (P)(Q)(hp)(H)). 
    right. exact (p_and_q (P)(R)(hp)(H)).
    intro h.
    destruct h. destruct H.
    split. exact H. 
    left. exact H0.
    destruct H.
    split. exact H.
    right. exact H0.
Qed.

Proposition contra (P Q : Prop) : (P /\ ~P) -> Q.
Proof.
    intro h.
    destruct h as [p notp].
    assert False.
    exact (notp (p)).
    exfalso. exact H.
Qed.

Lemma a_then_b (A B : Prop)(b : B) : A->B.
Proof.
    intro h. exact b.
Qed.
Lemma prop_assoc (A B C : Prop) : ((A -> B) -> C) -> (A -> (B -> C)).
Proof.
    intros h h1 h2.
    assert (A->B). exact (a_then_b (A)(B)(h2)).
    apply h in H. exact H.
Qed.

(*Logic*)
Definition prop_degeneracy := forall A:Prop, A = True \/ A = False.

Definition prop_extensionality := forall A B:Prop, (A <-> B) -> A = B.

Definition excluded_middle := forall A:Prop, A \/ ~ A.

Lemma True_is_true : True.
Proof. apply I. Qed.

Lemma False_is_not_true : False <> True.
Proof.
    intro h. rewrite h. apply True_is_true.
Qed.

Lemma True_then_false (h : prop_degeneracy) : (True -> False) = False.
Proof.
    unfold prop_degeneracy in h. 
    assert ((True -> False) = True \/ (True -> False) = False).
    exact (h (True -> False)).
    case H. intro hq. exfalso.
    assert (True -> False). rewrite hq. exact True_is_true.
    apply H0. exact True_is_true.
    intro h1. exact h1.
Qed.
(**)

Lemma not_true_is_false (h : prop_extensionality) ( hm : excluded_middle) : 
(~True) = False.
Proof.
    unfold excluded_middle in hm. unfold prop_extensionality in h.
    apply h. split. 
    intro hp. apply hp. exact True_is_true.
    
    intros hp ht. exact hp. 
Qed.

Lemma prop_equality_right_select (A B C : Prop) :
((A = B) = C) -> (B = C).
Proof.
Admitted.

Lemma not_false_is_true (h : prop_degeneracy) : (~False) = True.
Proof.
    unfold prop_degeneracy in h.
    assert (((~False) = True)= True \/ ((~False) = True)= False). 
    exact (h((~False) = True)). 
    case H. intro h1.
    rewrite h1. exact True_is_true.
    intro h1. 
    assert (True = False). apply prop_equality_right_select in h1. exact h1.
    assert (True -> False). intro ht. rewrite <-H0. exact True_is_true.
    exfalso. rewrite <- H0. exact True_is_true.
Qed.

Lemma deg_ext : prop_degeneracy -> prop_extensionality.
Proof.
    intro h. unfold prop_degeneracy in h. unfold prop_extensionality.
    intros ha hb H. 
    assert (ha = True \/ ha = False). exact (h(ha)).
    assert (hb = True \/ hb = False). exact (h(hb)).
    destruct H0. destruct H1.
    rewrite H0. rewrite H1. reflexivity.
    exfalso.
    destruct H. rewrite H0 in H. rewrite H1 in H. rewrite (True_then_false) in H.
    exact H. exact h.
    destruct H1.
    destruct H. rewrite H1 in H2. rewrite H0 in H2. rewrite (True_then_false) in H2.
    exfalso. exact H2. exact h. 
    rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma deg_mid : prop_degeneracy -> excluded_middle.
Proof.
    unfold prop_degeneracy. unfold excluded_middle. intros h ha.
    assert (ha = True \/ ha = False). exact (h(ha)).
    destruct H. left. rewrite H. exact True_is_true.
    right. rewrite H.
    assert ((~ False) = True). apply not_false_is_true. exact h. 
    rewrite H0. exact True_is_true. 
Qed.

Lemma false_implies (A : Prop): False -> A.
Proof.
    intro h. exfalso. exact h.
Qed.
Lemma implied_truth (A : Prop) : A -> True. 
Proof.
    intro h. exact True_is_true.
Qed.
Lemma iff_true_then_True (A : Prop) (a : A): A <-> True.
Proof.
    split.
    intro h.  exact True_is_true. intro h. exact a. 
Qed.

Lemma swap_not (A : Prop) (h_ext : prop_extensionality)(h_mid : excluded_middle )
: ((~A) = True) -> (A = False).
Proof.
    intro h. 
    unfold prop_extensionality in h_ext. 
    unfold excluded_middle in h_mid.
    apply h_ext. 
    split. intro ha. 
    assert ((A -> False) <-> False). split. intro H. apply H. exact ha.
    intros H1 H2. exact H1. apply H. 
    assert ((~ A )= (A -> False)). reflexivity.
    rewrite <-H0 in H. rewrite h in H.  
    apply H. exact True_is_true. exact ha. exact (false_implies (A)).
Qed.

Lemma swap_not_op (A : Prop) (h_ext : prop_extensionality)(h_mid : excluded_middle )
: ((~A) = False) -> (A = True).
Proof.
Admitted.

Lemma mid_ext_deg : 
((prop_extensionality) /\ (excluded_middle)) -> (prop_degeneracy).
Proof.
    unfold prop_degeneracy. unfold prop_extensionality. unfold excluded_middle.
    intro h. destruct h as [h_ext h_mid].
    intro ha.
    assert (ha \/ ~ha). exact (h_mid (ha)). 
    destruct H. 
    assert (ha <-> True). exact (iff_true_then_True (ha)(H)).
    apply h_ext in H0. 
    left. exact H0.
    
    assert (~ha <-> True). split. exact (implied_truth (~ha)).
    intro ht. exact H.
    apply h_ext in H0. 
    right.
    apply (swap_not (ha)) in H0. exact H0. exact h_ext. exact h_mid.
Qed.

Proposition ext_mid_iff_deg : ((prop_extensionality) /\ (excluded_middle)) <-> (prop_degeneracy).
Proof.
    split. exact mid_ext_deg. intro h. split. apply deg_ext. exact h.
    apply deg_mid. exact h.
Qed.

Proposition contradiction (h: prop_degeneracy) (P : Prop): P <-> ((~P) = False).
Proof.
    split. intro h1. 
    unfold prop_degeneracy in h.
    assert (P = True \/ P = False). exact (h(P)).
    case H. 
    intro Hp. rewrite Hp. apply not_true_is_false.   
    apply deg_ext. exact h. apply deg_mid. exact h.
    intro H1. exfalso. rewrite H1 in h1. exact h1.
    intro hp.
    assert ((~P) = True \/ (~P) = False). exact (h (~P)).
    case H. 
    intro Hp. exfalso. rewrite <- hp. rewrite Hp. exact True_is_true.  
    intro Hp. apply (swap_not_op (P)) in Hp. rewrite Hp. exact True_is_true.
    apply deg_ext. exact h. apply deg_mid. exact h.
Qed.

Proposition contrapostive2 (P Q : Prop) : (~Q -> ~P) -> (P -> Q).
Proof.
Admitted.

End Advanced_Proposition_World.