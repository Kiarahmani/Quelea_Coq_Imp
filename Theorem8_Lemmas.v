Require Import Cases.
Require Import Coq.Sets.Constructive_sets.
Require Import Definitions.
Require Import Axioms.
Require Import Omega.

(*----------------------------------------------------*)
(*Trivial Assertion About Binders of Replica IDs*)
Lemma rid_same_binder: forall (r:ReplID), (beq_nat (Rid_to_nat r)(Rid_to_nat r)) = true.
Proof.
  intro r. induction r. simpl. induction n.
  reflexivity. simpl. apply IHn.
Qed.


(*----------------------------------------------------*)
Lemma  Theorem8_beq_help:  forall η θ r,  F_Union θ r η r = Union Effect ( θ r) (Singleton Effect η).
Proof. intros. unfold F_Union.
       rewrite rid_same_binder. reflexivity.
Qed.



(*----------------------------------------------------*)
(*Two ReplIDs are the same, iff their binders are the same number*)
Lemma Theorem8_dom_help'_help: forall r r', r=r' <->  (beq_nat (Rid_to_nat r) (Rid_to_nat r')=true).
Proof.
  intros r r'.
  split; intro H.
  -Case"->".
   rewrite <- H.
   induction r. simpl. symmetry. apply beq_nat_refl.
  -Case"<-". destruct r. destruct r' as [n']. simpl in H.
   apply beq_nat_true  in H. rewrite H. reflexivity.
Qed.   



(*----------------------------------------------------*)
(*F_Union of something, has only one element in its domain!*)
Lemma Theorem8_dom_help' : forall η θ r' r,  dom (F_Union θ r η) r' -> r'=r.
Proof.
  intros. 
  assert (r=r' \/ r<>r') as HRidDec; try( apply ReplID_Equality_Decidable).
  destruct HRidDec; auto. apply error_not_domain in H; intuition. 
  destruct (beq_nat (Rid_to_nat r) (Rid_to_nat r')) eqn:E. compute. apply Theorem8_dom_help'_help in E; intuition.
  unfold F_Union. rewrite E. reflexivity.
Qed.




(*----------------------------------------------------*)
(*forall i>0, i-1 is less than i*)
Lemma Theorem8_nat_help : forall i:SeqNo, (i<>0) -> (lt (i-1) i).
Proof.
  intros.
  destruct i. 
  -compute in H. assert (0=0). reflexivity. intuition.
  - omega.
Qed.

