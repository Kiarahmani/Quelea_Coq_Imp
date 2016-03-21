Require Import case_coq.
Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Tactics.
Require Import Definitions.
Require Import oper_semantic_coq.
Require Import axioms_coq.
Require Import theorems_coq.
Require Import contract_definition.
Require Import contract_subs.
Require Import contract_Eval.
Require Import lemma5.
Require Import Theorem7_Lemma.
Require Import Theorem7.
Require Import Omega.
Import Operational_Semantics.


Lemma rid_same_binder: forall (r:ReplID), (beq_nat (Rid_to_nat r)(Rid_to_nat r)) = true.
Proof.
  intro r.
  induction r. simpl. induction n.
  reflexivity. simpl. apply IHn.
Qed.

  
Lemma  Theorem8_beq_help:  forall η θ r,  F_Union θ r η r = Union Effect ( θ r) (Singleton Effect η).
Proof. intros. unfold F_Union.
         rewrite rid_same_binder. reflexivity.
Qed.

Axiom error_not_domain: forall (r:ReplID)(t:Store),  (t r = St_Dom_Error) <-> (~(dom t) r).
Axiom ReplID_Equality_Decidable: forall (r r':ReplID), (r=r') \/ (r<>r').

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


                                 
Lemma Theorem8_dom_help' : forall η θ r' r,  dom (F_Union θ r η) r' -> r'=r.
Proof.
intros. 
assert (r=r' \/ r<>r') as HRidDec; try( apply ReplID_Equality_Decidable).
destruct HRidDec; auto. apply error_not_domain in H; intuition. 
destruct (beq_nat (Rid_to_nat r) (Rid_to_nat r')) eqn:E. compute. apply Theorem8_dom_help'_help in E; intuition.
unfold F_Union. rewrite E. reflexivity.
Qed.


  

Lemma Theorem8_nat_help : forall i:SeqNo, (i<>0) -> (lt (i-1) i).
Proof.
  intros.
  destruct i. 
  -compute in H. assert (0=0). reflexivity. intuition.
  - omega.
Qed.

