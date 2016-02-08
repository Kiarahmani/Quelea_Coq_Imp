KIA
Require Import case_coq.
Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import parametes_coq.
Require Import config_coq.
Require Import oper_semantic_coq.
Require Import axioms_coq.
Require Import theorems_coq.
Import Config.
Import parameters.
Import Operational_Semantics.

(**************************************************************************************************)
(*************************************** Lemma 5 of the Paper *************************************)
Theorem Lemma5: forall (Θ: Store)(Ex Ex':Exec) (s:SessID) (i:SeqNo)(op:OperName)(η:Effect)(r:ReplID),
                                       {Θ|-Ex, <s,i,op> ~r~> Ex', η} -> (WF Ex) -> (WF Ex').

Proof.
  
  intros Θ Ex Ex' s i op η r. intros H_reduct H_WF.    
  (*Inversion on the reduction*)
  inversion H_reduct;
  clear H9 H1 H0 H H2 H5 s0 i0 op0 η0;rename H3 into  H_η; rename H4 into  H_η'; rename H7 into H_vis';
  rename H10 into H_so';rename H11 into H_sameobj';rename H6 into H_Exec; rename H8 into H_Exec'.

  (*Trivial assertions*)
  assert ((Ex')-A = A')                as H_EX'A.      rewrite <- H_Exec'; auto.
  assert ((Ex')-vis = vis')            as H_EX'vis.    rewrite <- H_Exec'; auto. 
  assert ((Ex')-so = so')              as H_EX'so.     rewrite <- H_Exec'; auto.
  assert ((Ex')-sameobj = sameobj')    as H_EX'sameobj.  rewrite <- H_Exec'; auto.

  (*so is transitive*)
  assert (forall (Ex:Exec)(a b c:Effect), (Ex-so a b)->(Ex-so b c)->(Ex-so a c)) as H_soTrans. apply SO_SeqIII.
 
(******************The goal is to prove well formedness of the Ex', based on the 
                   definition of well formedness, now break it into 6 subgoals *)
  apply FW.


  Case "----------------Proof of WF1".
        {apply hb'_Acyclicity in H_reduct. rewrite <- H_Exec' in H_reduct. exact H_reduct. exact H_WF. }

         
  Case "----------------Proof of WF2".
        {unfold WF2. rewrite H_Exec'. intros a b G1 G2 G3. rewrite  H_EX'A in G1; rewrite  H_EX'A in G2.
         rewrite H_EX'sameobj.
         specialize (H_sameobj' a b). apply H_sameobj'.
         exact G1. exact G2. }

  Case "----------------Proof of WF3 ".
        { unfold  WF3. intros  a b c. rewrite H_Exec'; rewrite H_EX'so. intro G1. destruct G1.
          specialize (H_soTrans Ex' a b c). rewrite H_EX'so in H_soTrans.
          apply H_soTrans. exact H. exact H0. }

  Case "----------------Proof of WF4 ".
        { unfold WF4. intro a. rewrite H_Exec'; rewrite H_EX'A; rewrite H_EX'sameobj.
          specialize (H_sameobj' a a).
          intro G. apply H_sameobj'. exact G. exact G. }

  Case "----------------Proof of WF5 ".
        { unfold WF5. intros a b. rewrite H_Exec'; rewrite H_EX'A; rewrite H_EX'sameobj.
          intros G1 G2 G3. specialize (H_sameobj' b a).
          apply H_sameobj' in G2. exact G2. exact G1. }

  Case "----------------Proof of WF6 ".
        { unfold WF6. intros a b c. rewrite H_Exec'; rewrite H_EX'A; rewrite H_EX'sameobj.
          intros G1 G2 G3 G4. specialize (H_sameobj' a c).
          apply H_sameobj' in G1. exact G1. exact G3. }   
Qed.

 

























