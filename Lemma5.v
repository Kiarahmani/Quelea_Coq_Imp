Require Import Cases.
Require Import Definitions.
Require Import Operational_Semantics.
Require Import Axioms.
Require Import Lemma5_Lemmas.

(**************************************************************************************************)
(*************************************** Lemma 5 of the Paper *************************************)
Theorem Lemma5: forall (Θ: Store)(Ex Ex':Exec) (s:SessID) (i:SeqNo)(op:OperName)(η:Effect)(r:ReplID),
                                       [Θ|-Ex, <s,i,op> ~r~> Ex', η] -> (WF Ex) -> (WF Ex').

Proof.
    
  intros Θ Ex Ex' s i op η r. intros H_reduct H_WF.    
  (*Inversion on the reduction*)
  inversion H_reduct;
    clear H11 H1 H0 H H3 H6 s0 i0 op0 η0. rename H4 into  H_η; rename H5 into  H_η'. rename H13 into Hi.
  rename H7 into H_vis'.
  rename H9 into H_so'; rename H12 into H_sameobj';rename H8 into H_Exec; rename H10 into H_Exec'.

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


  Case "Proof of WF1".
        {apply hb'_Acyclicity in H_reduct. rewrite <- H_Exec' in H_reduct. exact H_reduct. exact H_WF. }

         
  Case "Proof of WF2".
        {unfold WF2. rewrite H_Exec'. intros a b G1 G2 G3. rewrite  H_EX'A in G1; rewrite  H_EX'A in G2.
         rewrite H_EX'sameobj.
         specialize (H_sameobj' a b). apply H_sameobj'.
         exact G1. exact G2. }

  Case "Proof of WF3 ".
        { unfold  WF3. intros  a b c. rewrite H_Exec'; rewrite H_EX'so. intro G1. destruct G1.
          specialize (H_soTrans Ex' a b c). rewrite H_EX'so in H_soTrans.
          apply H_soTrans. exact H. exact H0. }

  Case "Proof of WF4 ".
        { unfold WF4. intro a. rewrite H_Exec'; rewrite H_EX'A; rewrite H_EX'sameobj.
          specialize (H_sameobj' a a).
          intro G. apply H_sameobj'. exact G. exact G. }

  Case "Proof of WF5 ".
        { unfold WF5. intros a b. rewrite H_Exec'; rewrite H_EX'A; rewrite H_EX'sameobj.
          intros G1 G2 G3. specialize (H_sameobj' b a).
          apply H_sameobj' in G2. exact G2. exact G1. }

  Case "Proof of WF6 ".
        { unfold WF6. intros a b c. rewrite H_Exec'; rewrite H_EX'A; rewrite H_EX'sameobj.
          intros G1 G2 G3 G4. specialize (H_sameobj' a c).
          apply H_sameobj' in G1. exact G1. exact G3. }

  Case "Proof of WF7 ".
        {unfold WF7.
         intros a b H.
         intuition; apply WF_Relation with (a:=a)(b:=b) in H; destruct H as [Ha Hb].
         -apply So_Domain in Ha; auto.
         -apply Vis_Domain in Ha; auto.
         -apply Sameobj_Domain in Ha; auto.

         -apply So_Domain in Hb; auto.
         -apply Vis_Domain in Hb; auto.
         -apply Sameobj_Domain in Hb; auto.
        }
        
Qed.

 


























