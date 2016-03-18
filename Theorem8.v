Require Import case_coq.
Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Tactics.
Require Import parametes_coq.
Require Import config_coq.
Import Config.
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
Import parameters.
Import Operational_Semantics.


Lemma Theorem8_dom_help : forall η θ r,  dom (F_Union θ r η) = Singleton ReplID r.
Proof.
intros.
compute. admit.
Qed.


Lemma Theorem8_nat_help : forall i:SeqNo, (i<>0) -> (lt (i-1) i).
Proof.
  intros.
  destruct i. 
  -compute in H. assert (0=0). reflexivity. intuition.
  - omega.
Qed.
  
Lemma  Theorem8_beq_help:  forall η θ r,  F_Union θ r η r = Union Effect ( θ r) (Singleton Effect η).
  Proof. admit. Qed.

  
Theorem Theorem8: forall Σ Ex Ex' θ θ' η τ Ing1 Ing2 ss ii σσ op, 
                     (Ing1 = (mkSoup_Ing ss ii ((mkop_cls op τ)::σσ))) ->
                     (Ing2 = (mkSoup_Ing ss (ii+1) σσ)) ->
                     (WF_union Σ Ing1) -> (WF_union Σ Ing2) ->
                     [[Ex,θ,(Σ||| Ing1) --τ,η-->  Ex' ,θ' , (Σ|||Ing2)]] ->

                     WF Ex -> CausCons θ Ex -> CausCons θ' Ex'.
Proof. intros  Σ Ex Ex' θ θ' η τ Ing1 Ing2 ss ii σσ op HIng1 HIng2. intros HWF_Union1 HWF_Union2.
       intros HProg HWF HCausCons.
       inversion HProg; subst.
       -Case"EffVis". rename Ex' into Ex. clear H. 
        unfold CausCons. intros; rename η0 into η'; rename r0 into r'.
        rename H into HAa. rename H0 into H. rename H1 into H0. rename H2 into H1. rename H3 into H2.
        rename H4 into H3. rename H5 into H4. rename H6 into H5. rename H7 into H6. 
        inversion H; subst.
        +destruct H7.  unfold CausCons in HCausCons. specialize (HCausCons r' a η').
         apply HCausCons; auto. 
         
         



         
        +inversion H7. rewrite H7. rewrite<- H7 in H4. rewrite Theorem8_dom_help in H4. destruct H4.
         (*nice so far*)
         rewrite <- H8 in H5.
         rewrite Theorem8_beq_help in H5.
         inversion H5.
         (*1- η' is in θr*)
         subst.
         rewrite Theorem8_beq_help. apply Union_introl. compute.
         unfold CausCons in HCausCons. specialize (HCausCons r a η').
         apply HCausCons;auto. 
         (*2  η'=η*)
         inversion H4; subst; rename η' into η.
         destruct Ex as [A vis so sameobj]. 
         apply Inversion_HBO_Help with (A:=A) (vis:=vis) (so:=so) (sameobj:=sameobj)in H6.
         destruct H6 as [|Hsingle]. rename H6 into Hsteps.
         (***2.1 multiple steps behind hbo*)
         destruct Hsteps as [c]. destruct H6 as [HBOac Hsinglecη].
         assert (θ r c). { 
            apply H2. unfold In. simpl. destruct Hsinglecη.
            apply Union_introl. unfold In. apply first. apply H6.
            apply Union_intror. destruct H6. unfold In. apply first. apply H6. }
         
         rewrite Theorem8_beq_help. apply Union_introl.
         unfold In. unfold CausCons in HCausCons.
         specialize (HCausCons r a c). apply HCausCons; auto. 
         (***2.2 ONE step behind hbo*)
         (*2.2.1 from so*)
         rewrite Theorem8_beq_help. apply Union_introl.
         apply H2. unfold In.  simpl.
         destruct Hsingle.  apply Union_intror.
         unfold In. apply first. inversion H6. apply H8.
         (*2.2.2 from vis*)
         apply Union_introl. unfold In. apply first. apply H6.
         (***2.3 Trivial*)
         reflexivity.




       - unfold CausCons. intros; rename η0 into η'; rename r0 into r'. rename H6 into Hreduct.
         clear HWF_Union1 HWF_Union2 H HProg H0. rename H4 into HBO'. 
         inversion Hreduct. subst.
         remember (E A vis so sameobj) as Ex.
         assert (Ex-hbo a η'). {
           apply HBO'_HBO with
           (Ex:=Ex)(Ex':= (E A' vis' so' sameobj'))(s:=ss0)
                   (i:=ii0)(op:=opp)(η:=η)(r:=r)(θ:=θ');auto.
           intro. intuition. subst. specialize (H9 a). apply H9 in H1.
           destruct H1. 
           subst.
           (*apply hbo accyclic*)


           
           inversion HBO'; subst.
           +SCase"single step".
            inversion H.
            *SSCase"from soo".
             inversion H0 as [Hso' Hsameobj']; simpl in Hso'; simpl in Hsameobj'; clear H0.
             apply t_step. simpl. unfold soo. left.  split.
             (*1Proof of so*)
             specialize (H14 a η'). apply H14 in Hso'.
             inversion Hso'.
             (*1.1 proof from  (so a η'0 \/ a = η'0) /\ η' = η*)
             destruct H0. rewrite H4; clear H4.
             inversion H0.
             (*1.1.1 proof from  (so a η'0)*)
             replace so with ((E A vis so sameobj)-so) in H4.
             rewrite SO_Seq_General.
             rewrite SO_Seq_General  in H4. specialize (H8 η'0).
             assert (seq η'0 = seq η - 1). { assert (seq η'0 = ii0-1). intuition. rewrite H6. intuition. }
             rewrite H6 in H4. omega. reflexivity.
             (*1.1.2 proof from  (a = η'0)*)
             apply SO_Seq_General. rewrite H4.
             replace (seq η'0) with (ii0 - 1). replace (seq η) with ii0.
             apply Theorem8_nat_help. (***!***) admit. (******!****)
             intuition.  specialize (H8 η'0). intuition. 
             (*1.2 proof from so: trivial*)
             apply H0.

             (*2proof of sameobj*)
             apply Sameobj_Def with (Ex:= (E A vis so sameobj)) (Ex':=  (E A' vis' so' sameobj'))
                                                                (opk :=  < ss0, ii0, opp >)
                                                                (η:=η)(r:=r)(Θ:= θ'); simpl;auto.
             apply WF_Relation with (a:=a)(b:=η')(r:=sameobj') in Hsameobj'.
             destruct Hsameobj'. replace (sameobj') with ((E A' vis' so' sameobj')-sameobj) in H0;auto.
             apply Sameobj_Domain in H0; simpl in H0.
             replace (sameobj') with ((E A' vis' so' sameobj')-sameobj) in H4;auto.
             apply Sameobj_Domain in H4; simpl in H4.
(*here we need to prove that A a and A η'*)
             specialize (H9 a).
             apply H9 in H0. destruct H0; auto.
             subst. intuition.
             apply SO_NewEff with (Ex:= E A vis so sameobj) (Ex':=  E A' vis' so' sameobj')
                                                                (opk :=  < ss0, ii0, opp >)
                                                                (η:=η)(r:=r)(Θ:= θ')(a:=η') in Hreduct.
             
             
         }



                               
         unfold CausCons in HCausCons. specialize (HCausCons r' a η').
         apply HCausCons; auto.

       -unfold CausCons. intros; rename η0 into η'; rename r0 into r'.
         assert (Ex-hbo a η'). admit.
         unfold CausCons in HCausCons. specialize (HCausCons r' a η').
         apply HCausCons; auto.