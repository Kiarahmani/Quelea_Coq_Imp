Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Add LoadPath "/Users/Kiarash/Desktop/Quelea Coq".
Require Import parametes_coq.
Require Import config_coq.
Require Import oper_semantic_coq.
Require Import axioms_coq.
Require Import Cases.

Import Config.
Import parameters.
Import Operational_Semantics.


(*Lemma if Ex is well formeed, vis and so and hb are acyclic*)
Lemma WellFormed_res1 : forall (Ex:Exec), (WF Ex) -> ((forall x:Effect, Ex-A x -> ~ Ex-vis x x) /\
                                                      (forall x:Effect, Ex-A x -> ~ Ex-so x x) /\
                                                      (forall x:Effect, Ex-A x -> ~ Ex-hb x x)).
Proof.
      intros Ex WF_H. split. 
      -Case "Acyclicity of vis". apply WFhelp in WF_H; inversion WF_H; clear H0 WF_H. (*Get WF1 from WF, WF1 is acyclicity of hb*)
                                 intros x Hx.
                                 unfold WF1 in H. specialize (H x). apply H in Hx. apply PaperH8. exact Hx. 
      -split. 
      Case "Acyclicity of so". { apply WFhelp in WF_H; inversion WF_H; clear H0 WF_H. 
                                 intros x Hx.                                         
                                 unfold WF1 in H. specialize (H x). apply H in Hx. apply PaperH8. exact Hx. }
      Case "Acyclicity of hb". { apply WFhelp in WF_H; inversion WF_H; clear H0 WF_H.
                                 unfold WF1 in H. 
                                 intros x. specialize (H x). exact H. }
Qed.
 

(*Lemma: if Ex is well fromed and reduces to Ex',    ===>     Ex'.vis  is acyclic*)
Lemma Vis'_Acyclicity :  forall (Θ: Store)(Ex Ex':Exec) (opk:op_key)(η:Effect)(r:ReplID),
                                      WF Ex -> {Θ|-Ex, opk ~r~> Ex', η} -> ((forall a:Effect, Ex'-A a -> ~ Ex'-vis a a)).
Proof.
    intros Θ Ex Ex' key η r; intros WF_H reduct_H. 
    apply WellFormed_res1 in WF_H. inversion WF_H; clear H0  WF_H.
    inversion reduct_H.
    unfold return_A. unfold return_vis. 
    intros a H_a. unfold not. intros vis'_H.
    specialize (H4 a a). apply H4 in vis'_H. inversion  vis'_H. 
    -Case "Θ r a /\ a = η ". { inversion H11. rewrite H13 in H12. apply Freshness in reduct_H. contradiction reduct_H. }
    -Case "(A a /\ A a) /\ vis a a". {specialize (H a). rewrite <- H7 in H. unfold return_A in H. unfold return_vis in H. 
                                                   inversion H11. inversion H12. apply H in H14. contradiction. }
Qed.
                                           

(*Lemma: if Ex is well fromed and reduces to Ex' ===> Ex'.so  is acyclic*)
Lemma So'_Acyclicity :  forall (Θ: Store)(Ex Ex':Exec) (opk:op_key)(η:Effect)(r:ReplID),
                                     WF Ex ->  {Θ|-Ex, opk ~r~> Ex', η} -> ((forall a:Effect, Ex'-A a -> ~ Ex'-so a a)). 
Proof. 
    intros Θ Ex Ex' key η r; intros WF_H reduct_H. 
    apply WellFormed_res1 in WF_H. inversion WF_H; inversion H0; clear H0 H H2  WF_H.
    inversion reduct_H.
    unfold return_A. unfold return_so. 
    intros a H_a. unfold not. intros so'_H.
    specialize (H5 a a). apply H5 in so'_H. inversion so'_H.
    -Case "(so a η' \/ a = η') /\ a = η". { inversion H11; inversion H12.
                                            +SCase"(so a η') /\ a=η ".
                                               rewrite H13 in H14. assert (so = Ex-so). rewrite <- H7; unfold return_so; reflexivity.
                                               rewrite H15 in H14. apply SessionOrder in H14.
                                               inversion H14. 
                                               assert (seq η = i0). intuition.
                                               assert (seq η' = i0-1). specialize (H2  η'). intuition.
                                               rewrite H19 in H17; rewrite H18 in H17. apply natSeq in H17. exact H17.
                                            +SCase"(a=η') /\ a=η ".
                                               rewrite H13 in H14; rewrite <- H14 in H2.
                                               assert (seq η = i0-1). specialize (H2 η). intuition.
                                               assert (seq η = i0). intuition.
                                               rewrite H16 in H15. apply Why_Coq in H15. exact H15. }
   -Case "so a a". { assert (Ex-A a \/ ~Ex-A a). apply Soup_comp. inversion H12.
                     +SCase"Ex-A a". specialize (H1 a). apply H1 in H13. rewrite <- H7 in H13; unfold return_so in H13. contradiction.
                     +SCase"~(Ex-A a)". apply Relation_Dom in H13. rewrite <- H7 in H13; unfold return_so in H13. contradiction. }

Qed.




