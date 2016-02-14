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
Require Import Cases.
Import Config.
Import parameters.
Import Operational_Semantics.

(*********************************************************************************************************)
(*Lemma if Ex is well formeed, vis and so and hb are acyclic*)
(*********************************************************************************************************)
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

(*********************************************************************************************************)
(*********************************************************************************************************)
(*Lemma: if Ex is well fromed and reduces to Ex',    ===>     Ex'.vis  is acyclic*)
(*********************************************************************************************************)

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


(*********************************************************************************************************)
(*********************************************************************************************************)
(*Lemma: if Ex is well fromed and reduces to Ex' ===> Ex'.so  is acyclic*)
(*********************************************************************************************************)
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



(*********************************************************************************************************)
(*********************************************************************************************************)
(*Lemma: if Ex is well fromed and reduces to Ex' ===> Ex'.hb  is acyclic*)
(*********************************************************************************************************)
Lemma hb'_Acyclicity: forall (Θ: Store)(Ex Ex':Exec) (s:SessID) (i:SeqNo)(op:OperName)(η:Effect)(r:ReplID),
                                       {Θ|-Ex, <s,i,op> ~r~> Ex', η} -> (WF Ex) ->  (WF1 Ex').
Proof.
  intros Θ Ex Ex' s i op η r. intros H_reduct H_WF.
  (*Inversion on the reduction*)
  inversion H_reduct;
  clear H9 H1 H0 H H2 H5 s0 i0 op0 η0;rename H3 into  H_η; rename H4 into  H_η'; rename H7 into H_vis';
  rename H10 into H_so';rename H11 into H_sameobj';rename H6 into H_Exec; rename H8 into H_Exec'.


  (*************************************************Assertions that will be needed*)
  
  (*Trivial assertions*)
  assert ((Ex')-A = A')    as H_EX'A.      rewrite <- H_Exec'; auto.
  assert ((Ex')-vis = vis')as H_EX'vis.    rewrite <- H_Exec'; auto. 
  assert ((Ex')-so = so')  as H_EX'so.     rewrite <- H_Exec'; auto.
  assert ((Ex)-A = A)      as H_EXA.       rewrite <- H_Exec;  auto.
  assert ((Ex)-vis = vis)  as H_EXvis.     rewrite <- H_Exec;  auto. 
  assert ((Ex)-so = so)    as H_EXso.      rewrite <- H_Exec;  auto.
  assert (seq η' =  i - 1) as H_η'def.     specialize (H_η'  η'). intuition.

  (*ignore this->*)rename H_WF into temp; assert (WF Ex) as H_WF. exact temp.
  
  (*Acyclicity of vis, so and hb*)
  apply WellFormed_res1 in temp.
  inversion temp; inversion H0; clear H0; rename H into H_vis;rename H1 into H_so;rename H2 into H_hb; clear temp.

  (*Assert that the newly produced effect η, does not preceed other effects. Proof by an axiom *)
  assert ( forall (Θ: Store)(Ex Ex':Exec) (opk:op_key)(η:Effect)(r:ReplID),
                      {Θ|-Ex, opk ~r~> Ex', η} -> (forall e:Effect, Θ r e -> ~ Ex-so η e)) as H_newEff. apply SO_NewEff. 

  (*Assert if b is before c, and if (so a b), then (so a c)*)
  assert (forall (Ex:Exec)(a b c:Effect), (Ex-so a b)->(seq b)=(seq c)-1 ->(Ex-so a c)) as H_soRefl. apply SO_Seq.

  (*Assert if b's sequence number is plus one of a's, the (so a b) holds.*)
  assert (forall (Ex:Exec)(a b :Effect), seq a = seq b -1  -> Ex-so a b) as H_soDef. apply SO_SeqII.

  (*Claim from the Paper, H16 of the paper*)
  assert ((forall a:Effect,(Ex)-A a -> ~(Ex) -hb a a)-> (forall x y:Effect, ~(Ex-vis x y /\ Ex-so y x ))) as H16.
                          intros; apply PaperH8II.


                          
  (*****************************************3 equal assertions to the final goal  are stated:*)                          
  (*1*)
  assert (forall a:Effect, A' a -> ~ vis' a a) as H_EqualI.
  Case "Acyclicity of vis'". {
            rewrite <- H_EX'A; rewrite<-H_EX'vis.
            assert ({Θ|-Ex,< s, i, op >  ~r~> Ex', η} -> ((forall a:Effect, Ex'-A a -> ~ Ex'-vis a a))).
            apply Vis'_Acyclicity. exact H_WF.
            apply H. exact H_reduct. }

  (*2*)                           
  assert ( forall a : Effect, A' a -> ~ so' a a) as H_EqualII.
  Case "Acyclicity of so'". {
            rewrite <- H_EX'A. rewrite <- H_EX'so.
            assert ({Θ|-Ex,< s, i, op >  ~r~> Ex', η} -> ((forall a:Effect, Ex'-A a -> ~ Ex'-so a a))).
            apply So'_Acyclicity; exact H_WF.
            apply H. exact H_reduct. }

  (*3*)                          
  assert (forall (a b:Effect), A' a -> A' b -> ~((vis' a b)/\(so' b a))) as H_EqualIII. 
  Case "~((vis' a b)/\(so' b a))". {
            intros a b; intros H_eff H_eff'.
            unfold not. intros; inversion H; clear H.
            apply H_vis' in H0. apply H_so' in H1.
            (*Based on definitions of vis' and so', there are 6 cases deal with*)
            intuition.
            
            +SCase"(Θ r a)/\b=η AND (so b η')/\a=η".
                     apply Freshness in H_reduct. rewrite H7 in H0. contradiction.

            +SCase"(Θ r a)/\b=η AND b=η'/\a=η".
                     apply Freshness in H_reduct. rewrite H7 in H0. contradiction.

            +SCase"(Θ r a)/\b=η AND(so b a)".
                     rewrite H6 in H4. specialize (H_newEff Θ Ex Ex' <s,i,op> η r).
                     intuition; rename H7 into H_newEff.
                     specialize (H_newEff a ). rewrite  H_EXso in H_newEff.
                     auto.

            +SCase" (A a/\A b)/\(vis a b) AND a=η/\(so b η')".
                     specialize(H_soRefl Ex b η' η).
                     rewrite H_EXso in H_soRefl; rewrite H3 in H_soRefl; rewrite H_η'def in H_soRefl.
                     intuition. specialize (H1 a b). rewrite<- H8 in H10.  rewrite H_EXvis in H1; rewrite H_EXso in H1.
                     auto.


            +SCase"(A a/\A b)/\(vis a b) AND a=η/\b=η'".
                     specialize (H_soDef Ex  b a). rewrite H0 in H_soDef; rewrite H8 in H_soDef.
                     rewrite H3 in H_soDef; rewrite H_η'def in H_soDef. intuition.
                     specialize (H1 η η'). rewrite H_EXvis in H1. rewrite H8 in H6; rewrite H0 in H6.
                     auto.

            +SCase"(A a/\A b)/\(vis a b) AND so b a".
                    specialize (H1 a b). rewrite H_EXvis in H1; rewrite H_EXso in H1.
                    auto.
  }

  (* Now use previously proven assertions, to show WF1 of Ex'*)
  assert(forall (Ex:Exec), 
             (forall (a:Effect), Ex-A a -> ~ Ex-vis a a) ->
             (forall (a:Effect), Ex-A a -> ~ Ex-so  a a) ->
             (forall (a b:Effect),Ex-A a -> Ex-A b ->  ~((Ex-vis a b)/\ (Ex-so b a))) ->
             (forall (a:Effect),~(Ex-hb a a))).
  apply PaperH8III.
  specialize (H Ex'). rewrite H_EX'vis in H; rewrite H_EX'so in H; rewrite H_EX'A in H. intuition.
  unfold WF1. rewrite  H_Exec'. intros a H_final.
  unfold not. 
  specialize (H5 a).
  exact H5.

Qed.

