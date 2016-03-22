Require Import Definitions.
Require Import Operational_Semantics.
Require Import Axioms.
Require Import Cases.






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
                                      WF Ex -> [Θ|-Ex, opk ~r~> Ex', η] -> ((forall a:Effect, Ex'-A a -> ~ Ex'-vis a a)).
Proof.
    intros Θ Ex Ex' key η r; intros WF_H reduct_H. 
    apply WellFormed_res1 in WF_H. inversion WF_H; clear H0  WF_H.
    inversion reduct_H. rename H8 into Hi; rename H9 into H8; rename H10 into H9; rename H11 into H10;
    rename H12 into H11.
    unfold return_A. unfold return_vis. 
    intros a H_a. unfold not. intros vis'_H.
    specialize (H5 a a). apply H5 in vis'_H. inversion  vis'_H. 
    -Case "Θ r a /\ a = η ". { inversion H12. rewrite H14 in H13. apply Freshness with (r0:=r) in reduct_H. contradiction reduct_H. apply H0. }
    -Case "(A a /\ A a) /\ vis a a". {specialize (H a). rewrite <- H8 in H. unfold return_A in H. unfold return_vis in H. 
                                                   inversion H12. inversion H13. apply H in H15. contradiction. }
Qed.


(*********************************************************************************************************)
(*********************************************************************************************************)
(*Lemma: if Ex is well fromed and reduces to Ex' ===> Ex'.so  is acyclic*)
(*********************************************************************************************************)
Lemma So'_Acyclicity :  forall (Θ: Store)(Ex Ex':Exec) (opk:op_key)(η:Effect)(r:ReplID),
                                     WF Ex ->  [Θ|-Ex, opk ~r~> Ex', η] -> ((forall a:Effect, Ex'-A a -> ~ Ex'-so a a)). 
Proof. 
    intros Θ Ex Ex' key η r; intros WF_H reduct_H. 
    apply WellFormed_res1 in WF_H. inversion WF_H; inversion H0; clear H0 H H2  WF_H.
    inversion reduct_H. rename H8 into Hi; rename H9 into H8; rename H10 into H9; rename H11 into H10;
    rename H12 into H11.
    unfold return_A. unfold return_so. 
    intros a H_a. unfold not. intros so'_H. 
    specialize (H6 a a). apply H6 in so'_H. inversion so'_H.
    -Case "(so a η' \/ a = η') /\ a = η". { inversion H12; inversion H13.
                                            +SCase"(so a η') /\ a=η ".
                                               rewrite H14 in H15. assert (so = Ex-so). rewrite <- H8; unfold return_so; reflexivity.
                                               rewrite H16 in H15. apply SessionOrder in H15.
                                               inversion H15. 
                                               assert (seq η = i). intuition.
                                               assert (seq η' = i-1). specialize (H3  η'). intuition.
                                               rewrite H20 in H18; rewrite H19 in H18. apply natSeq in H18. exact H18.
                                            +SCase"(a=η') /\ a=η ".
                                               rewrite H14 in H15; rewrite <- H15 in H3.
                                               assert (seq η = i-1). specialize (H3 η). intuition.
                                               assert (seq η = i). intuition.
                                               rewrite H17 in H16.
                                               apply  Eneq_nat_cont with (i:=i); auto. }
   -Case "so a a". { assert (Ex-A a \/ ~Ex-A a). apply Soup_comp. inversion H13.
                +SCase"Ex-A a". specialize (H1 a). apply H1 in H14. rewrite <- H8 in H14; unfold return_so in H14. contradiction.
                +SCase"~(Ex-A a)". apply Relation_Dom in H14. rewrite <- H8 in H14; unfold return_so in H14. contradiction. }
Qed.



(*********************************************************************************************************)
(*********************************************************************************************************)
(*Lemma: if Ex is well fromed and reduces to Ex' ===> Ex'.hb  is acyclic*)
(*********************************************************************************************************)
Lemma hb'_Acyclicity: forall (Θ: Store)(Ex Ex':Exec) (s:SessID) (i:SeqNo)(op:OperName)(η:Effect)(r:ReplID),
                                       [Θ|-Ex, <s,i,op> ~r~> Ex', η] -> (WF Ex) ->  (WF1 Ex').
Proof.
  intros Θ Ex Ex' s i op η r. intros H_reduct H_WF.
  (*Inversion on the reduction*)
  inversion H_reduct.  subst. rename H13 into Hi.
  rename H4 into  H_η; rename H5 into  H_η'; rename H7 into H_vis';
  rename H9 into H_so';rename H12 into H_sameobj'.
  remember (E A' vis' so' sameobj') as Ex'.  remember (E A vis so sameobj) as Ex.
  rename HeqEx into H_Exec. rename HeqEx' into H_Exec'.


  (*************************************************Assertions that will be needed*)
  
  (*Trivial assertions*)
  assert ((Ex')-A = A')    as H_EX'A.      rewrite  H_Exec'; auto.
  assert ((Ex')-vis = vis')as H_EX'vis.    rewrite  H_Exec'; auto. 
  assert ((Ex')-so = so')  as H_EX'so.     rewrite  H_Exec'; auto.
  assert ((Ex)-A = A)      as H_EXA.       rewrite  H_Exec;  auto.
  assert ((Ex)-vis = vis)  as H_EXvis.     rewrite  H_Exec;  auto. 
  assert ((Ex)-so = so)    as H_EXso.      rewrite  H_Exec;  auto.
  assert (seq η' =  i - 1) as H_η'def.     specialize (H_η'  η'). intuition.

  (*ignore this->*)rename H_WF into temp; assert (WF Ex) as H_WF. exact temp.
  
  (*Acyclicity of vis, so and hb*)
  apply WellFormed_res1 in temp.
  inversion temp; inversion H0; clear H0; rename H into H_vis;rename H1 into H_so;rename H2 into H_hb; clear temp.

  (*Assert that the newly produced effect η, does not preceed other effects. Proof by an axiom *)
  assert ( forall (Θ: Store)(Ex Ex':Exec) (opk:op_key)(η:Effect)(r:ReplID),
                      [Θ|-Ex, opk ~r~> Ex', η] -> (forall e:Effect, Θ r e -> ~ Ex-so η e)) as H_newEff. apply SO_NewEff. 

  (*Assert if b is before c, and if (so a b), then (so a c)*)
  assert (forall (Ex:Exec)(a b c:Effect), (Ex-so a b)->(seq b)=(seq c)-1 ->(Ex-so a c)) as H_soRefl. apply SO_Seq.

  (*Assert if b's sequence number is plus one of a's, the (so a b) holds.*)
  assert (forall (Ex:Exec)(a b :Effect),(seq b>0)-> seq a = seq b -1  -> Ex-so a b) as H_soDef. apply SO_SeqII';auto.

  (*Claim from the Paper, H16 of the paper*)
  assert ((forall a:Effect,(Ex)-A a -> ~(Ex) -hb a a)-> (forall x y:Effect, ~(Ex-vis x y /\ Ex-so y x ))) as H16.
                          intros; apply PaperH8II.


                          
  (*****************************************3 equal assertions to the final goal  are stated:*)                          
  (*1*)
  assert (forall a:Effect, A' a -> ~ vis' a a) as H_EqualI.
  Case "Acyclicity of vis'". {
            rewrite <- H_EX'A; rewrite<-H_EX'vis.
            assert ([Θ|-Ex,< s, i, op >  ~r~> Ex', η] -> ((forall a:Effect, Ex'-A a -> ~ Ex'-vis a a))).
            apply Vis'_Acyclicity. exact H_WF.
            apply H. exact H_reduct. }

  (*2*)                           
  assert ( forall a : Effect, A' a -> ~ so' a a) as H_EqualII.
  Case "Acyclicity of so'". {
            rewrite <- H_EX'A. rewrite <- H_EX'so.
            assert ([Θ|-Ex,< s, i, op >  ~r~> Ex', η] -> ((forall a:Effect, Ex'-A a -> ~ Ex'-so a a))).
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
                     apply Freshness with (r0:=r) in H_reduct; auto. rewrite H9 in H0. contradiction.

            +SCase"(Θ r a)/\b=η AND b=η'/\a=η".
                     apply Freshness with (r0:=r) in H_reduct; auto. rewrite H9 in H0. contradiction.

            +SCase"(Θ r a)/\b=η AND(so b a)".
                     rewrite H8 in H5. specialize (H_newEff Θ Ex Ex' <s,i,op> η r).
                     intuition; rename H9 into H_newEff.
                     specialize (H_newEff a ). rewrite  H_EXso in H_newEff.
                     auto.

            +SCase" (A a/\A b)/\(vis a b) AND a=η/\(so b η')".
                     specialize(H_soRefl Ex b η' η).
                     rewrite H_EXso in H_soRefl; rewrite H4 in H_soRefl; rewrite H_η'def in H_soRefl.
                     intuition. specialize (H1 a b). rewrite<- H10 in H12.  rewrite H_EXvis in H1; rewrite H_EXso in H1.
                     auto.


            +SCase"(A a/\A b)/\(vis a b) AND a=η/\b=η'".
                     specialize (H_soDef Ex  b a). rewrite H0 in H_soDef; rewrite H10 in H_soDef.
                     rewrite H4 in H_soDef; rewrite H_η'def in H_soDef. intuition.
                     specialize (H1 η η'). rewrite H_EXvis in H1. rewrite H10 in H8; rewrite H0 in H8.
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
  specialize (H7 a). rewrite <- H_Exec'.
  exact H7.

Qed.
 
