Require Import Cases.
Require Import Definitions.
Require Import Axioms.
Require Import Lemma5_Lemmas.
Require Import Lemma5.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Program.Tactics.
Require Import Operational_Semantics.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Lt.


(*-------------------------------------------------------------------------------------------------------*)
(*If hbo holds, then hb holds! *)
Lemma HBO_HB : forall(Ex:Exec)(a b:Effect), Ex-hbo a b -> Ex-hb a b.
Proof.
  intros Ex a b Hbo. induction Hbo.
  +Case"base case:".
   inversion H; try(unfold hb; apply t_step).
   right; apply H0 . left; apply H0.

  +Case"inductive step".
   apply t_trans with (y:=y). apply IHHbo1. apply IHHbo2.
Qed.  



(*-------------------------------------------------------------------------------------------------------*)
(* hbo(a,b) AND vis(b,c) Will Result in : hbo(a,c)*)
Lemma  HBO'_newEff_help : forall (Ex:Exec) (a b c:Effect),
                            Ex-hbo a b -> Ex-vis  b c -> Ex-hbo a c.
Proof.
  intros Ex a b c HBO VIS.
  apply t_trans with (y:= b). apply HBO.
  apply t_step. right. apply VIS.
Qed.


(*-------------------------------------------------------------------------------------------------------*)
(* In a reduction, if hbo(a,b) holds, then η is not equal to either a or b*)
Lemma HBO'_newEff: forall (Ex Ex':Exec)(a b η:Effect) (r:ReplID) (i:SeqNo)(s:SessID)(op:OperName)(θ:Store),
                     [ θ |- Ex, < s, i, op > ~ r ~> Ex', η] -> WF Ex -> Ex'-hbo a b ->
                     Ex'-A a -> Ex'-A b  ->~((a=η)/\ (b=η)).

Proof. intros Ex Ex' a b η r i s op θ Hreduct HWF HBO'  Ha Hb . 
       intro H.  inversion H.
       rewrite H0 in HBO'. rewrite H1 in HBO'.
       assert (WF Ex') as WF'. { apply Lemma5 in Hreduct. apply Hreduct. apply HWF. }
                               apply WellFormed_res1 in WF'.
       destruct_conjs. clear H2 H3; rename H4 into HBcyc. specialize (HBcyc η). 
       apply HBcyc.
       assert ((Ex') -A η \/ ~(Ex') -A η) as Hcomp. apply Soup_comp.
       inversion Hcomp. apply H2. apply WF_Relation with (a:=η)(b:=η)(r:=Ex'-hbo) in HBO'.
       inversion HBO'. apply Hbo_Domain in H3. apply H3. apply HBO_HB. apply HBO'.              
Qed.


(*-------------------------------------------------------------------------------------------------------*)
(*A trivial fact about natural numbers: Sn is not less than n! *)
Lemma triv_nat : forall (n:nat), ~(lt (S n) n).
Proof.
  intros n H.
  induction n as [|n'].
  +Case"Induction Base:".
   inversion H.
  +Case"Induction Step:".
   inversion H. apply IHn'. unfold lt. rewrite H1. apply le_n.
   subst.  unfold lt in H. apply le_S_n in H. apply le_lt_n_Sm in H.
   apply lt_S_n in H. intuition.
Qed.


(*-------------------------------------------------------------------------------------------------------*)
(*If E ~> E', then there is not a z, such that   hbo'(η,z) *)  
Lemma HBO'_HBO_help : forall (Ex Ex':Exec)(η:Effect) (r:ReplID) (i:SeqNo)(s:SessID)(op:OperName)(θ:Store),
                        [ θ |- Ex, < s, i, op > ~ r ~> Ex', η] ->
                        ~(exists z:Effect, Ex'-A z /\ Ex'-hbo η z).

Proof.
  intros Ex Ex' η r u s op θ H Hc.
  destruct Hc as [k G]. intuition. rename H0 into HAk. rename H1 into Hbo'.
  assert ( [ θ |- Ex, < s, u, op > ~ r ~> Ex', η]) as Hreduct. apply H.
  apply CorrectFreshness with (ex1:=Ex)(ex2:=Ex')(opk :=  < s, u, op >) (eff:=η) (r:=r) in H. rename H into Hfresh.  
  induction Hbo'.
  -Case"Induction Base".
   rename H into Htemp.
   inversion Htemp as [Hsoo'|Hvis'].
   +SCase"soo'".
    inversion Hsoo'; clear Hsoo'; clear Htemp; rename H into Hso'; rename H0 into Hsameobj'; rename x into η.
    inversion Hreduct; subst. rename H13 into Hi. simpl in Hso'. remember (E A vis so sameobj) as Ex;
      remember (E A' vis' so' sameobj') as Ex'. rename  H9 into H11.  rename H7 into H8.
    specialize (H11 η y). rewrite H11 in Hso'.
    inversion Hso'.
    *SSCase"new effect". inversion H.  clear H. rename H0 into Hso. subst y.
     inversion Hso. assert (seq η = u). intuition. assert (seq η'=u-1). specialize (H5 η'). intuition.
     replace so with Ex-so in H. rewrite  SO_Seq_General  in H. rewrite H0 in H. rewrite H1 in H.
     induction u. simpl in H. inversion H.
     simpl in H. rewrite <-  minus_n_O in H.  apply  triv_nat in  H. apply H.
     rewrite HeqEx. auto. subst. rename η' into η. specialize (H5 η). intuition.    
    *SSCase"Same as so". apply WF_Relation with (a:=η) (b:=y) (r:=so) in H. inversion H.
     replace so with Ex-so in H0. apply So_Domain in H0. contradiction.
     rewrite HeqEx. auto.  
   +SCase"vis'". clear Htemp. inversion Hreduct. subst. rename x into η.
    rename  H9 into H11.  rename H7 into H8.
    specialize (H8 η y). simpl in Hvis'. apply H8 in Hvis'.
    inversion Hvis'.
    *SSCase"θ r η /\ y = η". inversion H. apply Freshness with (r0:=r) in Hreduct; auto. 
    *SSCase"(A η /\ A y) /\ vis η y". apply CorrectFreshness in Hreduct. simpl in  Hreduct. inversion H.
     inversion H0. contradiction.
     
  -Case"Induction Step". rename x into  η.  intuition. apply H.
   assert ((Ex') -A y \/ ~(Ex') -A y) as Hcomp. apply Soup_comp. inversion Hcomp.
   apply H0. apply WF_Relation with (a:=η)(b:=y)(r:=Ex'-hbo) in Hbo'1 . inversion Hbo'1.
   apply Hbo_Domain in H2. contradiction.
   apply Hreduct. 
Qed.


(*-------------------------------------------------------------------------------------------------------*)
(*In a reduction, if x<>η and y<>η then:   hbo'(x,y) -> hbo(x,y)  *)
Lemma HBO'_HBO: forall (Ex Ex':Exec)(a b η:Effect) (r:ReplID) (i:SeqNo)(s:SessID)(op:OperName)(θ:Store),
                  [ θ |- Ex, < s, i, op > ~ r ~> Ex', η] -> WF Ex -> ~(b=η)-> Ex'-hbo a b -> Ex-hbo a b.
Proof.
  intros Ex Ex' a b η r i s op θ H HWF Hbη Hbo'.
  induction Hbo'.
  -Case"induction base".
   subst. inversion H0.
   inversion H1.
   apply t_step. left.
   +SCase"Proof from soo".
    unfold soo. split.
    *SSCase"Proof of so".
     inversion H. subst. specialize (H14 x y). apply H14 in H2.
     inversion H2. inversion H4.  contradiction. apply H4.
    *SSCase"Porof of saemobj".
     assert (~(x=η)).  intro.
     subst. inversion H. subst η0 op0 i0 s0. specialize (H14 η y). replace Ex'-so with so' in H2.
     rewrite H14 in H2. inversion H2. inversion H4. contradiction.
     replace so with Ex-so in H4. apply CorrectFreshness in H.
     apply WF_Relation with (a:=η)(b:=y)(r:=Ex-so) in H4.  inversion H4. apply So_Domain in H5.
     contradiction.
     rewrite<- H13. auto. rewrite<- H15. auto.                                                    
     apply WF_Relation with (a:=x)(b:=y)(r:=Ex'-so) in H2. inversion H2.
     apply So_Domain in H6.  apply So_Domain in H5. inversion H.
     subst η0 op0 i0 s0. assert (Ex-A x). specialize (H14 x). simpl in H5. subst.
     rewrite <- H14 in H5. simpl. inversion H5. apply H7. contradiction.
     assert (Ex-A y).  specialize (H14 y). simpl in H6. subst. rewrite <- H14 in H6.
     simpl. inversion H6. apply H8. contradiction.
     apply Sameobj_Def with (a:=x)(b:=y) in H.
     rewrite<-H16 in H. apply H. apply H7. apply H8.
   +SCase"Proof from vis".
    apply t_step. right. inversion H. subst. specialize (H10 x y). apply H10 in H1.
    inversion H1. inversion H2. contradiction. apply H2.
    
  -Case "induction step".
   apply t_trans with (y:=y).
   apply IHHbo'1; try (auto). intro.
   subst. apply  HBO'_HBO_help in H. apply H. exists z.
   split.
   assert (forall (Ex:Exec)(eff:Effect), (Ex-A eff)\/(~ Ex-A eff)) as Hcomp. apply Soup_comp.
   specialize (Hcomp Ex' z). inversion Hcomp.
   apply H0. apply WF_Relation with (r:=Ex'-hbo) (a:=η)(b:=z) in Hbo'2.
   inversion Hbo'2. apply Hbo_Domain in H2. contradiction. apply Hbo'2.
   apply IHHbo'2; try (auto). 
Qed.


(*-------------------------------------------------------------------------------------------------------*)
Lemma Inversion_HBO_Help: forall (Ex:Exec)(a b:Effect)(A: Exec_A)(vis so sameobj :Relation),
                            (Ex = (E A vis so sameobj))->
                            (Ex-hbo a b) -> (exists c, (Ex-hbo a c) /\ ((Ex-vis) ∪ (Ex-soo)) c b )\/ (((Ex-soo) ∪ (Ex-vis) ) a b) .
Proof.  
  intros Ex a b A vis so sameobj HExec. intro HBO.
  induction HBO.
  -Case"direct hbo".
   right. apply H.
  -Case"indirect hbo". 
   destruct IHHBO2.
   +SCase"left2".
    left. destruct H as [k G]. exists k. split.
    apply t_trans with (y:=y)(z:=k). apply HBO1.
    apply G. apply G.   
   +SCase"right2".
    left. exists y. split. apply HBO1. unfold Rel_Union. destruct H. auto. auto.
Qed.






