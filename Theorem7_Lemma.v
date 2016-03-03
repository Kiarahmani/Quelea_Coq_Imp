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
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Lt.
Import parameters.
Import Operational_Semantics.

Definition m:EffVar := effvar "m".
Definition n:EffVar :=effvar "n".
Infix " '#-->' " := contract_prop_implication (at level 80).
Infix " '#\/#' " := contract_prop_disjunction (at level 70).
Infix " '#/\#' " := contract_prop_conjunction (at level 60).
Notation " 'Sameobj' " := contract_sameobj.
Notation " 'Vis' " := contract_vis.
Notation " 'Equi' " := contract_equi.
Notation " 'PROP:'  ":= contract_prop_varvar (at level 90).
Notation " 'CONTR:'  ":=contract_free_cons (at level 95).
Notation " 'ALL'  ":=(contract_untyped_cons) (at level 96).


(*if hbo holds, then hb holds! *)
Lemma HBO_HB : forall(Ex:Exec)(a b:Effect), Ex-hbo a b -> Ex-hb a b.
Proof.
  intros Ex a b Hbo. induction Hbo.
  +Case"base case:".
   inversion H; try(unfold hb; apply t_step).
                right; apply H0 . left; apply H0.

  +Case"inductive step".
   apply t_trans with (y:=y). apply IHHbo1. apply IHHbo2.
Qed.  


(* hbo(a,b) AND vis(b,c) WILL RESULT IN : hbo(a,c)   *)
Lemma  HBO'_newEff_help : forall (Ex:Exec) (a b c:Effect),
                            Ex-hbo a b -> Ex-vis  b c -> Ex-hbo a c.
Proof.
  intros Ex a b c HBO VIS.
  apply t_trans with (y:= b).
  apply HBO.
  apply t_step. right.  apply VIS.
Qed.



(* if hbo(a,b) holds, then η is not equal to either a or b   *)
Lemma HBO'_newEff: forall (Ex Ex':Exec)(a b η:Effect) (r:ReplID) (i:SeqNo)(s:SessID)(op:OperName)(θ:Store),
                     [ θ |- Ex, < s, i, op > ~ r ~> Ex', η] -> WF Ex ->
                     Ex'-hbo a η -> Ex'-A a -> Ex'-A b ->  Ex'-hbo b η  ->(~(a=η))/\ (~(b=η)).
Proof. intros Ex Ex' a b η r i s op θ H HWF HBOa Ha Hb HBOb. 
       split.   
         intro Haη. rewrite <- Haη in HBOa. 
         assert (WF Ex') as WF'. { apply Lemma5 in H. apply H. apply HWF. }
         apply WellFormed_res1 in WF'.
         destruct_conjs. clear H0 H1; rename H2 into HBcyc. specialize (HBcyc a). 
         apply HBcyc. apply Ha. apply HBO_HB. apply HBOa.
        
         intro Hbη. rewrite <- Hbη in HBOb. 
         assert (WF Ex') as WF'. { apply Lemma5 in H. apply H. apply HWF. }
         apply WellFormed_res1 in WF'.
         destruct_conjs. clear H0 H1; rename H2 into HBcyc. specialize (HBcyc b). 
         apply HBcyc. apply Hb. apply HBO_HB. apply HBOb.
 Qed.





Lemma triv_nat : forall (n:nat), ~(lt (S n) n).
  Proof.
    intro n.
    intro.
    induction n as [|n'].
    inversion H.
    inversion H.
    apply IHn'. unfold lt. rewrite H1. apply le_n.
    subst.  unfold lt in H. apply le_S_n in H. apply le_lt_n_Sm in H.
    apply lt_S_n in H. intuition.
Qed.
    
Lemma HBO'_HBO_help : forall (Ex Ex':Exec)(η:Effect) (r:ReplID) (i:SeqNo)(s:SessID)(op:OperName)(θ:Store),
                        [ θ |- Ex, < s, i, op > ~ r ~> Ex', η] ->
                        ~(exists z:Effect, Ex'-A z /\ Ex'-hbo η z).
                     
Proof.
  intros Ex Ex' η r u s op θ H.
  intro Hc.
  destruct Hc as [k G].
  intuition. rename H0 into HAk. rename H1 into Hbo'.
  assert ( [ θ |- Ex, < s, u, op > ~ r ~> Ex', η]) as Hreduct. apply H.
  apply CorrectFreshness with (ex1:=Ex)(ex2:=Ex')(opk :=  < s, u, op >) (eff:=η) (r:=r) in H. rename H into Hfresh.  
  induction Hbo'.

  -Case"Induction Base".
   rename H into Htemp.
   inversion Htemp as [Hsoo'|Hvis'].
   +SCase"soo'".
    inversion Hsoo'; clear Hsoo'; clear Htemp; rename H into Hso'; rename H0 into Hsameobj'; rename x into η.
    inversion Hreduct; subst. simpl in Hso'. remember (E A vis so sameobj) as Ex; remember (E A' vis' so' sameobj') as Ex'.
    specialize (H11 η y). rewrite H11 in Hso'.
    inversion Hso'.
    *SSCase"new effect". inversion H.  clear H. rename H0 into Hso. subst y.
     inversion Hso. assert (seq η = u). intuition. assert (seq η'=u-1). specialize (H5 η'). intuition.
     replace so with Ex-so in H. rewrite  SO_Seq_General  in H. rewrite H0 in H. rewrite H1 in H.
     induction u. simpl in H. inversion H.
     simpl in H. rewrite <-  minus_n_O in H.  apply  triv_nat in  H. apply H.
     rewrite HeqEx. auto.
     subst. rename η' into η. specialize (H5 η). intuition.    
    *SSCase"Same as so". apply WF_Relation with (a:=η) (b:=y) (r:=so) in H. inversion H.
     replace so with Ex-so in H0. apply So_Domain in H0. contradiction.
     rewrite HeqEx. auto.
    
   +SCase"vis'". clear Htemp. inversion Hreduct. subst. rename x into η.
    specialize (H8 η y). simpl in Hvis'. apply H8 in Hvis'.
    inversion Hvis'.
    *SSCase"θ r η /\ y = η". inversion H. apply Freshness in Hreduct. contradiction.
    *SSCase"(A η /\ A y) /\ vis η y". apply CorrectFreshness in Hreduct. simpl in  Hreduct. inversion H.
     inversion H0. contradiction.
     
  -Case"Induction Step". rename x into  η.  intuition. apply H.
   assert ((Ex') -A y \/ ~(Ex') -A y) as Hcomp. apply Soup_comp. inversion Hcomp.
   apply H0. apply WF_Relation with (a:=η)(b:=y)(r:=Ex'-hbo) in Hbo'1 . inversion Hbo'1.
   apply Hbo_Domain in H2. contradiction.
   apply Hreduct. 
Qed.


Lemma HBO'_HBO: forall (Ex Ex':Exec)(a b η:Effect) (r:ReplID) (i:SeqNo)(s:SessID)(op:OperName)(θ:Store),
                  [ θ |- Ex, < s, i, op > ~ r ~> Ex', η] -> WF Ex -> (~(a=η)) -> (~(b=η))-> Ex'-hbo a b -> Ex-hbo a b.
Proof.
  intros Ex Ex' a b η r i s op θ H HWF Haη Hbη Hbo'.
  induction Hbo'.
  Case"induction base".
    subst. inversion H0.
    inversion H1.
    apply t_step. left. unfold soo. split. {
                        inversion H. subst. specialize (H16 x y). apply H16 in H2.
                        inversion H2. inversion H4.  contradiction. apply H4. }
                             { admit. }
    apply t_step. right. inversion H. subst. specialize (H11 x y). apply H11 in H1.
    inversion H1. inversion H2. contradiction. apply H2.
    

    
  Case "induction step".
    apply t_trans with (y:=y).
    apply IHHbo'1; try (auto). intro.
    subst. apply  HBO'_HBO_help in H. apply H. exists z.
    split.
    assert (forall (Ex:Exec)(eff:Effect), (Ex-A eff)\/(~ Ex-A eff)) as Hcomp. apply Soup_comp.
    specialize (Hcomp Ex' z). inversion Hcomp.
    apply H0. apply WF_Relation with (r:=Ex'-hbo) (a:=η)(b:=z) in Hbo'2.
    inversion Hbo'2. apply Hbo_Domain in H2. contradiction. apply Hbo'2.

    apply IHHbo'2; try (auto). intro.
    subst. apply  HBO'_HBO_help in H. apply H. exists z.
    split.
    assert (forall (Ex:Exec)(eff:Effect), (Ex-A eff)\/(~ Ex-A eff)) as Hcomp. apply Soup_comp.
    specialize (Hcomp Ex' z). inversion Hcomp.
    apply H0. apply WF_Relation with (r:=Ex'-hbo) (a:=η)(b:=z) in Hbo'2.
    inversion Hbo'2. apply Hbo_Domain in H2. contradiction. apply Hbo'2.
Qed.


  
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
   left.
   destruct H as [k G]. exists k. split.
   apply t_trans with (y:=y)(z:=k). apply HBO1.
   apply G. apply G.
   
 +SCase"right2".
   left. 
   exists y. split. apply HBO1. unfold Rel_Union. destruct H. auto. auto.
Qed.


(*###################### Prove THIS!!!!!! ##########################*)
Notation " '<<' A ',' B ',' C  '>>'  " := (mkSoup_Ing A B C)(at level 10).
Notation " OP '__' t " := (mkop_cls OP t) (at level 0).

Theorem Injection_Help : forall Σ0 Σ ss ii opp s i op τ0 τ oplist σ,
  (Σ0 ||| mkSoup_Ing ss ii (mkop_cls opp τ0 :: oplist)) =
  (Σ |||  mkSoup_Ing s i (mkop_cls op τ :: σ)) ->
                              ((Σ0 ||| << ss,ii+1,oplist>>) = (Σ ||| << s, i + 1, σ >>)) ->
                                                 σ=oplist /\ τ=τ0 /\ opp=op /\ i=ii /\ s=ss /\ Σ=Σ0 .
Proof. admit. Qed.