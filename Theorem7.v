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
Require Import oper_semantic_coq.
Require Import axioms_coq.
Require Import theorems_coq.
Require Import contract_definition.
Require Import contract_subs.
Require Import contract_Eval.
Require Import lemma5.
Require Import Stlc.
Require Import Imp.
Require Import Equiv.
Import STLC.
Import Config.
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







Lemma Inversion_HBO_Help: forall (Ex:Exec)(a b:Effect)(A: Exec_A)(vis so sameobj :Relation),
                            (Ex = (E A vis so sameobj))->
                            (Ex-hbo a b) -> exists c, (Ex-hbo a c) /\ (Ex-so c b)/\(Ex-vis c b) .
Proof.
intros Ex a b A vis so sameobj HExec. intro HBO.
induction HBO. rename x0 into x. rename y0 into y.
exists y. intuition. apply t_step. apply H. apply so_trans. apply vis_trans. 
destruct IHHBO2 as [k G]. exists k. intuition.
destruct IHHBO1 as [p G].
unfold hbo in G. intuition. unfold soo in H0. rewrite HExec in H0. compute in H0.


apply t_step. rewrite HExec. compute.

rewrite HExec in H0. unfold soo in H0. simpl in H0. inversion H0.
intuition. subst.
 right. 








(*############################################################# Prove THIS!!!!!! ######################################################*)
Notation " '<<' A ',' B ',' C  '>>'  " := (mkSoup_Ing A B C)(at level 10).
Notation " OP '__' t " := (mkop_cls OP t) (at level 0).
Notation " A '||' B " := (A +soup+ B). 

Theorem Injection_Help : forall Σ0 Σ ss ii opp s i op τ0 τ oplist σ,
  (Σ0 +soup+  mkSoup_Ing ss ii (mkop_cls opp τ0 :: oplist)) =
  (Σ +soup+  mkSoup_Ing s i (mkop_cls op τ :: σ)) ->
                              ((Σ0 || << ss,ii+1,oplist>>) = (Σ || << s, i + 1, σ >>)) ->
                                                 σ=oplist /\ τ=τ0 /\ opp=op /\ i=ii /\ s=ss /\ Σ=Σ0.
Proof. admit. Qed.



Definition Store_Contr (τ:ConsCls):contract_Contract:=
  match τ with
    |sc =>ALL  m (CONTR: ((PROP: Sameobj m η'')   #-->
                                         ((PROP: Vis m η'') #\/#
                                          (PROP: Vis η'' m) #\/#
                                          (PROP: Equi m η''))))
    |cc => ALL m (CONTR: ((PROP: Hbo m η'') #--> (PROP: Vis m η'')))
    |ec => ALL m (ALL n (CONTR: ((PROP: Hbo m n) #/\# (PROP: Vis n η'') #--> (PROP: Vis m η''))))
  end.
Notation " 'Ψ' " := Store_Contr.



Definition CausCons (Θ:Store)(Ex:Exec):= 
                                        forall(r: ReplID)(a η:Effect), ((Θ r) η)  -> ((Ex-hbo) a η) -> ((Θ r) a). 


Definition Models (Ex:Exec) (cont:contract_Contract) (eff:Effect) : Prop :=
  contract_Eval cont Ex eff (contract_free_number cont).
Notation " A '|=' B " := (Models A B) (at level 30).




Theorem theorem7 : forall  (Ex Ex':Exec)(Θ Θ':Store)(Σ: SessSoup)(τ: ConsCls)(ss:SessID)
                      (ii:SeqNo)(σσ:session)(η:Effect) (op: OperName),
                     (WF Ex) -> (CausCons Θ Ex) ->
                     [[Ex,Θ,(Σ+soup+(mkSoup_Ing ss ii ((mkop_cls op τ)::σσ))) --η-->  Ex' ,Θ' , (Σ+soup+(mkSoup_Ing ss (ii+1) σσ)) ]]
                     -> WF Ex'/\ (Ex'|=Store_Contr τ) η.

Proof. intros Ex Ex' θ θ' Σ τ s i σ η op.
       intros HWF HCausCons. intro H.
       split.
       -Case"Proof of Well-Formedness of Ex'". 
        destruct H.
                +exact HWF.
                +apply Lemma5 in H0. exact H0. exact HWF.
                +apply Lemma5 in H1. exact H1. exact HWF.
                +apply Lemma5 in H0. exact H0. exact HWF.
               
       -Case"Proof of E'|=Ψτ". 
         inversion H.
        +SCase"EFFVIS"; admit.

        +SCase"[EC]". 
         apply Injection_Help in H0. Focus 2. apply H1.
         intuition; subst; clear H H1 oplist Σ0; rename ii into i; rename θ' into θ; rename ss into s;rename H7 into H1.
         inversion H1; subst. compute.
          intros a Ha; intros b Hb. intros; intuition. 
         rewrite H9 in H5. intuition.
         Focus 2.
         apply CorrectFreshness in H1.
         compute in H1. apply H1 in H14. inversion H14.
         remember (E A vis so sameobj) as Ex.
         assert ((E A' vis' so' sameobj')-hbo a b) as HBO'. 
         intuition. clear H4.

         assert (Ex-hbo a b). unfold hbo. unfold hbo in HBO'. simpl in HBO'.
         unfold soo in HBO'. simpl in HBO'. unfold soo.  admit.
         (*******THIS NEEDS TO BE PROVEN******)

         unfold CausCons in HCausCons.
          
         assert ((θ r) a). specialize (HCausCons r a b). apply HCausCons.
         apply H5.
         apply H4.
         specialize (H9 a η). rewrite H9.
         left. split. apply H8. reflexivity.




        +SCase"[CC]". 
         apply Injection_Help in H0. Focus 2. apply H1. intuition.
         subst. clear H H1 oplist Σ0.
         rename ii into i; rename ss into s; rename θ' into θ. simpl in H5.
         unfold Models. inversion H8. subst.  
         compute.
         intros ef Hef Hbo' . rename ef into a. 
         inversion Hbo'. intuition.
         *SSCase"Inversion on hbo': case 1".
          subst.
          assert (θ r a). simpl in H5.
          assert ((rtrn_invs so' η)  a) . apply first.  apply H.
          unfold Included in H5. specialize (H5 a). apply H5 in H0. intuition.       
          specialize (H10 a η). rewrite H10. left. auto.
          
         *SSCase"Inversion on hbo': case 2". 
          subst. 






              