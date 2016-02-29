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

(*

Lemma HBO_to_HBO':forall (a b :Effect)(Θ:Store)(Σ: SessSoup)(Ex Ex':Exec)(ss:SessID)(ii:SeqNo) 
                             (opp:OperName)(r:ReplID),     [Θ |- Ex, <ss,ii,opp> ~r~> Ex', η] ->  Ex'-hbo a b -> Ex-hbo a b     .

*)




  
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


(*############################################################# Prove THIS!!!!!! ######################################################*)
Notation " '<<' A ',' B ',' C  '>>'  " := (mkSoup_Ing A B C)(at level 10).
Notation " OP '__' t " := (mkop_cls OP t) (at level 0).

Theorem Injection_Help : forall Σ0 Σ ss ii opp s i op τ0 τ oplist σ,
  (Σ0 ||| mkSoup_Ing ss ii (mkop_cls opp τ0 :: oplist)) =
  (Σ |||  mkSoup_Ing s i (mkop_cls op τ :: σ)) ->
                              ((Σ0 ||| << ss,ii+1,oplist>>) = (Σ ||| << s, i + 1, σ >>)) ->
                                                 σ=oplist /\ τ=τ0 /\ opp=op /\ i=ii /\ s=ss /\ Σ=Σ0 .
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
                     [[Ex,Θ,(Σ|||(mkSoup_Ing ss ii ((mkop_cls op τ)::σσ))) --η-->  Ex' ,Θ' , (Σ|||(mkSoup_Ing ss (ii+1) σσ)) ]]
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
        +SCase"EFFVIS". subst. rename Ex' into Ex. inversion H0.
         induction  (Σ ||| << s, i, (op) __ (τ) :: σ >> ) in H.
         injection H0.
         compute in H0.
         injection H0.

      
          compute in H0. 
   
         inversion H0.
u
         inversion H0.
         inversion H.
         unfold Models.admit.

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
         unfold Models. (**)
         inversion H8. subst.
         simpl. intros ef HA' HBO'. rename ef into a.
         assert ((E A' vis' so' sameobj')-hbo a η). intuition.
         apply Inversion_HBO_Help with (vis:=vis')(so:=so')(sameobj:=sameobj')(A:=A') in H.

         (*begin change*)
         destruct H.
         *
         destruct H as [c G]. unfold Rel_Union in G. inversion G.
         inversion H0.       
          generalize (H10 c η). intro. rewrite H3 in H1.
          inversion H1.  unfold CausCons in HCausCons. specialize (HCausCons r a c).
          inversion H9. apply HCausCons in H11. 
          specialize (H10 a η). rewrite H10.
          left. split. apply H11. reflexivity.
          assert ((E A vis so sameobj)-hbo a c) as HBO. admit.  (* PROOOOOOVE MEEEEEEE   *)
          apply HBO.
          apply CorrectFreshness in H8. compute in H8. inversion H9. inversion H11.
          apply H8 in H16. contradiction.
          
          assert ((θ r) c). apply H5. compute. apply first. compute in H1. apply H1.
          assert ((E A vis so sameobj)-hbo a c). admit. (* PROOOOOOVE MEEEEEEE   *)
          unfold CausCons in HCausCons. specialize (HCausCons r a c).
          assert (θ r a). apply HCausCons. apply H3. apply H9.
          specialize (H10 a η). rewrite H10.
          left. split. apply H11. reflexivity.

         * destruct H.  Focus 2. apply H.
           specialize (H10 a). rewrite H10. left. split.
           apply H5. compute. apply first. compute in H. apply H. reflexivity.

           
           



         *SSCase"Trivial".
          reflexivity.



        +SCase "[SC]".
         subst.  apply Injection_Help in H0. Focus 2. apply H1.
         intuition; subst; clear H1 H; rename ii into i; rename ss into s; rename oplist into σ.
         inversion H3.
         subst.
         unfold Models; 
         compute. intros a HA' HSame' .
         specialize (H12 a). apply H12 in HA'.
         destruct HA'.
         *SSCase"a∈A".
          remember (E A' vis' so' sameobj')-hbo as hbo'.
          (*
          assert ((hbo' a η)->(vis' a η) ). admit.
          assert ((hbo' η a)->(vis' η a) ). admit.
*)

          unfold Included in  H4. specialize (H4 a).
          simpl in H4. unfold In in H4. apply H4 in H.
          assert (vis' a η). rewrite H14. left. auto.
          left. left. apply H0.



         *SSCase"a=η".
         rewrite H. right. apply  Eff_Equi_refl.
Qed.         

              