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
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Lt.

Import parameters.
Import Operational_Semantics.




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
                      (ii:SeqNo)(σσ:session)(η:Effect) (op: OperName)(Ing1 Ing2: Soup_Ing),
                     (WF Ex) -> (CausCons Θ Ex) ->
                     (Ing1 = (mkSoup_Ing ss ii ((mkop_cls op τ)::σσ))) ->
                     (Ing2 = (mkSoup_Ing ss (ii+1) σσ)) ->
                     (WF_union Σ Ing1) -> (WF_union Σ Ing2) ->
                     [[Ex,Θ,(Σ||| Ing1) --η-->  Ex' ,Θ' , (Σ|||Ing2)]]        
                     -> WF Ex'/\ (Ex'|=Store_Contr τ) η.

Proof. intros Ex Ex' θ θ' Σ τ s i σ η op. intros Ing1 Ing2. 
       intros HWF HCausCons. intros HIng1 HIng2. intros WFl WFr. intro H.
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
         remember (<< s, i, (op) __ (τ) :: σ >>) as Ing1.
         remember ( << s, i + 1, σ >>) as Ing2.
         assert ( forall (S S':SessSoup), S=S' -> forall (I:Soup_Ing), (In Soup_Ing S I -> In Soup_Ing S' I)) as Heq.
         apply Sess_Equal. specialize (Heq (Σ |||Ing1)  (Σ ||| Ing2 )).
         intuition. unfold In in H4.
         assert ((Σ ||| Ing1) Ing1). apply Union_intror. compute. intuition.
         specialize (H4 Ing1). apply H4 in H6.
         inversion H6. unfold WF_union in WFl. contradiction.
         inversion H7. 
         subst.
         apply Seq_Uniq in H10.
         assert (forall i:SeqNo, i=i-1\/i=i+1 -> False) as Triv. apply Why_Coq .
         specialize (Triv i).
         assert False. apply Triv. right. rewrite H10. reflexivity.
         contradiction.
        +SCase"[EC]". subst.
         apply Injection_Help' with (η:=η)(Ex':=Ex')(Ex:=Ex)(θ:=θ')(θ':=θ')in H0. Focus 2. apply H1.
         Focus 2. apply H.
         intuition; subst; clear H H1; rename θ' into θ;rename H7 into H1.
         inversion H1; subst. compute.
          intros a Ha; intros b Hb. intros; intuition. 
         rewrite H9 in H5. intuition.
         Focus 2. 
         apply CorrectFreshness in H1.
         compute in H1. apply H1 in H14. inversion H14.
         remember (E A vis so sameobj) as Ex.
         remember (E A' vis' so' sameobj') as Ex'.
         assert ((E A' vis' so' sameobj')-hbo a b) as HBO'; intuition; clear H4.
         assert ( ~ ( b = η)). intro. apply Freshness in H1. rewrite H4 in H5. contradiction.         
         assert (Ex-hbo a b) as HBOab.
         apply HBO'_HBO with (a:=a)(b:=b) in H1.  apply H1.
         apply HWF. apply H4.
         rewrite HeqEx'. apply HBO'.
         unfold CausCons in HCausCons.     
         assert ((θ r) a). specialize (HCausCons r a b). apply HCausCons.
         apply H5.
         apply HBOab.
         specialize (H9 a η). rewrite H9.
         left. split. apply H8. reflexivity.




        +SCase"[CC]". subst.
         apply Injection_Help_CC with (η:=η)(Ex':=Ex')(Ex:=Ex)(θ:=θ')(θ':=θ') in H0. Focus 2. apply H1.
         Focus 2. apply H.
         intuition.
         subst. clear H H1.
         rename θ' into θ. simpl in H5.
         unfold Models. (**)
         inversion H8. subst.
         simpl. intros ef HA' HBO'. rename ef into a.
         assert ((E A' vis' so' sameobj')-hbo a η). intuition.
         apply Inversion_HBO_Help with (vis:=vis')(so:=so')(sameobj:=sameobj')(A:=A') in H.
         Focus 2. reflexivity.
         
         destruct H.
         *SSCase"exists c s.t. hbo a c and so\/vis c η".
          destruct H as [c G]. unfold Rel_Union in G. inversion G.
          clear G; rename H into HBO'ac;rename H0 into Hstepcη.
          inversion Hstepcη; clear Hstepcη.
          (*1*)assert ((θ r) c).  specialize (H10 c η). rewrite H10 in H.
               inversion H. apply H0. apply CorrectFreshness in H8. inversion H0.
               simpl in H8. inversion H1. contradiction.
         
          (*2*)assert ((E A vis so sameobj)-hbo a c).
              apply HBO'_HBO with (a:=a)(b:=c) in H8.  apply H8.
              apply HWF. intro. apply Freshness  in H8. rewrite H1 in H0. contradiction.
              apply HBO'ac. 

         unfold CausCons in HCausCons. specialize (HCausCons r a c).
         assert ((θ r) a). auto. specialize (H10 a η). rewrite H10. auto.

  
         inversion H; clear H; rename H0 into H; clear H1.
         (*1*)assert ((θ r) c) as Hc.
              apply H5. compute. apply first. apply H.
         
         (*2*)assert ((E A vis so sameobj)-hbo a c) as Hbo.
              apply HBO'_HBO with (a:=a)(b:=c) in H8.  apply H8.
              apply HWF. intro. apply Freshness  in H8. rewrite H0 in Hc. contradiction.
              apply HBO'ac.

         specialize (H10 a η). rewrite H10. left. split. Focus 2. reflexivity.
         unfold CausCons in HCausCons. specialize (HCausCons r a c). apply HCausCons.
         apply Hc. apply Hbo.
                                                                         
         *SSCase"One step hbo".
         inversion H; clear H; rename H0 into H.
         inversion H; clear H; clear H1; rename H0 into H.
         specialize (H10 a η). rewrite H10. left. split. Focus 2. reflexivity.
         compute in H5. specialize (H5 a). apply H5. apply first. apply H.         
         apply H.
         
           

        +SCase "[SC]".
         subst.  apply Injection_Help' with (η:=η)(Ex':=Ex')(Ex:=Ex)(θ:=θ)(θ':=θ') in H0.
         Focus 2. apply H1. Focus 2. apply H.
         intuition; subst; clear H1 H.
         inversion H3.
         subst.
         unfold Models; 
         compute. intros a HA' HSame' .
         specialize (H12 a). apply H12 in HA'.
         destruct HA'.
         *SSCase"a∈A".
          remember (E A' vis' so' sameobj')-hbo as hbo'.
          unfold Included in  H4. specialize (H4 a).
          simpl in H4. unfold In in H4. apply H4 in H.
          assert (vis' a η). rewrite H14. left. auto.
          left. left. apply H0.

         *SSCase"a=η".
         rewrite H. right. apply  Eff_Equi_refl.
Qed.         

              