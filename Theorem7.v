Require Import Cases.
Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Tactics.
Require Import Definitions.
Require Import Operational_Semantics.
Require Import Axioms.
Require Import Lemma5_Lemmas.
Require Import Contracts_Definition.
Require Import Contracts_Subst.
Require Import Contracts_Evaluation.
Require Import Lemma5.
Require Import Theorem7_Lemmas.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Lt.


Definition Models (Ex:Exec)(cont:contract_Contract)(eff:Effect) : Prop :=
  contract_Eval cont Ex eff (contract_free_number cont).

Notation " A '|=' B " := (Models A B) (at level 30).





(**************************************************************************************************)
(*************************************** Theorem 7 of the Paper ***********************************)

Theorem theorem7 : forall  (Ex Ex':Exec)(Θ Θ':Store)(Σ: SessSoup)(τ: ConsCls)(ss:SessID)
                      (ii:SeqNo)(σσ:session)(η:Effect) (op: OperName)(Ing1 Ing2: Soup_Ing),
                     (WF Ex) -> (CausCons Θ Ex) ->
                     (Ing1 = (mkSoup_Ing ss ii ((mkop_cls op τ)::σσ))) ->
                     (Ing2 = (mkSoup_Ing ss (ii+1) σσ)) ->
                     (WF_union Σ Ing1) -> (WF_union Σ Ing2) ->
                     [[Ex,Θ,(Σ||| Ing1) --τ,η-->  Ex' ,Θ' , (Σ|||Ing2)]]        
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
        
        +SCase"EFFVIS".
         clear H2; clear H3. rename H4 into H2;  rename H5 into H3;
         rename H6 into H4; rename H7 into H5; rename H8 into H6; rename H9 into H7;
         rename H10 into H8; rename H11 into H9.
         subst. rename Ex' into Ex. inversion H0.
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
         apply Seq_Uniq in H10. omega.
         (*---*)
        +SCase"[EC]". subst. 
         intuition; subst; clear H H1; rename θ' into θ;rename H7 into H1.
         inversion H1; subst. compute.
          intros a Ha; intros b Hb. intros; intuition. 
          (**)
          assert ((E A' vis' so' sameobj')-hbo a b) as HBO'; intuition.
          remember (E A vis so sameobj) as Ex.
          assert ((θ r) b). {
          specialize (H9 b η). rewrite H9 in H6. inversion H6. apply H10.
          destruct H10 as [Htemp Hvisbη]; clear Htemp. apply WF_Relation with (r:=vis)(a:=b)(b:=η) in Hvisbη.
          destruct Hvisbη as [Htemp Hdomη]; clear Htemp.
          replace vis with Ex-vis in Hdomη.
          apply Vis_Domain in Hdomη. apply CorrectFreshness in H1. contradiction. rewrite HeqEx. auto. }

          assert ( ~ ( b = η))as Hneqbη. { intro. apply Freshness with (r0:=r) in H1;auto. rewrite <- H13 in H1. contradiction. }
          assert (Ex-hbo a b) as HBOab.  { apply HBO'_HBO with (a:=a)(b:=b) in H1.  apply H1. apply HWF. apply Hneqbη. apply HBO'. }
          assert ((θ r) a)    as Hainθ.  { unfold CausCons in HCausCons. specialize (HCausCons r a b).
                                          apply HCausCons. intuition.
                                          assert (Ex-A a \/ ~Ex-A a) as Hcomp. apply Soup_comp.
                                          destruct Hcomp; auto.
                                          apply WF_Relation with (a:=a)(b:=b)(r:=Ex-hbo) in HBOab.
                                          destruct HBOab. apply Hbo_Domain in H16. apply H16. intuition.
                                          apply H10. apply HBOab.  }
                                     
          specialize (H9 a η). rewrite H9. left. split. apply Hainθ. reflexivity.
                                            
         (*---*)                         
        +SCase"[CC]". subst.
         clear H H1.
         rename θ' into θ. simpl in H5.
         unfold Models. inversion H8. subst. rename H10 into HVis'.
         simpl. intros ef HA' HBO'. rename ef into a.
         assert ((E A' vis' so' sameobj')-hbo a η). intuition.
         apply Inversion_HBO_Help with (vis:=vis')(so:=so')(sameobj:=sameobj')(A:=A') in H.
         Focus 2. reflexivity.
         
         destruct H.
         *SSCase"exists c s.t. hbo a c and so\/vis c η".
          destruct H as [c G]. unfold Rel_Union in G. inversion G.
          clear G; rename H into HBO'ac;rename H1 into Hstepcη.
          inversion Hstepcη; clear Hstepcη.
          (*1*)assert ((θ r) c).  specialize (HVis' c η). rewrite HVis' in H.
          inversion H. apply H1.
          apply CorrectFreshness in H8. simpl in H8. inversion H1.
          inversion H2. contradiction.
          
          (*2*)assert ((E A vis so sameobj)-hbo a c).
          apply HBO'_HBO with (a:=a)(b:=c) in H8.  apply H8. 
          apply HWF. intro. apply Freshness with (r0:=r) in H8;auto. rewrite H2 in H1. contradiction.
          apply HBO'ac. 
          unfold CausCons in HCausCons. specialize (HCausCons r a c).
          assert ((θ r) a).
          apply HCausCons; auto.
          apply WF_Relation with (a:=a)(b:=c)(r:= (E A vis so sameobj) -hbo) in H2.
          destruct H2. apply Hbo_Domain in H2. apply H2.         
          specialize (HVis' a η). rewrite HVis'. auto.

          
          inversion H; clear H. rename H1 into H; clear H2.
          (*1*)assert ((θ r) c) as Hc.
          apply H5. compute. apply first. apply H.
          
          (*2*)assert ((E A vis so sameobj)-hbo a c) as Hbo.
          apply HBO'_HBO with (a:=a)(b:=c) in H8.  apply H8.
          apply HWF. intro. apply Freshness with (r0:=r) in H8;auto. rewrite H1 in Hc. contradiction.
          apply HBO'ac.

          specialize (HVis' a η). rewrite HVis'. left. split. Focus 2. reflexivity.
          unfold CausCons in HCausCons. specialize (HCausCons r a c). apply HCausCons; auto.
          apply WF_Relation with (a:=a)(b:=c)(r:= (E A vis so sameobj) -hbo) in Hbo.
          destruct Hbo. apply Hbo_Domain in H1. apply H1. 
          
         *SSCase"One step hbo".
          inversion H; clear H; rename H1 into H.
          inversion H; clear H; clear H2; rename H1 into H.
          specialize (HVis' a η). rewrite HVis'. left. split. Focus 2. reflexivity.
          compute in H5. specialize (H5 a). apply H5. apply first. apply H.         
          apply H.
          
          
         (*---*)                         
        +SCase "[SC]".
         subst. 
         intuition; subst; clear H0 H1. rename H3 into Hreduct.
         inversion Hreduct; subst. 
         unfold Models; compute. intros a HA' HSame' .
         specialize (H12 a). apply H12 in HA'.
         destruct HA'.
         *SSCase"a∈A".
          remember (E A' vis' so' sameobj')-hbo as hbo'.
          unfold Included in  H4. specialize (H4 a).
          simpl in H4. unfold In in H4. apply H4 in H0.
          assert (vis' a η). rewrite H13. left. auto.
          left. left. apply H1.

         *SSCase"a=η".
          rewrite H0. right. apply  Eff_Equi_refl.
Qed.         


