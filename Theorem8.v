Require Import Cases.
Require Import List.
Require Import Coq.Sets.Constructive_sets.
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
Require Import Theorem8_Lemmas.


Theorem Theorem8: forall Σ Ex Ex' θ θ' η τ Ing1 Ing2 ss ii σσ op, 
                    (Ing1 = (mkSoup_Ing ss ii ((mkop_cls op τ)::σσ))) ->
                    (Ing2 = (mkSoup_Ing ss (ii+1) σσ)) ->
                    (WF_union Σ Ing1) -> (WF_union Σ Ing2) ->
                    [[Ex,θ,(Σ||| Ing1) --τ,η-->  Ex' ,θ' , (Σ|||Ing2)]] ->
                    WF Ex -> CausCons θ Ex -> CausCons θ' Ex'.
Proof. intros  Σ Ex Ex' θ θ' η τ Ing1 Ing2 ss ii σσ op HIng1 HIng2. intros HWF_Union1 HWF_Union2.
       intros HProg HWF HCausCons.
       inversion HProg; subst.
       
       -Case"EffVis".
        rename Ex' into Ex. clear H. 
        unfold CausCons. intros; rename η0 into η'; rename r0 into r'.
        rename H into HAa. rename H0 into H. rename H1 into H0. rename H2 into H1. rename H3 into H2.
        rename H4 into H3. rename H5 into H4. rename H6 into H5. rename H7 into H6. 
        inversion H; subst.
        +destruct H7.  unfold CausCons in HCausCons. specialize (HCausCons r' a η').
         apply HCausCons; auto.
         
        +inversion H7. rewrite H7. rewrite<- H7 in H4. apply Theorem8_dom_help' in H4. subst r'.
         rewrite <- H8 in H5.
         rewrite Theorem8_beq_help in H5.
         inversion H5.
         (*1- η' is in θr*)
         subst. rewrite Theorem8_beq_help. apply Union_introl. compute.
         unfold CausCons in HCausCons. specialize (HCausCons r a η').
         apply HCausCons;auto. 
         (*2  η'=η*)
         inversion H4; subst; rename η' into η.
         destruct Ex as [A vis so sameobj]. 
         apply Inversion_HBO_Help with (A:=A) (vis:=vis) (so:=so) (sameobj:=sameobj)in H6.
         destruct H6 as [|Hsingle]. rename H6 into Hsteps.
         (***2.1 multiple steps hbo*)
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


       -Case"[EC]".
        unfold CausCons. intros; rename η0 into η'; rename r0 into r'; rename H6 into Hreduct.
        clear HWF_Union1 HWF_Union2 H HProg H0; rename H4 into HBO'; rename θ' into θ.
        unfold CausCons in HCausCons.
        apply HBO'_HBO with
        (Ex:=Ex)(Ex':= Ex')(s:=ss0)(i:=ii0)(op:=opp)(η:=η)(r:=r)(θ:=θ) in HBO'; auto.
        unfold CausCons in HCausCons. specialize (HCausCons r' a η').
        apply HCausCons; auto.
        apply WF_Relation with (r:=Ex-hbo)(a:=a)(b:=η') in HBO'. destruct HBO'.
        apply Hbo_Domain in H. apply H.
        intro. apply Freshness with (r0:=r') in Hreduct; auto. subst. contradiction.


       -Case"[CC]".
        unfold CausCons. intros; rename η0 into η'; rename r0 into r'; rename H7 into Hreduct.
        clear HWF_Union1 HWF_Union2 H HProg H0; rename H5 into HBO'; rename θ' into θ.
        unfold CausCons in HCausCons.
        apply HBO'_HBO with
        (Ex:=Ex)(Ex':= Ex')(s:=ss0)(i:=ii0)(op:=opp)(η:=η)(r:=r)(θ:=θ) in HBO'; auto.
        unfold CausCons in HCausCons. specialize (HCausCons r' a η').
        apply HCausCons; auto.
        apply WF_Relation with (r:=Ex-hbo)(a:=a)(b:=η') in HBO'. destruct HBO'.
        apply Hbo_Domain in H. apply H.
        intro. apply Freshness with (r0:=r') in Hreduct; auto. subst. contradiction.

       -Case"[SC]".
        clear HProg H HWF_Union1 HWF_Union2 H0. rename H2 into Hreduct.
        unfold CausCons. intros. rename r0 into r''. rename η0 into η''.
        generalize dependent (H7 r''). intro Hr''. assert ( r'' ∈ θ') as Hr'; auto.
        apply H7 in H0. inversion H0; clear H6. compute in H5. specialize (H5 η''). apply H5 in H1.
        inversion H1; try (compute in H5); try(inversion H5); subst; try(rename  η'' into η); try(rename r'' into r').
        
        +SCase"η'' in θ(r')".
         assert (Ex-A a \/ a=η).  inversion Hreduct; subst. specialize (H16 a). intuition.
         destruct H8.
         *specialize (HCausCons r' a η'').
          assert (r' ∈ θ). apply H4;auto.
          apply H0. apply Union_introl. apply HCausCons; auto.
          apply HBO'_HBO with (r:=r) (Ex:=Ex)(η:=η)(i:=ii0)(s:=ss0)(op:=opp)(θ:=θ) in H2; auto.
          intro; subst. apply Freshness with (r0:=r') in Hreduct;auto.
         *generalize dependent (H7 r'). intro Hrθ. apply Hrθ in Hr'. inversion Hr'.
          compute in H11. specialize (H11 a). apply H11. apply Union_intror. intuition.
          
        +SCase"η'' equal to η".
         inversion H6; subst; rename η'' into η.
         assert (Ex-A a \/ a=η).  inversion Hreduct; subst. specialize (H16 a). intuition. 
         assert (a<>η) as Haη. { intro; subst.  apply Lemma5 in Hreduct; auto. apply HBO_HB in H2.
                                      assert (~(Ex')-hb η η). apply WFhelp in Hreduct.
                                      destruct Hreduct. apply H9; auto. contradiction. }
         destruct H8.
                               
         *SSCase"Ex-A a".
          apply H10; auto.
         *SSCase"a=η". contradiction.

Qed.
