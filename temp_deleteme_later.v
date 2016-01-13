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

Import Config.
Import parameters.
Import Operational_Semantics.

(*Lemma: if Ex is well fromed and reduces to Ex',    ===>     Ex'.vis  is acyclic*)
Lemma Vis'_Acyclicity :  forall (Θ: Store)(Ex Ex':Exec) (opk:op_key)(η:Effect)(r:ReplID),
                                      WF Ex -> {Θ|-Ex, opk ~r~> Ex', η} -> ((forall a:Effect, Ex'-A a -> ~ Ex'-vis a a)).
Proof. 
    intuition. apply WFhelp in H. intuition. assert (forall x:Effect, Ex-A x -> ~ Ex-vis x x). unfold WF1 in H3.
    intros. generalize ( H3  x). intros.  assert (~(Ex) -hb x x). intuition. apply PaperH8 in H9. intuition. exact H7.
    clear H4 H5 H6 H8 H. inversion H0.  assert ((E A' vis' so' sameobj') = Ex'). intuition.   
    assert ((Ex')-A = A'). rewrite <- H15. auto. assert ((Ex')-vis = vis'). rewrite <- H15. auto. 
    assert ((Ex')-so = so'). rewrite <- H15. auto. rewrite H17 in H2. apply H8 in H2. intuition. 
    rewrite H23 in H2. apply Freshness in H0. auto. specialize (H7 a). assert (Ex-A = A). compute. 
    rewrite <- H11. auto. assert (Ex-vis = vis). compute. rewrite <- H11. auto. rewrite <- H2 in H21.
    rewrite <- H25 in H23. assert ((Ex) -vis a a -> False). apply H7. exact H21. auto.
Qed.


(*Lemma: if Ex is well fromed and reduces to Ex' ===> Ex'.so  is acyclic*)
Lemma So'_Acyclicity :  forall (Θ: Store)(Ex Ex':Exec) (opk:op_key)(η:Effect)(r:ReplID),
                                     WF Ex ->  {Θ|-Ex, opk ~r~> Ex', η} -> ((forall a:Effect, Ex'-A a -> ~ Ex'-so a a)). 
Proof. 
    intuition. apply WFhelp in H. intuition. assert (forall x:Effect, Ex-A x -> ~ Ex-so x x). unfold WF1 in H3.
    intros. generalize ( H3  x). intros.  assert (~(Ex) -hb x x). intuition. apply PaperH8 in H9. intuition. exact H7.
    clear H4 H5 H6 H8 H. 

    inversion H0. 
    assert ((E A vis so sameobj) = Ex). intuition. 
    assert ((Ex)-A = A). rewrite <- H15. auto. 
    assert ((Ex)-vis = vis). rewrite <- H15. auto. 
    assert ((Ex)-so = so). rewrite <- H15. auto. 
    assert ((E A' vis' so' sameobj') = Ex'). intuition. 
    assert ((Ex')-A = A'). rewrite <- H19. auto. 
    assert ((Ex')-vis = vis'). rewrite <- H19. auto. 
    assert ((Ex')-so = so'). rewrite <- H19. auto. rewrite  H22 in H2. 
    rewrite H9 in H2. intuition.  rewrite H27 in H25.  rewrite <- H18 in H25. apply SessionOrder in H25. intuition.  
    assert (η.(seq)=i0). auto. rewrite H25 in H28. clear H25. assert (seq η' = i0-1). apply H5. auto. rewrite H25 in H28. 
    apply natSeq in H28. auto. rewrite H27 in H25. rewrite <- H25 in H5. assert (η.(seq)=i0-1). apply H5. auto. 
    assert (η.(seq)=i0). intuition. rewrite H28 in H2. apply Why_Coq in H2. auto.



    rewrite  H18 in H7. rewrite H16 in H7. 
    rewrite H20 in H1. apply H6 in H1. intuition. specialize (H7 a). intuition. assert ((A a) \/~(A a)). rewrite <- H16. 
    apply Soup_comp. intuition. rewrite H2 in H27. rewrite H2 in H25. specialize (H7 η). intuition.  rewrite <- H16 in H27.
    apply Relation_Dom in H27. rewrite H18 in H27. intuition. 
Qed.