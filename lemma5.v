Require Import case_coq.
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
Require Import theorems_coq.
Import Config.
Import parameters.
Import Operational_Semantics.

(**************************************************************************************************)
(*****************************************Lemma 5 of the Paper *******************************)

Theorem Lemma5: forall (Θ: Store)(Ex Ex':Exec) (s:SessID) (i:SeqNo)(op:OperName)(η:Effect)(r:ReplID),
                                       {Θ|-Ex, <s,i,op> ~r~> Ex', η} -> (WF Ex) -> (WF Ex').

Proof. intuition. apply WFhelp in H0. intuition.
(*---------------------------------------------Paper H8*) (*3 equal statements to acyclicity of hb *)
(*H14*) assert (forall eff,~ (Ex-hb eff eff)-> (forall x:Effect, Ex-A x -> ~ Ex-vis x x)).
                          unfold WF1 in H1. intros. specialize (H1 x). intuition. apply PaperH8 in H9. intuition.
(*H15*) assert (forall eff,~ (Ex-hb eff eff)-> (forall x:Effect, Ex-A x -> ~ Ex-so x x)).
                          unfold WF1 in H1. intros. specialize (H1 x). intuition. apply PaperH8 in H10. intuition.
(*H16*) assert (forall a:Effect, ~(Ex) -hb a a -> (forall x y:Effect, (*(Ex-A x)->(Ex-A y)->*) ~(Ex-vis x y /\ Ex-so y x ))).
                          intros. apply PaperH8II. 

(*Facts that will be needed*)
inversion H.
assert ((Ex')-A = A'). rewrite <- H18. auto.
assert ((Ex')-vis = vis'). rewrite <- H18. auto. 
assert ((Ex')-so = so'). rewrite <- H18. auto.

assert ((Ex)-A = A). rewrite <- H16. auto.
assert ((Ex)-vis = vis). rewrite <- H16. auto. 
assert ((Ex)-so = so). rewrite <- H16. auto.
assert ( forall (Θ: Store)(Ex Ex':Exec) (opk:op_key)(η:Effect)(r:ReplID),
                      {Θ|-Ex, opk ~r~> Ex', η} -> (forall a:Effect, Θ r a -> ~ Ex-so η a)). apply SO_NewEff. 
assert (forall (Ex:Exec)(a b c:Effect), Ex-so a b -> seq b = seq c - 1 -> Ex-so a c). apply SO_Seq.
assert (forall (Ex:Exec)(a b :Effect), seq a = seq b -1  -> Ex-so a b). apply SO_SeqII.
assert (seq η' =  i0 - 1). specialize (H14 η'). intuition.
assert  (forall a : Effect,((Ex)-A a -> (Ex) -hb a a -> False)). intuition. 

(*--------------------------------------------Paper H8*) (*Break the goal into 6 subgoals equal to it*)
apply FW. intuition. 


(*--------------------------------------------------------Proof of WF1 =  acyclicity of hb' *)(*3 Equal statements are proved instead*)
(*H17 = ~vis' a a *) 
Case "Prooving acyclicity of vis'".
assert (forall a:Effect, A' a -> ~ vis' a a). rewrite <- H23. rewrite <- H22. 
assert ({Θ|-Ex,< s0, i0, op0 >  ~r~> Ex', η} -> ((forall a:Effect, Ex'-A a -> ~ Ex'-vis a a))). apply Vis'_Acyclicity. 
apply FW;auto. intuition.

(*H18 = ~so' a a*)
assert ( forall a : Effect, A' a -> ~ so' a a). rewrite <- H24. rewrite <- H22.  
assert ({Θ|-Ex,< s0, i0, op0 >  ~r~> Ex', η} -> ((forall a:Effect, Ex'-A a -> ~ Ex'-so a a))). apply So'_Acyclicity.
apply FW;auto. intuition. 

(*H19 = ~((vis' a b)/\(so' b a)) *)
assert (forall (a b:Effect), A' a -> A' b -> ~((vis' a b)/\(so' b a))). 
intuition. apply H17 in H41. apply H20 in H42. intuition.
    (*Based on definitions of vis' and so', there are 6 subgoals to prove*)  
    (*Case 1*) apply Freshness in H. rewrite H44 in H41. auto.
    (*Case 2*) rewrite H44 in H41. apply Freshness in H. auto.
    (*Case 3*) rewrite H43 in H40. specialize (H28 Θ Ex Ex' < s0, i0, op0 >  η r). intuition. specialize (H42 a). rewrite H27 in H42. intuition.
    (*Case 4*) specialize (H29 Ex b η' η). rewrite H27 in H29. intuition. rewrite H13 in H42. rewrite H31 in H42. intuition. 
                      rewrite <- H45 in H29. 
                      assert  (forall a : Effect,((Ex)-A a -> (Ex) -hb a a -> False)). intuition. specialize (H8 a).  specialize (H42 a). 
                      rewrite <- H25 in H40.  intuition. specialize (H42 a b). rewrite H26 in H42. rewrite H27 in H42. intuition.
    (*Case 5*) specialize ( H30 Ex b a). rewrite H27 in H30. rewrite <- H41 in H31. assert (so b a). rewrite H31 in H30.
                      rewrite <- H45 in H13. intuition. 
                      assert  (forall a : Effect,((Ex)-A a -> (Ex) -hb a a -> False)). intuition. specialize (H8 a). specialize (H46 a).
                      rewrite <- H25 in H40. intuition.  specialize (H46 a b). rewrite H26 in H46. rewrite H27 in H46. intuition.
    (*case 6*)
                      assert  (forall a : Effect,((Ex)-A a -> (Ex) -hb a a -> False)). intuition. specialize (H8 a). specialize (H42 a).
                      rewrite <- H25 in H40. intuition.  specialize (H42 a b). rewrite H26 in H42. rewrite H27 in H42. intuition.

(*Now, use PaperH8III to show these 3 statements are equal to acyclicity of hb'*)
assert ( forall (Ex:Exec), 
                                      (forall (a:Effect), Ex-A a -> ~ Ex-vis a a) ->
                                      (forall (a:Effect), Ex-A a -> ~ Ex-so  a a) ->
                                      (forall (a b:Effect),Ex-A a -> Ex-A b ->  ~((Ex-vis a b)/\ (Ex-so b a))) ->
                                                                                                                              (forall (a:Effect),~(Ex-hb a a))).
apply  PaperH8III . specialize (H39 Ex'). rewrite H23 in H39.  rewrite H24 in H39. rewrite H22 in H39. intuition. 
unfold WF1. rewrite  H18. intuition. specialize (H40 a). intuition.

(*----------------------------------------------------------------------proof of WF2  *)
 inversion H. unfold WF2. intuition. assert ((E A' vis' so' sameobj') -sameobj = sameobj'). intuition.
rewrite H55. specialize (H45 a b). intuition.

(*----------------------------------------------------------------------proof of WF3  *)
unfold WF3. intuition. rewrite H18 in H37. rewrite H18 in H38. rewrite  H24 in H38. rewrite H24 in H37. apply H20 in H38.
apply H20 in H37. rewrite H18. rewrite H24. apply H20.  intuition.
    (*5 new subgoals, based on definition of so'*)
    (*Case 1*) assert (so a c). intuition. rewrite H39 in H35. specialize (H29 Ex a η' η). rewrite  H27 in H29. intuition.
                     rewrite H13 in H37. rewrite H31 in H37. intuition. unfold WF3 in H2. specialize (H2 a η c). rewrite H27 in H2. intuition.
    (*Case 2*) intuition.
    (*Case 3*) specialize (H30 Ex a b). rewrite H39 in H30. rewrite H38 in H30.  rewrite H13 in H30. rewrite H31 in H30. intuition.
                     rewrite <- H38 in H37. rewrite <- H39 in H37. unfold WF3 in H2. specialize (H2 a b c). rewrite H27 in H2. rewrite H27 in H37.
                     intuition.
    (*Case 4*) unfold WF3 in H2. specialize (H2 a b η'). rewrite H27 in H2. intuition. rewrite H37 in H35. specialize(H30  Ex η' η).
                     rewrite H27 in H30. rewrite H13 in H30. intuition.
    (*Case 5*) unfold WF3 in H2. specialize (H2  a b c). rewrite H27 in H2. intuition.

(*----------------------------------------------------------------------proof of WF4  *)
unfold WF4. intuition. rewrite H18 in H35. rewrite H22 in H35. assert ((E A' vis' so' sameobj') -sameobj  = sameobj'). intuition.  
rewrite H37. specialize (H21 a a). intuition.

(*----------------------------------------------------------------------proof of WF5  *)
unfold WF5. intuition. rewrite H18 in H35. rewrite H22 in H35. assert ((E A' vis' so' sameobj') -sameobj = sameobj'). intuition. 
rewrite H39. specialize (H21 b a). intuition. 

(*----------------------------------------------------------------------proof of WF6  *)
unfold WF6. intuition. rewrite H18 in H35. rewrite H22 in H35. assert ((E A' vis' so' sameobj') -sameobj = sameobj'). intuition.
rewrite H39.  specialize (H21 a c). intuition. 

Qed.

 

























