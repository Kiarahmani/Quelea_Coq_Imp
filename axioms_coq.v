Require Import Coq.Sets.Constructive_sets.
Require Import Definitions.
Require Import oper_semantic_coq.
Import Operational_Semantics.






(*---Well-Formedness of Executions *)
Axiom FW: forall (Ex:Exec), (WF1 Ex) ->(WF2 Ex) ->(WF3 Ex) ->(WF4 Ex) ->(WF5 Ex) ->(WF6 Ex)-> (WF7 Ex) ->(WF Ex). 
Axiom WFhelp: forall (Ex:Exec), (WF Ex)->(WF1 Ex)/\(WF2 Ex)/\(WF3 Ex)/\(WF4 Ex)/\(WF5 Ex)/\(WF6 Ex)/\(WF7 Ex).



(*---Freshness of the Newly Generated Effect *)
Axiom Freshness: forall (Θ:Store)(ex1 ex2:Exec) (opk:op_key)(eff:Effect)(r:ReplID),  
                   [Θ|-ex1, opk ~r~> ex2, eff] -> forall r, (dom Θ r)-> ~ (Θ r) eff.
Axiom CorrectFreshness: forall(Θ:Store)(ex1 ex2:Exec)(opk:op_key)(eff:Effect)(r:ReplID), 
                          [Θ|-ex1, opk ~r~> ex2, eff] -> ~ (ex1-A) eff.


(*---The Definition of Equality of two Session Soups *)
Axiom  Sess_Equal : forall (S S':SessSoup), S=S' <-> forall (I:Soup_Ing), (In Soup_Ing S I <-> In Soup_Ing S' I).


(*---Trivial Facts About Relations*)
Axiom sameobj_trans: forall (Ex:Exec)(a b c: Effect), Ex-sameobj a b -> Ex-sameobj b c -> Ex-sameobj a c.
Axiom Sameobj_Def: forall  (Θ:Store) (Ex Ex':Exec)(opk:op_key) (η:Effect) (r:ReplID) (a b: Effect),
                     [Θ |- Ex, opk ~r~> Ex', η] -> Ex-A a -> Ex-A b -> Ex-sameobj a b.
Axiom SO_Seq_General : forall (Ex:Exec) (a b:Effect), (Ex-so a b) <-> (lt (seq a) (seq b)). 



(*---Relating Domain of the Relations to the Universe of Effects*)
Axiom So_Domain :      forall (Ex:Exec)(a:Effect), ((Rel_dom Ex-so a)      -> (Ex-A a)).
Axiom Vis_Domain :     forall (Ex:Exec)(a:Effect), ((Rel_dom Ex-vis a)     -> (Ex-A a)).
Axiom Hbo_Domain :     forall (Ex:Exec)(a:Effect), ((Rel_dom Ex-hbo a)     -> (Ex-A a)).
Axiom Sameobj_Domain : forall (Ex:Exec)(a:Effect), ((Rel_dom Ex-sameobj a) -> (Ex-A a)).

(*---The Definition of Equality of Soup Ingredients*)
Axiom Seq_Uniq : forall (i i': SeqNo)(s s': SessID)(σ σ' : session), (<<s , i , σ >>) = (<<s', i' , σ' >>) -> i=i'.


(*--- So only relates effects from the same session*)
Axiom SO_SameSession : forall (Ex:Exec)(eff eff':Effect), Ex-so eff eff' -> (eff.(sess) = eff'.(sess)).

(*---Decidability of Membership of a Soup *)
Axiom Soup_comp : forall (Ex:Exec)(eff:Effect), (Ex-A eff)\/(~ Ex-A eff).


(*---Claimed in the Paper *)
(*3 equal statements to the acyclicity of hb*)
Axiom PaperH8: forall (Ex:Exec)(eff:Effect), ~ (Ex-hb eff eff)-> ((~Ex-vis eff eff) /\ (~ Ex-so eff eff)).

Axiom PaperH8II : forall (Ex:Exec)(eff eff': Effect), ~((Ex-vis eff eff')/\ (Ex-so eff' eff)).

Axiom PaperH8III : forall (Ex:Exec), 
                     (forall (eff:Effect), Ex-A eff -> ~ Ex-vis eff eff) ->
                     (forall (eff:Effect), Ex-A eff -> ~ Ex-so  eff eff) ->
                     (forall (eff eff':Effect),Ex-A eff -> Ex-A eff' ->  ~((Ex-vis eff eff')/\ (Ex-so eff' eff))) ->
                     (forall (eff:Effect),~(Ex-hb eff eff)).





(*************************************************************************************************************************)
(*=============================These Were Axioms Before, But Now Are Replaced with Other Axioms and Are Trivially Proved *)

Lemma  SO_NewEff: forall (Θ: Store)(Ex Ex':Exec) (opk:op_key)(η:Effect)(r:ReplID),
                    [Θ|-Ex, opk ~r~> Ex', η] -> (forall a:Effect, Θ r a -> ~ Ex-so η a).
Proof. intuition. apply CorrectFreshness in H. apply WF_Relation with (a:= η) (b:=a) in H1; destruct H1.
       apply So_Domain in H1; auto.
Qed.

Require Import Omega.

Lemma SessionOrder : forall (Ex:Exec)(eff eff':Effect), Ex-so eff eff' -> ((eff.(sess) = eff'.(sess))/\ ((eff.(seq))+1 <= (eff'.(seq)))).
Proof.
  intros Ex a b Hso. split.
  apply SO_SameSession in Hso; auto. apply SO_Seq_General in Hso. intuition.
Qed.

Lemma  SO_Seq : forall (Ex:Exec)(a b c:Effect), Ex-so a b -> seq b = seq c - 1 -> Ex-so a c.
Proof.
  intros Ex a b c. intros Hso Heq. apply SO_Seq_General. apply SO_Seq_General in Hso. intuition.
Qed.

Lemma SO_SeqII' : forall (Ex:Exec)(a b :Effect), (seq b>0)->seq a = seq b -1  -> Ex-so a b.
Proof.
  intros. apply SO_Seq_General. omega.
Qed.

Require Import Omega.
Lemma Eneq_nat_cont : forall i:SeqNo, (i>0)->(i=i-1)\/(i=i+1) -> False.
Proof. intros. omega.
Qed.

Lemma natSeq: forall ss:SeqNo, ~(ss+1 <= (ss-1)).
Proof.
  intros. omega.
Qed.

Lemma  SO_SeqIII : forall (Ex:Exec)(a b c:Effect), Ex-so a b -> Ex-so b c  -> Ex-so a c.
Proof.
  intros.
  apply SO_Seq_General. apply SO_Seq_General in H. apply SO_Seq_General in H0. omega.
Qed.


Lemma Relation_Dom : forall (Ex:Exec) (eff:Effect), (~Ex-A eff ) -> (~Ex-so eff eff).
  Proof.
    intuition. apply WF_Relation with (a:=eff)(b:=eff)(r:=Ex-so) in H0. destruct H0.
    apply So_Domain in H1; auto.
Qed.

