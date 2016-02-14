Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import parametes_coq.
Require Import config_coq.
Require Import oper_semantic_coq.
Import Config.
Import parameters.
Import Operational_Semantics.

Infix "∩" := Rel_Intersect (at level 10).
Infix "∪" := Rel_Union (at level 0).

(*****************DEFINITIONS******************)

(*Well-Formedness of an Execution*)
Parameter WF : Exec->Prop.
(*Well-Formedness of an Execution is equal to: *)
Definition WF1 (Ex:Exec) :  Prop := forall (a:Effect), (Ex-A a) ->  ~(Ex-hb a a).
Definition WF2 (Ex:Exec) := forall (a b : Effect), (Ex-A a) -> (Ex-A b) -> (Ex-vis a b)-> (Ex-sameobj a b).
Definition WF3 (Ex:Exec) := forall (a b c: Effect), (Ex-so a b)/\(Ex-so b c) -> (Ex-so a c ).
Definition WF4 (Ex:Exec) := forall (a:Effect), (Ex-A a) -> (Ex-sameobj a a).
Definition WF5 (Ex:Exec) := forall (a b : Effect),(Ex-A a) -> (Ex-A b) ->   (Ex-sameobj a b)-> (Ex-sameobj b a).
Definition WF6 (Ex:Exec) := forall (a b c: Effect), (Ex-A a) -> (Ex-A b) ->(Ex-A c) -> (Ex-sameobj a b)/\(Ex-sameobj b c) -> (Ex-sameobj a c ).

(*Definition6 of Paper: Causually Consistent Stores*)
Definition CausCons (Θ:Store)(Ex:Exec):= 
                                        forall(r: ReplID)(a η:Effect), ((Θ r) η) -> (Ex-A a) -> ((Ex-hbo) a η) -> ((Θ r) a). 

Definition StoreCons (τ:ConsCls)(Ex:Exec)(η':Effect):=
  match τ with
    |ec => forall(a b:Effect), (Ex-hbo a b)/\(Ex-vis b η') -> (Ex-vis a η') 
    |cc => forall(a:Effect),   (Ex-hbo a η')              -> (Ex-vis a η')
    |sc => forall(a:Effect),   (Ex-sameobj a η')          -> (Ex-vis a η')\/(Ex-vis η' a)\/(a=η') 
  end.


Definition Model (Ex:Exec)(τ:ConsCls) := forall(η:Effect), (Ex-A η)-> StoreCons τ Ex η.  

Variable A':Exec_A.
Variable vis' so' same':Relation.
Definition Ex := (E A' vis' so' same').


Infix "|=Ψ" := Model (at level 10). 


Eval compute in  Ex |=Ψ cc.







(*------------------------------------------------------------------------------------------------------------------------*)
(******************AXIOMS******************)
Axiom FW: forall (Ex:Exec), (WF1 Ex) ->(WF2 Ex) ->(WF3 Ex) ->(WF4 Ex) ->(WF5 Ex) ->(WF6 Ex) ->(WF Ex). (*WF1 to WF6 result WF*)
Axiom WFhelp: forall (Ex:Exec), (WF Ex)->(WF1 Ex)/\(WF2 Ex)/\(WF3 Ex)/\(WF4 Ex)/\(WF5 Ex)/\(WF6 Ex). (*and vice versa*)

Axiom Freshness: forall  (Θ:Store)(ex1 ex2:Exec) (opk:op_key) (eff:Effect) (r:ReplID),  (*new effect in reductions is fresh*)
                                                                                                {Θ|-ex1, opk ~r~> ex2, eff} -> ~ (Θ r) eff.
    
(*Trivial Axioms*)
Axiom SessionOrder : forall (Ex:Exec)(eff eff':Effect), Ex-so eff eff' -> ((eff.(sess) = eff'.(sess))/\ (  (eff.(seq))+1 <= (eff'.(seq)) )).
Axiom Why_Coq : forall i:SeqNo, i=i-1 -> False.
Axiom Relation_Dom : forall (Ex:Exec) (eff:Effect), (~Ex-A eff ) ->  (~Ex-so eff eff).
Axiom Soup_comp : forall (Ex:Exec)(eff:Effect), (Ex-A eff)\/(~ Ex-A eff).
Axiom natSeq: forall ss:SeqNo, ~(ss+1 <= (ss-1)). 


(*The new produced effect does not precede existing effects *)
Axiom  SO_NewEff: forall (Θ: Store)(Ex Ex':Exec) (opk:op_key)(η:Effect)(r:ReplID),
                                          {Θ|-Ex, opk ~r~> Ex', η} -> (forall a:Effect, Θ r a -> ~ Ex-so η a).

(*So holds if an effects precedes another*)
Axiom  SO_Seq : forall (Ex:Exec)(a b c:Effect), Ex-so a b -> seq b = seq c - 1 -> Ex-so a c.
Axiom SO_SeqII : forall (Ex:Exec)(a b :Effect), seq a = seq b -1  -> Ex-so a b.
Axiom  SO_SeqIII : forall (Ex:Exec)(a b c:Effect), Ex-so a b -> Ex-so b c  -> Ex-so a c.


(*Claimed in the paper:  3 equal statements to the acyclicity of hb*)
Axiom PaperH8: forall (Ex:Exec)(eff:Effect),~ (Ex-hb eff eff)->
                                     ~Ex-vis eff eff /\ ~ Ex-so eff eff  .
Axiom PaperH8II : forall (Ex:Exec)(eff eff': Effect), 
                                     ~((Ex-vis eff eff')/\ (Ex-so eff' eff)).
Axiom PaperH8III : forall (Ex:Exec), 
                                      (forall (eff:Effect), Ex-A eff -> ~ Ex-vis eff eff) ->
                                      (forall (eff:Effect), Ex-A eff -> ~ Ex-so  eff eff) ->
                                      (forall (eff eff':Effect),Ex-A eff -> Ex-A eff' ->  ~((Ex-vis eff eff')/\ (Ex-so eff' eff))) ->
                                                                                                                              (forall (eff:Effect),~(Ex-hb eff eff)).

