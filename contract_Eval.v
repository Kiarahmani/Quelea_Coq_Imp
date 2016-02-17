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
Require Import contract_defintion.


Fixpoint relation_Evaluation (rel : contract_Relation) (Ex:Exec) : Relation :=
  match rel with
    |contract_vis   => Ex-vis
    |contract_so => Ex-so
    |contract_sameobj => Ex-sameobj
    |contract_relation_union R1 R2 => my_union (relation_Evaluation R1 Ex) (relation_Evaluation R2 Ex)
    |contract_relation_intersect R1 R2 => my_intersect (relation_Evaluation R1 Ex)  (relation_Evaluation R2 Ex)
    |contract_relation_closure R1 => (my_trans  (relation_Evaluation R1 Ex))
  end.

Inductive Eval_result : Type :=
|result : Prop -> Eval_result
|error : Eval_result.

Definition result_prop (e1:Eval_result) : Prop :=
  match e1 with
    |result T => T
    |_=> False
  end.

Definition And_result (e1 e2: Eval_result): Eval_result:=
  match (e1,e2) with
    |(_,error) => error
    |(error,_) => error
    |(result X1,result X2) => result (X1/\X2)
  end.

Definition Or_result (e1 e2: Eval_result): Eval_result:=
  match (e1,e2) with
    |(_,error) => error
    |(error,_) => error
    |(result X1,result X2) => result (X1\/X2)
  end.

Definition Imp_result (e1 e2: Eval_result): Eval_result:=
  match (e1,e2) with
    |(_,error) => error
    |(error,_) => error
    |(result X1,result X2) => result (X1->X2)
  end.

