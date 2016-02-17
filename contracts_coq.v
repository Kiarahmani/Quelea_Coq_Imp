Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import parametes_coq.
Require Import config_coq.
Require Import oper_semantic_coq.
Require Import Coq.Strings.String.
Import Config.
Import parameters.
Import Operational_Semantics.
Require Import contract_defintion.
Require Import contract_Eval.


Parameter var_equal : forall x y : EffVar, {x = y} + {x <> y}.

Fixpoint Prop_Evaluation (pr:contract_Prop)(Ex:Exec) : Eval_result :=
  match pr with
    |contract_prop_true => result True
    |contract_prop_effeff R1 α β      => result((relation_Evaluation R1 Ex) α β)
    |contract_prop_conjunction p1 p2  => And_result (Prop_Evaluation p1 Ex) (Prop_Evaluation p2 Ex)
    |contract_prop_disjunction p1 p2  => Or_result  (Prop_Evaluation p1 Ex) (Prop_Evaluation p2 Ex)
    |contract_prop_implication p1 p2  => Imp_result (Prop_Evaluation p1 Ex) (Prop_Evaluation p2 Ex)
    |_=> error                                                             
  end.



Fixpoint Prop_Subst (pr:contract_Prop)(eff:Effect)(v:EffVar) : contract_Prop :=
  match pr with
    |contract_prop_true => contract_prop_true
    |contract_prop_effeff R1 e1 e2 => contract_prop_effeff R1 e1 e2
    |contract_prop_effvar R1 e1 v1 => if (var_equal v v1) then contract_prop_effeff R1 e1 eff else contract_prop_effvar R1 e1 v1
    |contract_prop_vareff R1 v1 e1 => if (var_equal v v1) then contract_prop_effeff R1 eff e1 else contract_prop_vareff R1 v1 e1
    |contract_prop_varvar R1 v1 v2 => if (var_equal v v1)
                                     then (if (var_equal v v2) then contract_prop_effeff R1 eff eff
                                                               else contract_prop_effvar R1 eff v2)
                                     else (if (var_equal v v2) then contract_prop_vareff R1 v1 eff
                                           else contract_prop_varvar R1 v1 v2)
    |contract_prop_disjunction p1 p2 => contract_prop_disjunction (Prop_Subst p1 eff v) (Prop_Subst p2 eff v)
    |contract_prop_conjunction p1 p2 => contract_prop_conjunctieson (Prop_Subst p1 eff v) (Prop_Subst p2 eff v)
    |contract_prop_implication p1 p2 => contract_prop_implication (Prop_Subst p1 eff v) (Prop_Subst p2 eff v)                             
  end.


Fixpoint contract_Evaluation (cont: contract_Contract) (Ex:Exec) :Prop :=
  match cont with
    |contract_free_cons π => Prop_Evaluation π Ex
    |contract_untyped_cons e ψ => 
    |contract_typed_cons e τ ψ => True
  end.




