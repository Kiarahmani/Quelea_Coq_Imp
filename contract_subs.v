Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Definitions.
Require Import oper_semantic_coq.
Require Import Coq.Strings.String.
Import Operational_Semantics.
Require Import contract_definition.

Definition var_equal x y:=  match x with
                         |effvar namex => match y with
                                           |effvar namey => if (string_dec namex namey) then true  else false
                                         end
                       end.



Parameter Eff_Equi:Effect -> Effect->Prop.

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
    |contract_prop_conjunction p1 p2 => contract_prop_conjunction (Prop_Subst p1 eff v) (Prop_Subst p2 eff v)
    |contract_prop_implication p1 p2 => contract_prop_implication (Prop_Subst p1 eff v) (Prop_Subst p2 eff v)                             
  end.


Fixpoint contract_Subst (ct:contract_Contract) (eff:Effect)(v:EffVar) : contract_Contract :=
  match ct with
    |contract_free_cons π => contract_free_cons (Prop_Subst π eff v)
    |contract_untyped_cons e ψ => contract_untyped_cons e (contract_Subst ψ eff v)                               
    |contract_typed_cons e τ ψ => contract_typed_cons e τ (contract_Subst ψ eff v)
  end.
