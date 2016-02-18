Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Strings.String.
Require Import parametes_coq.
Require Import config_coq.
Require Import oper_semantic_coq.
Import Config.
Import parameters.
Import Operational_Semantics.


Inductive EffVar : Type :=
  |effvar: string -> EffVar.

Inductive contract_EffType : Type :=
|contract_EffType_cons: OperName -> contract_EffType
|contract_efftype_disjunction: contract_EffType -> contract_EffType -> contract_EffType.

Inductive contract_Relation : Type :=
|contract_vis: contract_Relation
|contract_so: contract_Relation
|contract_sameobj: contract_Relation
|contract_relation_union: contract_Relation -> contract_Relation -> contract_Relation
|contract_relation_intersect: contract_Relation -> contract_Relation -> contract_Relation
|contract_relation_closure: contract_Relation -> contract_Relation.

Inductive my_trans (R1:Relation): Relation :=
|my_base (e1 e2:Effect) : R1 e1 e2 -> my_trans R1 e1 e2
|my_step (e1 e2 e3:Effect) : (my_trans R1) e1 e2 -> (my_trans R1) e2 e3 -> my_trans R1 e1 e3.
Inductive my_union (R1 R2:Relation) : Relation :=
|my_uni_first  (e1 e2:Effect) : R1 e1 e2 -> my_union R1 R2 e1 e2
|my_uni_second (e1 e2:Effect) : R2 e1 e2 -> my_union R1 R2 e1 e2.                                                   
Inductive my_intersect (R1 R2: Relation) : Relation :=
|intersect_cons (e1 e2: Effect) : R1 e1 e2 -> R2 e1 e2 -> (my_intersect R1 R2) e1 e2.

Inductive contract_Prop : Type :=
|contract_prop_true
|contract_prop_effeff : contract_Relation -> Effect -> Effect -> contract_Prop
|contract_prop_effvar : contract_Relation -> Effect -> EffVar -> contract_Prop
|contract_prop_vareff : contract_Relation -> EffVar -> Effect -> contract_Prop
|contract_prop_varvar : contract_Relation -> EffVar -> EffVar -> contract_Prop                                     
|contract_prop_disjunction: contract_Prop -> contract_Prop   -> contract_Prop
|contract_prop_conjunction: contract_Prop -> contract_Prop   -> contract_Prop
|contract_prop_implication: contract_Prop -> contract_Prop   -> contract_Prop.      

Inductive contract_Contract : Type :=
|contract_free_cons: contract_Prop -> contract_Contract
|contract_untyped_cons: EffVar->contract_Contract -> contract_Contract
|contract_typed_cons: EffVar -> contract_EffType -> contract_Contract -> contract_Contract.















